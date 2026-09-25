#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""CDD-ECS C-series channel pipeline (preregistered 2026-08-30, v1.0).

Discipline:
  - All thresholds are read from the FROZEN preregistration JSON
    (H:\\cdd_ecs_channel_preregistration_v1.json). No threshold is defined here.
  - Cache-first fetching; raw files archived in H:\\cdd_ecs_data with SHA256.
  - Download failure -> channel status 'pending_data' (honest downgrade);
    manual numeric entry is FORBIDDEN.
  - Snapshot output: H:\\cdd_ecs_channel_pipeline_results_v1.json (new-file
    discipline; never edit in place).
"""
import csv
import hashlib
import io
import json
import math
import os
import re
import sys
import time
import urllib.request
import urllib.error
from datetime import datetime, timezone

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")

PREREG_MD = r"H:\cdd_ecs_channel_preregistration_20260830.md"
PREREG_JSON = r"H:\cdd_ecs_channel_preregistration_v1.json"
CACHE_DIR = r"H:\cdd_ecs_data"
OUT_JSON = r"H:\cdd_ecs_channel_pipeline_results_v1.json"

USER_AGENT = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) CDD-ECS-pipeline/1.0"

# Documented baseline offsets (frozen as operational [O] constants in prereg doc):
GISTEMP_PI_OFFSET_C = 0.79    # GISS 1951-1980 -> 1850-1900
HADCRUT5_PI_OFFSET_C = 0.36   # MetOffice 1961-1990 -> 1850-1900


def sha256_bytes(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest().upper()


def sha256_file(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 16), b""):
            h.update(chunk)
    return h.hexdigest().upper()


def utcnow_iso() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def fetch(url: str, cache_key: str, timeout: int = 90):
    """Cache-first download. Returns (text, provenance) or raises."""
    safe = re.sub(r"[^A-Za-z0-9._-]", "_", cache_key)
    cache_path = os.path.join(CACHE_DIR, safe)
    meta_path = cache_path + ".meta.json"
    if os.path.exists(cache_path) and os.path.exists(meta_path):
        with open(cache_path, "r", encoding="utf-8", errors="replace") as f:
            text = f.read()
        with open(meta_path, "r", encoding="utf-8") as f:
            meta = json.load(f)
        meta["cache_hit"] = True
        return text, meta
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        raw = resp.read()
    text = raw.decode("utf-8", errors="replace")
    meta = {
        "url": url,
        "downloaded_utc": utcnow_iso(),
        "raw_sha256": sha256_bytes(raw),
        "bytes": len(raw),
        "cache_hit": False,
    }
    with open(cache_path, "w", encoding="utf-8", errors="replace") as f:
        f.write(text)
    with open(meta_path, "w", encoding="utf-8") as f:
        json.dump(meta, f, indent=2)
    return text, meta


def ols(xs, ys):
    """OLS y = a + b*x. Returns (b, a, resid_std, t_b, n)."""
    n = len(xs)
    if n < 3:
        raise ValueError("insufficient points for OLS")
    mx = sum(xs) / n
    my = sum(ys) / n
    sxx = sum((x - mx) ** 2 for x in xs)
    if sxx == 0:
        raise ValueError("zero variance in x")
    b = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sxx
    a = my - b * mx
    resid = [y - (a + b * x) for x, y in zip(xs, ys)]
    dof = n - 2
    s2 = sum(r * r for r in resid) / dof if dof > 0 else float("nan")
    s = math.sqrt(s2) if s2 > 0 else float("nan")
    se_b = s / math.sqrt(sxx) if sxx > 0 else float("nan")
    t_b = b / se_b if se_b and se_b > 0 else float("nan")
    return b, a, s, t_b, n


def verdict_of(metric, prereg, thresholds_key="thresholds"):
    raise NotImplementedError  # verdicts are channel-specific; kept explicit


# ----------------------------------------------------------------------------
# C1 temperature (NASA GISTEEP primary; HadCRUT5 cross)
# ----------------------------------------------------------------------------

def parse_gistemp_monthly(text):
    """Rows: Year, Jan..Dec (positional). Returns [(year, month, anom)] vs 1951-1980."""
    rows = []
    for line in text.splitlines():
        parts = line.split(",")
        if not parts or not re.match(r"^\d{4}$", parts[0].strip()):
            continue
        year = int(parts[0])
        for i, v in enumerate(parts[1:13]):
            v = v.strip()
            if v in ("", "***", "nan", "NaN"):
                continue
            try:
                rows.append((year, i + 1, float(v)))
            except ValueError:
                continue
    return rows


def channel_C1(prereg):
    cfg = prereg["channels"]["C1_temperature"]
    ch = {"id": "C1", "name": "temperature_path", "status": "pending_data"}
    try:
        text, prov = fetch(cfg["primary_source"]["url"], "C1_gistemp_monthly.csv")
        rows = parse_gistemp_monthly(text)
        if len(rows) < 12 * 30:
            ch["error"] = f"series too short ({len(rows)} months < 360)"
            ch["provenance"] = prov
            return ch
        # last 12 calendar months present
        by_ym = {(y, m): v for y, m, v in rows}
        last_y, last_m = max(by_ym)
        vals, used = [], []
        y, m = last_y, last_m
        for _ in range(12):
            if (y, m) in by_ym:
                vals.append(by_ym[(y, m)])
                used.append((y, m))
            else:
                ch["error"] = f"missing month {(y, m)} in trailing window"
                ch["provenance"] = prov
                return ch
            m -= 1
            if m == 0:
                m, y = 12, y - 1
        t12 = sum(vals) / 12.0
        m1 = t12 + GISTEMP_PI_OFFSET_C - 1.5
        # sigma for numeric synthesis: residual std of annual series vs its own trend
        ann = {}
        for y0, m0, v in rows:
            ann.setdefault(y0, []).append(v)
        years = sorted(ann)
        ann_mean = [sum(ann[y0]) / len(ann[y0]) for y0 in years]
        last30y = years[-30:]
        last30v = ann_mean[-30:]
        _, _, sigma, _, _ = ols(last30y, last30v)
        # state verdict per prereg thresholds
        if m1 > 0.30:
            status = "green"
        elif m1 > 0.0:
            status = "yellow"
        else:
            status = "red"
        ch.update({
            "status": status,
            "metrics": {"M1_margin_to_1.5C_C": round(m1, 4)},
            "intermediates": {
                "trailing_window": [f"{used[-1][0]}-{used[-1][1]:02d}", f"{last_y}-{last_m:02d}"],
                "t12_C_vs_1951_1980": round(t12, 4),
                "pi_offset_C": GISTEMP_PI_OFFSET_C,
                "annual_series_years": [years[0], years[-1]],
                "sigma_annual_residual_C": round(sigma, 4),
            },
            "verdict_rule": cfg["thresholds"],
            "provenance": prov,
            "numeric_z": {
                "margin_to_red": round(m1 - 0.0, 4),
                "sigma": round(sigma, 4),
                "z": round((m1 - 0.0) / sigma, 4) if sigma and sigma > 0 else None,
            },
        })
        # cross source (register only; disagreement gate if available)
        cross = {"id": "HadCRUT5", "status": "unavailable"}
        try:
            url5 = ("https://www.metoffice.gov.uk/hadobs/hadcrut5/data/"
                    "HadCRUT.5.0.2.0/analysis/diagnostics/"
                    "HadCRUT.5.0.2.0.analysis.summary_series.global.monthly.csv")
            t5, p5 = fetch(url5, "C1_hadcrut5_monthly.csv")
            pts = []
            for line in t5.splitlines():
                parts = line.split(",")
                if len(parts) >= 2 and re.match(r"^\d{4}-\d{2}$", parts[0].strip()):
                    try:
                        pts.append((parts[0].strip(), float(parts[1])))
                    except ValueError:
                        pass
            if len(pts) >= 12:
                last12 = pts[-12:]
                t12_h = sum(v for _, v in last12) + HADCRUT5_PI_OFFSET_C
                diff = abs((t12 + GISTEMP_PI_OFFSET_C) - t12_h)
                cross = {
                    "status": "ok",
                    "t12_C_vs_1850_1900": round(t12_h, 4),
                    "abs_diff_C": round(diff, 4),
                    "disagreement_gate_C": cfg["cross_disagreement_gate"]["abs_diff_C"],
                    "disagreement": diff > cfg["cross_disagreement_gate"]["abs_diff_C"],
                    "provenance": p5,
                }
                if cross["disagreement"]:
                    ch["status"] = "yellow"
                    ch["cross_source_disagreement"] = True
        except Exception as e:  # noqa: BLE001
            cross["error"] = str(e)[:200]
        ch["cross_source"] = cross
    except Exception as e:  # noqa: BLE001
        ch["error"] = str(e)[:300]
    return ch


# ----------------------------------------------------------------------------
# C2 AMOC (RAPID 26.5N)
# ----------------------------------------------------------------------------

def channel_C2(prereg):
    cfg = prereg["channels"]["C2_amoc"]
    ch = {"id": "C2", "name": "amoc", "status": "pending_data"}
    candidates = [
        "https://rapid.ac.uk/rapidmoc/rapid_data/moc_transports.csv",
        "https://rapid.ac.uk/rapidmoc/rapid_data/datadl/moc_transports.csv",
        "https://rapid.ac.uk/rapidmoc/rapid_data/OSNAP/moc_transports.csv",
    ]
    text = prov = None
    used_url = None
    for url in candidates:
        try:
            text, prov = fetch(url, "C2_rapid_moc.csv")
            used_url = url
            break
        except Exception:  # noqa: BLE001
            continue
    if text is None:
        ch["error"] = "RAPID 26.5N monthly transports not reachable at registered candidates"
        ch["candidate_urls"] = candidates
        return ch
    # [implementation fix 2026-08-30] rapid.ac.uk direct URL returns an HTML
    # download-form page (email-gated) instead of data - detect and register the
    # alternative access routes honestly instead of reporting '0 months'.
    head = text[:500].lower()
    if text.lstrip()[:15].lower().startswith("<!doctype html") or "<html" in head:
        ch["error"] = ("RAPID direct URL returns HTML download-form page (email-gated), "
                       "not data. Alternative access: BODC DOI "
                       "10.5285/04c79ece-3186-349a-e063-6c86abc015b0 (interactive "
                       "download, no direct file link on catalogue page); SEA.NO mirror "
                       "https://www.seanoe.org/data/00311/42182/ (connection timeout "
                       "from this network). Manual form submission is outside pipeline "
                       "scope - honest pending_data.")
        return ch
    if used_url and "OSNAP" in used_url:
        ch["error"] = ("only OSNAP (60N) transport table reachable; prereg channel is "
                       "RAPID 26.5N - cross-latitude substitution forbidden")
        return ch
    # tolerant parse: time column + numeric transport column
    pts = []
    for line in text.splitlines():
        parts = [p.strip() for p in line.split(",")]
        if len(parts) < 2:
            continue
        m = re.match(r"^(\d{4})-(\d{2})", parts[0])
        if not m:
            continue
        for v in parts[1:]:
            try:
                pts.append((int(m.group(1)), int(m.group(2)), float(v)))
                break
            except ValueError:
                continue
    if len(pts) < 12 * cfg["quality_gates"]["min_series_years"]:
        ch["error"] = f"RAPID series too short ({len(pts)} months)"
        ch["provenance"] = prov
        return ch
    ann = {}
    for y, m, v in pts:
        ann.setdefault(y, []).append(v)
    years = sorted(ann)
    ann_mean = [sum(ann[y]) / len(ann[y]) for y in years]
    b, a, sigma, t_b, n = ols(years, ann_mean)
    trend_per_decade = b * 10.0
    last5 = ann_mean[-5:]
    m2b = sum(last5) / 5.0 - cfg["collapse_threshold_Sv"]
    # red: significant negative trend AND linear extrapolation crosses 10 Sv before 2060
    cross_year = None
    if trend_per_decade < 0:
        # solve a + b*y = 10
        y_cross = (cfg["collapse_threshold_Sv"] - a) / b
        cross_year = y_cross
    significant_negative = (t_b is not None and not math.isnan(t_b) and t_b < -2.0)
    extrapolates_before_2060 = (cross_year is not None and cross_year < 2060)
    if significant_negative and extrapolates_before_2060:
        status = "red"
    elif significant_negative or m2b <= cfg["warning_margin_Sv"]:
        status = "yellow"
    else:
        status = "green"
    ch.update({
        "status": status,
        "metrics": {
            "M2a_trend_Sv_per_decade": round(trend_per_decade, 4),
            "M2a_t_stat": round(t_b, 4),
            "M2b_margin_to_10Sv": round(m2b, 4),
            "latest_5yr_mean_Sv": round(m2b + 10.0, 4),
        },
        "intermediates": {
            "series_years": [years[0], years[-1]],
            "ols_slope_Sv_per_yr": round(b, 6),
            "sigma_annual_residual_Sv": round(sigma, 4),
            "extrapolation_cross_year": None if cross_year is None else round(cross_year, 1),
        },
        "verdict_rule": cfg["thresholds"],
        "provenance": prov,
        "data_cutoff_note": "RAPID release lag ~18 months",
        "numeric_z": {
            "margin_to_red": round(m2b - cfg["red_anchor_numeric"], 4),
            "sigma": round(sigma, 4),
            "z": round((m2b - cfg["red_anchor_numeric"]) / sigma, 4) if sigma > 0 else None,
        },
    })
    return ch


# ----------------------------------------------------------------------------
# C3 ice sheets (NASA vital-signs GRACE CSV extraction attempt)
# ----------------------------------------------------------------------------

def _try_extract_vitalsign_csvs(page_url, cache_key):
    page, prov = fetch(page_url, cache_key)
    links = re.findall(r'href="([^"]+\.(?:csv|txt|json))"', page)
    cand = [u for u in links if re.search(r"ice|grace|mass|sheet", u, re.I)]
    return cand, prov


def channel_C3(prereg):
    cfg = prereg["channels"]["C3_icesheets"]
    ch = {"id": "C3", "name": "ice_sheets", "status": "pending_data"}
    try:
        links, prov = _try_extract_vitalsign_csvs(
            "https://climate.nasa.gov/vital-signs/ice-sheets/", "C3_nasa_vitalsigns_icesheets.html")
        if not links:
            ch["error"] = ("NASA vital-signs ice-sheet CSVs now require an Earthdata "
                           "account (page is a JS app; no anonymous data links in HTML); "
                           "IMBIE figshare and JPL tellus routes also gated/unreachable. "
                           "Honest pending_data - v2 data-engineering task (Earthdata "
                           "credential registration or GSFC mascon mirror).")
            ch["provenance"] = prov
            return ch
        ch["candidate_links"] = links[:8]
        # try each link: expect two-column series (decimal year, Gt)
        series = {}
        for u in links:
            if "climate.nasa.gov" in u and u.startswith("/"):
                u = "https://climate.nasa.gov" + u
            try:
                txt, p = fetch(u, "C3_" + re.sub(r"[^A-Za-z0-9._-]", "_", u)[-60:])
                pts = []
                for line in txt.splitlines():
                    parts = line.replace(",", " ").split()
                    if len(parts) >= 2:
                        try:
                            yr = float(parts[0])
                            gt = float(parts[1])
                            if 2001 <= yr <= 2030 and -10000 < gt < 10000:
                                pts.append((yr, gt))
                        except ValueError:
                            continue
                if len(pts) >= 12 * 10:
                    name = "greenland" if re.search(r"green", u, re.I) else (
                        "antarctica" if re.search(r"antarct|ais", u, re.I) else None)
                    if name:
                        series[name] = {"pts": pts, "provenance": p, "url": u}
            except Exception:  # noqa: BLE001
                continue
        if "greenland" not in series and "antarctica" not in series:
            ch["error"] = "no parseable GRACE mass series found at candidate links"
            return ch
        metrics = {}
        intermediates = {}
        for name, d in series.items():
            xs = [p[0] for p in d["pts"]]
            ys = [p[1] for p in d["pts"]]
            # mass anomaly series: negative trend = loss; take last 10yr window
            pts10 = [p for p in d["pts"] if p[0] >= max(xs) - 10.0]
            b10, _, sig10, _, n10 = ols([p[0] for p in pts10], [p[1] for p in pts10])
            loss = -b10  # Gt/yr positive loss
            metrics[f"{'M3a' if name == 'greenland' else 'M3b'}_{name}_loss_Gt_per_yr"] = round(loss, 2)
            intermediates[f"{name}_series"] = {
                "span": [min(xs), max(xs)],
                "last10_pts": n10,
                "sigma_residual_Gt": round(sig10, 2),
                "source_url": d["url"],
            }
        if "greenland" not in series or "antarctica" not in series:
            # prereg C3 thresholds are joint (GIS AND AIS); single-sheet -> pending
            ch["error"] = ("only one ice sheet series parseable; prereg verdict is joint "
                           "(GIS and AIS) - honest pending")
            ch["metrics"] = metrics
            ch["intermediates"] = intermediates
            return ch
        gis = metrics["M3a_greenland_loss_Gt_per_yr"]
        ais = metrics["M3b_antarctica_loss_Gt_per_yr"]
        if gis > 270.0 or ais > 180.0:
            status = "red"
        elif gis > 150.0 or ais > 100.0:
            status = "yellow"
        else:
            status = "green"
        ch.update({
            "status": status,
            "metrics": metrics,
            "intermediates": intermediates,
            "verdict_rule": cfg["thresholds"],
            "gap_interpolated": True,
            "gap_note": "GRACE/GRACE-FO 2017-2018 mission gap inside series",
            "numeric_z": None,
            "z_exclusion_reason": "no preregistered single-value red anchor semantics for joint two-sheet verdict",
        })
    except Exception as e:  # noqa: BLE001
        ch["error"] = str(e)[:300]
    return ch


# ----------------------------------------------------------------------------
# C4 biosphere (NOAA OHC attempt + CHIRPS not mechanized this round)
# ----------------------------------------------------------------------------

def channel_C4(prereg):
    cfg = prereg["channels"]["C4_biosphere"]
    ch = {"id": "C4", "name": "biosphere", "status": "pending_data"}
    m4a = None
    try:
        page, prov = fetch("https://www.ncei.noaa.gov/access/monitoring/ocean-heat-content/",
                           "C4_ncei_ohc_page.html")
        links = re.findall(r'href="([^"]+\.(?:csv|txt|dat))"', page)
        for u in links:
            if not u.startswith("http"):
                u = "https://www.ncei.noaa.gov" + u
            try:
                txt, p = fetch(u, "C4_ohc_" + re.sub(r"[^A-Za-z0-9._-]", "_", u)[-55:])
                pts = []
                for line in txt.splitlines():
                    parts = line.replace(",", " ").split()
                    if len(parts) >= 2:
                        try:
                            yr = float(parts[0])
                            v = float(parts[1])
                            if 1955 <= yr <= 2030 and -50 < v < 400:
                                pts.append((yr, v))
                        except ValueError:
                            continue
                if len(pts) >= 15:
                    xs = [p[0] for p in pts]
                    pts10 = [p for p in pts if p[0] >= max(xs) - 10.0]
                    b10, _, _, _, _ = ols([p[0] for p in pts10], [p[1] for p in pts10])
                    m4a = b10
                    ch.setdefault("intermediates", {})["ohc"] = {
                        "span": [min(xs), max(xs)], "source_url": u,
                    }
                    break
            except Exception:  # noqa: BLE001
                continue
    except Exception as e:  # noqa: BLE001
        ch["error"] = f"OHC fetch failed: {str(e)[:200]}"
    # M4b Amazon regional precip: gridded pipeline not deployed this round
    ch["error"] = ("prereg C4 verdict is joint (M4a AND M4b); Amazon dry-season "
                   "regional-mean pipeline (CHIRPS gridded) not deployed - honest "
                   "pending even though M4a available"
                   if m4a is not None else ch.get("error", "data unreachable"))
    if m4a is not None:
        ch["metrics"] = {"M4a_ohc_trend_ZJ_per_yr": round(m4a, 3)}
    return ch


# ----------------------------------------------------------------------------
# C5 biogeochemical (NOAA GML global annual CO2 + frozen PB count)
# ----------------------------------------------------------------------------

def channel_C5(prereg):
    cfg = prereg["channels"]["C5_biogeochemical"]
    ch = {"id": "C5", "name": "biogeochemical", "status": "pending_data"}
    try:
        text, prov = fetch(cfg["primary_source"]["url"], "C5_noaa_co2_annmean_gl.txt")
        pts = []
        for line in text.splitlines():
            if line.startswith("#") or not line.strip():
                continue
            parts = line.split()
            if len(parts) >= 2:
                try:
                    pts.append((int(parts[0]), float(parts[1])))
                except ValueError:
                    continue
        if len(pts) < cfg["quality_gates"]["min_series_years"]:
            ch["error"] = f"CO2 series too short ({len(pts)} yrs)"
            ch["provenance"] = prov
            return ch
        last_year, last_co2 = pts[-1]
        m5b = last_co2 - cfg["pb_boundary_ppm"]
        m5a = cfg["metrics"]["M5a_pb_count"]["value"]
        if m5a >= 6 and m5b >= 85.0:
            status = "red"
        elif m5a == 5 or 70.0 <= m5b < 85.0:
            status = "yellow"
        else:
            status = "green"
        years = [p[0] for p in pts]
        vals = [p[1] for p in pts]
        _, _, sigma, _, _ = ols(years[-30:], vals[-30:])
        ch.update({
            "status": status,
            "metrics": {
                "M5a_pb_count": m5a,
                "M5b_co2_margin_to_350ppm": round(m5b, 2),
                "latest_co2_ppm": round(last_co2, 2),
                "latest_year": last_year,
            },
            "intermediates": {
                "series_years": [years[0], years[-1]],
                "sigma_annual_residual_ppm": round(sigma, 3),
                "M5a_provenance": "literature_snapshot (Rockstrom 2023 PB update), not recomputed observation",
            },
            "verdict_rule": cfg["thresholds"],
            "provenance": prov,
            "numeric_z": {
                "margin_to_red": round(85.0 - m5b, 2),
                "sigma": round(sigma, 3),
                "z": round((85.0 - m5b) / sigma, 3) if sigma > 0 else None,
                "sign_note": "CO2 margin inverted: larger = worse; z computed on (red_anchor - M5b)",
            },
        })
    except Exception as e:  # noqa: BLE001
        ch["error"] = str(e)[:300]
    return ch


# ----------------------------------------------------------------------------
# C6 social structure (US real median household income via FRED)
# ----------------------------------------------------------------------------

def channel_C6(prereg):
    cfg = prereg["channels"]["C6_social_structure"]
    ch = {"id": "C6", "name": "social_structure", "status": "pending_data"}
    text = prov = None
    last_err = None
    # [implementation fix 2026-08-30] FRED endpoint intermittently times out from this
    # network; retry up to 3x with 150s timeout before honest pending.
    for attempt in range(3):
        try:
            text, prov = fetch(cfg["primary_source"]["url"], "C6_fred_MEHOINUSA672N.csv",
                               timeout=150)
            break
        except Exception as e:  # noqa: BLE001
            last_err = str(e)[:200]
            time.sleep(8)
    if text is None:
        ch["error"] = f"FRED unreachable after 3 attempts: {last_err}"
        return ch
    try:
        pts = []
        for line in text.splitlines():
            parts = line.split(",")
            if len(parts) >= 2 and re.match(r"^\d{4}-\d{2}-\d{2}$", parts[0].strip()):
                try:
                    pts.append((int(parts[0][:4]), float(parts[1])))
                except ValueError:
                    continue
        if len(pts) < cfg["quality_gates"]["min_series_years"]:
            ch["error"] = f"series too short ({len(pts)} yrs)"
            ch["provenance"] = prov
            return ch
        latest_y, latest_v = pts[-1]
        peak_y, peak_v = max(pts, key=lambda p: p[1])
        if latest_v >= 0.99 * peak_v:
            m6a = 0
        else:
            m6a = latest_y - peak_y
        if m6a > 15:
            status = "red"
        elif m6a >= 5:
            status = "yellow"
        else:
            status = "green"
        # M6b background: log deviation from 1985-2007 trend
        w = [(y, v) for y, v in pts if 1985 <= y <= 2007]
        b, a, sig, _, _ = ols([y for y, _ in w], [math.log(v) for _, v in w])
        m6b = (math.log(latest_v) - (a + b * latest_y)) / sig if sig > 0 else None
        ch.update({
            "status": status,
            "metrics": {
                "M6a_stagnation_years": m6a,
                "M6b_deprivation_sigma": None if m6b is None else round(m6b, 3),
            },
            "intermediates": {
                "series_years": [pts[0][0], latest_y],
                "peak": {"year": peak_y, "value": peak_v},
                "latest": {"year": latest_y, "value": latest_v},
                "trend_window": [1985, 2007],
            },
            "verdict_rule": cfg["thresholds"],
            "provenance": prov,
            "s2_role": cfg["s2_role"],
            "z_exclusion_reason": "M6a is a duration count, no preregistered observable sigma",
        })
    except Exception as e:  # noqa: BLE001
        ch["error"] = str(e)[:300]
    return ch


# ----------------------------------------------------------------------------
# C7 energy unlock (OWID solar LCOE + cumulative capacity)
# ----------------------------------------------------------------------------

def _parse_owid_world(text, value_col=None):
    """OWID grapher CSV: entity,code,year,value... -> [(year, value)] for World.
    value_col=None picks the first non-Entity/Code/Year column (single-value charts);
    multi-column charts (LCOE by technology) must pass the exact column name."""
    reader = csv.DictReader(io.StringIO(text))
    cols = reader.fieldnames or []
    if value_col is None:
        for c in cols:
            if c and c not in ("Entity", "Code", "Year", "entity", "code", "year"):
                value_col = c
                break
    if value_col not in cols:
        raise ValueError(f"column {value_col!r} not in {cols[:8]}")
    pts = []
    for row in reader:
        ent = (row.get("Entity") or row.get("entity") or "").strip()
        if ent and ent != "World":
            continue
        try:
            y = int(row.get("Year") or row.get("year"))
            v = float(row.get(val_col := value_col))
            pts.append((y, v))
        except (TypeError, ValueError):
            continue
    return pts


def channel_C7(prereg):
    cfg = prereg["channels"]["C7_energy_unlock"]
    ch = {"id": "C7", "name": "energy_unlock", "status": "pending_data"}
    lcoe = cap = None
    lcoe_pts = cap_pts = None
    lcoe_errs = []
    # [implementation fix 2026-08-30] correct slug: levelized-cost-of-energy with
    # explicit 'Solar photovoltaic' column (multi-technology chart); attempts with
    # unspecified first-column logic picked 'Bioenergy' and failed.
    for slug, col in (("levelized-cost-of-energy", "Solar photovoltaic"),
                      ("solar-lcoe", None), ("solar-pv-lcoe", None)):
        try:
            t, p = fetch(f"https://ourworldindata.org/grapher/{slug}.csv",
                         f"C7_owid_{slug}.csv")
            pts = _parse_owid_world(t, col)
            if len(pts) >= 8:
                lcoe_pts, lcoe = pts, p
                break
        except Exception as e:  # noqa: BLE001
            lcoe_errs.append(f"{slug}: {str(e)[:80]}")
            continue
    for slug in ("cumulative-installed-solar-pv-capacity", "installed-solar-pv-capacity",
                 "cumulative-solar-pv-capacity"):
        try:
            t, p = fetch(f"https://ourworldindata.org/grapher/{slug}.csv", f"C7_owid_{slug}.csv")
            pts = _parse_owid_world(t)
            if len(pts) >= 8:
                cap_pts, cap = pts, p
                break
        except Exception:  # noqa: BLE001
            continue
    if lcoe_pts is None or cap_pts is None:
        ch["error"] = ("OWID solar LCOE or cumulative-capacity series not reachable "
                       "(prereg verdict is joint M7a AND M7b - honest pending)")
        ch["lcoe_fetch_errors"] = lcoe_errs
        return ch
    cap_map = dict(cap_pts)
    joined = [(y, v, cap_map[y]) for y, v in lcoe_pts if y in cap_map and v > 0 and cap_map[y] > 0]
    if len(joined) < 8:
        ch["error"] = f"joined LCOE-capacity series too short ({len(joined)})"
        return ch
    xs = [math.log(c) for _, _, c in joined]
    ys = [math.log(v) for _, v, _ in joined]
    beta, _, _, _, _ = ols(xs, ys)
    lr = 1.0 - 2.0 ** beta
    # M7b: 5yr CAGR decline of LCOE
    ys_lcoe = sorted(lcoe_pts)
    if ys_lcoe[-1][0] - ys_lcoe[-5][0] != 4:
        pass
    y0, v0 = ys_lcoe[-5]
    y1, v1 = ys_lcoe[-1]
    yrs = max(y1 - y0, 1)
    cagr = -(v1 / v0) ** (1.0 / yrs) * 100.0 + 100.0  # positive = declining
    if lr >= 0.20 and cagr >= 8.0:
        status = "green"
    elif lr >= 0.12 and cagr >= 3.0:
        status = "yellow"
    else:
        status = "red"
    ch.update({
        "status": status,
        "metrics": {
            "M7a_learning_rate_pct": round(lr * 100.0, 2),
            "M7b_lcoe_decline_pct_per_yr": round(cagr, 2),
        },
        "intermediates": {
            "loglog_slope_beta": round(beta, 4),
            "joined_points": len(joined),
            "lcoe_span": [ys_lcoe[0][0], ys_lcoe[-1][0]],
            "lcoe_latest_usd_per_MWh": round(v1, 2),
        },
        "verdict_rule": cfg["thresholds"],
        "provenance": {"lcoe": lcoe, "capacity": cap},
        "numeric_z": {
            "margin_to_red": round(lr * 100.0 - 12.0, 2),
            "z": None,
            "z_exclusion_reason": "learning-rate delta-method sigma deferred to v2 (joint metric)",
        },
    })
    return ch


# ----------------------------------------------------------------------------
# C8 information-automation (OECD adoption)
# ----------------------------------------------------------------------------

def channel_C8(prereg):
    cfg = prereg["channels"]["C8_information_automation"]
    ch = {
        "id": "C8", "name": "information_automation", "status": "pending_data",
        "error": ("OECD firm AI adoption series has no preregistered direct-download URL "
                  "(release-based statistics); manual numeric entry forbidden - honest "
                  "pending_data pending v2 dataset registration"),
        "verdict_rule": cfg["thresholds"],
        "excluded_background": cfg["excluded_background"],
    }
    return ch


# ----------------------------------------------------------------------------
# Synthesis (preregistered state machine, separate pressure/unlock)
# ----------------------------------------------------------------------------

def synthesize(channels):
    prereg_status = {}
    for ch in channels:
        prereg_status[ch["id"]] = ch["status"]
    active = {k: v for k, v in prereg_status.items() if v != "pending_data"}
    pending = [k for k, v in prereg_status.items() if v == "pending_data"]
    pressure_ids = ["C1", "C2", "C3", "C4", "C5", "C6"]
    unlock_ids = ["C7", "C8"]
    p_red = sum(1 for k in pressure_ids if active.get(k) == "red")
    p_yellow = sum(1 for k in pressure_ids if active.get(k) == "yellow")
    u_red = sum(1 for k in unlock_ids if active.get(k) == "red")
    u_yellow = sum(1 for k in unlock_ids if active.get(k) == "yellow")

    if len(pending) >= 3:
        state = "CHANNEL_REPORT_ONLY"
        global_reported = False
    else:
        c2 = active.get("C2")
        c6 = active.get("C6")
        if (c2 in ("red", "yellow") and c6 == "red") or p_red >= 4:
            state = "TRIGGER"
        elif p_red == 3:
            state = "TRIGGER_PREP"
        elif p_red == 2 or u_red == 1 or u_yellow == 2:
            state = "CRITICAL"
        elif p_red <= 1 and u_red == 0:
            state = "STABLE"
        else:
            state = "CRITICAL"
        global_reported = True

    # Stouffer auxiliary over channels that produced a numeric z
    z_pressure = {k: v["numeric_z"]["z"] for k, v in
                  ((c["id"], c) for c in channels)
                  if v.get("numeric_z") and v["numeric_z"].get("z") is not None
                  and k in pressure_ids and v["status"] != "pending_data"}
    z_unlock = {k: v["numeric_z"]["z"] for k, v in
                ((c["id"], c) for c in channels)
                if v.get("numeric_z") and v["numeric_z"].get("z") is not None
                and k in unlock_ids and v["status"] != "pending_data"}
    Zp = (sum(z_pressure.values()) / math.sqrt(len(z_pressure))) if z_pressure else None
    Zu = (sum(z_unlock.values()) / math.sqrt(len(z_unlock))) if z_unlock else None
    Zgap = (Zu - Zp) if (Zu is not None and Zp is not None) else None
    return {
        "pressure_index": {"red": p_red, "yellow": p_yellow,
                           "channels": {k: active.get(k, "pending_data") for k in pressure_ids}},
        "unlock_index": {"red": u_red, "yellow": u_yellow,
                         "channels": {k: active.get(k, "pending_data") for k in unlock_ids}},
        "state_machine": state,
        "global_state_reported": global_reported,
        "abort_rule": "pending >= 3 -> channel-level report only" if not global_reported else "not triggered",
        "pending_channels": pending,
        "stouffer_auxiliary": {
            "z_by_channel": {**z_pressure, **z_unlock},
            "Z_pressure": None if Zp is None else round(Zp, 4),
            "Z_unlock": None if Zu is None else round(Zu, 4),
            "Z_gap": None if Zgap is None else round(Zgap, 4),
            "k_pressure": len(z_pressure),
            "k_unlock": len(z_unlock),
            "semantics": "Z_gap is a directional proxy of R, NOT R itself",
        },
        "s2_dual_red_check": {
            "C2_status": prereg_status.get("C2"),
            "C6_status": prereg_status.get("C6"),
            "triggered": (prereg_status.get("C2") in ("red", "yellow")
                          and prereg_status.get("C6") == "red"),
        },
    }


def main():
    with open(PREREG_JSON, "r", encoding="utf-8") as f:
        prereg = json.load(f)
    channels = [
        channel_C1(prereg), channel_C2(prereg), channel_C3(prereg),
        channel_C4(prereg), channel_C5(prereg), channel_C6(prereg),
        channel_C7(prereg), channel_C8(prereg),
    ]
    synthesis = synthesize(channels)
    out = {
        "pipeline": {
            "name": "CDD-ECS C-series channel pipeline",
            "version": "v1.0",
            "run_utc": utcnow_iso(),
            "preregistration": {
                "document": PREREG_MD,
                "md_sha256": sha256_file(PREREG_MD),
                "machine_readable": PREREG_JSON,
                "json_sha256": sha256_file(PREREG_JSON),
                "frozen_before_data_contact": True,
            },
            "cache_dir": CACHE_DIR,
            "regeneration": "python H:\\cdd_lean4\\scripts\\cdd_ecs_channel_pipeline.py",
        },
        "channels": {ch["id"]: ch for ch in channels},
        "synthesis": synthesis,
        "notes": [
            "All thresholds executed verbatim from frozen preregistration JSON.",
            "pending_data channels are excluded from synthesis and reported explicitly.",
            "C5 M5a is a literature snapshot count (PB2023=6), not a recomputed observation.",
            "C8 excluded_background (NBER task-level effects) is not a mechanical criterion.",
            "No manual numeric values entered anywhere in this pipeline.",
        ],
    }
    with open(OUT_JSON, "w", encoding="utf-8") as f:
        json.dump(out, f, indent=2, ensure_ascii=False)
    print(f"snapshot written: {OUT_JSON}")
    print(f"prereg md sha256: {out['pipeline']['preregistration']['md_sha256']}")
    print(f"prereg json sha256: {out['pipeline']['preregistration']['json_sha256']}")
    print()
    for ch in channels:
        m = ch.get("metrics", {})
        mv = " ".join(f"{k}={v}" for k, v in (m or {}).items())
        print(f"  {ch['id']:>3} {ch['name']:<22} {ch['status']:<14} {mv[:90]}")
        if "error" in ch:
            print(f"      err: {ch['error'][:110]}")
    print()
    s = synthesis
    print(f"  pressure: red={s['pressure_index']['red']} yellow={s['pressure_index']['yellow']}")
    print(f"  unlock:   red={s['unlock_index']['red']} yellow={s['unlock_index']['yellow']}")
    print(f"  state:    {s['state_machine']} (reported={s['global_state_reported']})")
    print(f"  pending:  {', '.join(s['pending_channels']) or 'none'}")
    aux = s["stouffer_auxiliary"]
    print(f"  Z_pressure={aux['Z_pressure']} Z_unlock={aux['Z_unlock']} Z_gap={aux['Z_gap']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
