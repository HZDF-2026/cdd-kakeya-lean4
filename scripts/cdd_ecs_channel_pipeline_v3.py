#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""CDD-ECS C-series channel pipeline v3.0 (prereg v1.0 + amendments A1 + A2).

Discipline:
  - Thresholds executed VERBATIM from the frozen v1.0 preregistration JSON;
    routes/constants from amendment A1 JSON; C1 metric definition (margin
    form) from amendment A2 JSON (threshold_changes = 0 in both).
  - Event order (A2 §3 disclosure): v1 freeze -> v1 run (snapshot v1) ->
    reachability/format probes (no metric computed) -> A1 registration ->
    v2 run (snapshot v2) -> post-run verdict review (C1 sign defect found;
    no threshold viewed/adjusted) -> A2 registration -> THIS v3 run.
  - A2-1 implementation guard: this script asserts the frozen corrected
    formula string from the A2 JSON before computing C1.
  - Cache-first fetching (text + binary). Files downloaded during the probe
    phase are adopted with honest provenance registration (url + sha256).
  - Download failure -> channel 'pending_data'; manual numeric entry FORBIDDEN.
  - C4 partial decidability per A1-5 (literal OR semantics of v1.0 thresholds).
  - Snapshot: H:\\cdd_ecs_channel_pipeline_results_v3.json (new file;
    v1/v2 frozen; v2 C1 verdict + downstream superseded per A2 §0.5).
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
A1_MD = r"H:\cdd_ecs_channel_preregistration_A1_20260830.md"
A1_JSON = r"H:\cdd_ecs_channel_preregistration_v1_amendment_A1.json"
A2_MD = r"H:\cdd_ecs_channel_preregistration_A2_20260830.md"
A2_JSON = r"H:\cdd_ecs_channel_preregistration_v1_amendment_A2.json"
CACHE_DIR = r"H:\cdd_ecs_data"
OUT_JSON = r"H:\cdd_ecs_channel_pipeline_results_v3.json"

USER_AGENT = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) CDD-ECS-pipeline/3.0"

HADCRUT5_URL = ("https://www.metoffice.gov.uk/hadobs/hadcrut5/data/"
                "HadCRUT.5.0.2.0/analysis/diagnostics/"
                "HadCRUT.5.0.2.0.analysis.summary_series.global.monthly.csv")


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


def _cache_paths(cache_key: str):
    safe = re.sub(r"[^A-Za-z0-9._-]", "_", cache_key)
    cache_path = os.path.join(CACHE_DIR, safe)
    return cache_path, cache_path + ".meta.json"


def fetch(url: str, cache_key: str, timeout: int = 90):
    """Cache-first TEXT download. Returns (text, provenance) or raises."""
    cache_path, meta_path = _cache_paths(cache_key)
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


def fetch_binary(url: str, cache_key: str, timeout: int = 600):
    """Cache-first BINARY download. Returns (path, provenance) or raises.

    A file that exists WITHOUT meta is a probe-phase artifact downloaded from
    the same A1-registered URL; it is adopted with honest registration.
    """
    cache_path, meta_path = _cache_paths(cache_key)
    if os.path.exists(cache_path):
        if not os.path.exists(meta_path):
            meta = {
                "url": url,
                "downloaded_utc": None,
                "raw_sha256": sha256_file(cache_path),
                "bytes": os.path.getsize(cache_path),
                "cache_hit": True,
                "note": "adopted pre-A1 probe-phase download (same registered URL); "
                        "probe computed no metrics (A1 §0.2)",
            }
            with open(meta_path, "w", encoding="utf-8") as f:
                json.dump(meta, f, indent=2)
        else:
            with open(meta_path, "r", encoding="utf-8") as f:
                meta = json.load(f)
            meta["cache_hit"] = True
        return cache_path, meta
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        raw = resp.read()
    with open(cache_path, "wb") as f:
        f.write(raw)
    meta = {
        "url": url,
        "downloaded_utc": utcnow_iso(),
        "raw_sha256": sha256_bytes(raw),
        "bytes": len(raw),
        "cache_hit": False,
    }
    with open(meta_path, "w", encoding="utf-8") as f:
        json.dump(meta, f, indent=2)
    return cache_path, meta


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


# ----------------------------------------------------------------------------
# C1 temperature (GISTEMP primary; HadCRUT5 cross + A1-1 runtime offset derivation)
# ----------------------------------------------------------------------------

def parse_gistemp_monthly(text):
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


def _parse_hadcrut5(text):
    pts = []
    for line in text.splitlines():
        parts = line.split(",")
        if len(parts) >= 2 and re.match(r"^\d{4}-\d{2}$", parts[0].strip()):
            try:
                pts.append((parts[0].strip(), float(parts[1])))
            except ValueError:
                pass
    return pts


def channel_C1(prereg, a1):
    cfg = prereg["channels"]["C1_temperature"]
    a1c1 = a1["amendments"]["C1_baseline_offset"]
    fb = a1c1["fallback_constants_if_hadcrut5_unreachable"]
    ch = {"id": "C1", "name": "temperature_path", "status": "pending_data"}

    # ---- A1-1: derive baseline offsets at runtime from HadCRUT5 ----
    off_pi = fb["off_1850_1900_C"]          # HadCRUT5 1961-1990 -> 1850-1900
    off_5180 = None                          # HadCRUT5 1961-1990 -> 1951-1980
    off_gistemp = fb["gistemp_pi_offset_C"]  # GISTEMP 1951-1980 -> 1850-1900
    offsets = {
        "mode": "fallback_constants (A1-1)",
        "off_1850_1900_C": off_pi,
        "off_1951_1980_C": None,
        "gistemp_pi_offset_C": off_gistemp,
    }
    pts5 = []
    cross = {"id": "HadCRUT5", "status": "unavailable"}
    try:
        t5, p5 = fetch(HADCRUT5_URL, "C1_hadcrut5_monthly.csv")
        pts5 = _parse_hadcrut5(t5)

        def mean_band(y0, y1):
            vals = [v for d, v in pts5 if y0 <= int(d[:4]) <= y1]
            return (sum(vals) / len(vals)) if vals else None

        m_pi = mean_band(1850, 1900)
        m_51 = mean_band(1951, 1980)
        if m_pi is not None and m_51 is not None:
            off_pi = -m_pi
            off_5180 = -m_51
            off_gistemp = off_pi - off_5180
            offsets = {
                "mode": "derived_at_runtime_from_hadcrut5 (A1-1)",
                "off_1850_1900_C": round(off_pi, 4),
                "off_1951_1980_C": round(off_5180, 4),
                "gistemp_pi_offset_C": round(off_gistemp, 4),
                "a1_measured_reference": a1c1["measured_from_cached_file"],
            }
            cross = {"id": "HadCRUT5", "status": "ok", "provenance": p5,
                     "n_months": len(pts5), "last_month": pts5[-1][0]}
        else:
            cross = {"id": "HadCRUT5", "status": "insufficient_baseline_overlap"}
    except Exception as e:  # noqa: BLE001
        cross = {"id": "HadCRUT5", "status": "unreachable", "error": str(e)[:200]}
    ch["offsets"] = offsets

    try:
        text, prov = fetch(cfg["primary_source"]["url"], "C1_gistemp_monthly.csv")
        rows = parse_gistemp_monthly(text)
        if len(rows) < 12 * cfg["quality_gates"]["min_series_years"]:
            ch["error"] = f"series too short ({len(rows)} months)"
            ch["provenance"] = prov
            return ch
        by_ym = {(y, m): v for y, m, v in rows}
        last_y, last_m = max(by_ym)
        vals, used = [], []
        y, m = last_y, last_m
        for _ in range(12):
            if (y, m) not in by_ym:
                ch["error"] = f"missing month {(y, m)} in trailing window"
                ch["provenance"] = prov
                return ch
            vals.append(by_ym[(y, m)])
            used.append((y, m))
            m -= 1
            if m == 0:
                m, y = 12, y - 1
        t12 = sum(vals) / 12.0
        # A2-1 [F]: margin form M1 = 1.5 - T_12m (thresholds verbatim from v1.0)
        m1 = 1.5 - (t12 + off_gistemp)
        ann = {}
        for y0, m0, v in rows:
            ann.setdefault(y0, []).append(v)
        years = sorted(ann)
        ann_mean = [sum(ann[y0]) / len(ann[y0]) for y0 in years]
        _, _, sigma, _, _ = ols(years[-30:], ann_mean[-30:])
        if m1 > 0.30:
            status = "green"
        elif m1 > 0.0:
            status = "yellow"
        else:
            status = "red"
        ch.update({
            "status": status,
            "metrics": {"M1_margin_to_1.5C_C": round(m1, 4)},
            "a2_1_applied": "M1 = 1.5 - T_12m (margin form, A2-1 [F]; thresholds verbatim)",
            "intermediates": {
                "trailing_window": [f"{used[-1][0]}-{used[-1][1]:02d}", f"{last_y}-{last_m:02d}"],
                "t12_C_vs_1951_1980": round(t12, 4),
                "t12_C_vs_1850_1900": round(t12 + off_gistemp, 4),
                "annual_series_years": [years[0], years[-1]],
                "sigma_annual_residual_C": round(sigma, 4),
            },
            "verdict_rule": cfg["thresholds"],
            "provenance": prov,
            "numeric_z": {
                "margin_to_red": round(m1 - 0.0, 4),
                "sigma": round(sigma, 4),
                "z": round((m1 - 0.0) / sigma, 4) if sigma and sigma > 0 else None,
                "sign_note": "A2-1 margin form: red boundary below metric (red at M1 <= 0); "
                             "larger = safer; no sign inversion (v1.0 §2.3 unified)",
            },
        })
        # ---- cross source, A1-2: trailing mean (sum/12), not sum ----
        if pts5 and len(pts5) >= 12:
            last12 = pts5[-12:]
            t12_h = sum(v for _, v in last12) / 12.0 + off_pi
            diff = abs((t12 + off_gistemp) - t12_h)
            cross.update({
                "t12_C_vs_1850_1900": round(t12_h, 4),
                "hadcrut5_window": [last12[0][0], last12[-1][0]],
                "abs_diff_C": round(diff, 4),
                "disagreement_gate_C": cfg["cross_disagreement_gate"]["abs_diff_C"],
                "disagreement": diff > cfg["cross_disagreement_gate"]["abs_diff_C"],
                "window_alignment_note": (
                    f"HadCRUT5 source series ends {pts5[-1][0]} (fetched fresh at run "
                    f"time; upstream lag), GISTEMP window ends {last_y}-{last_m:02d}; "
                    "trailing windows are offset. Preregistered rule (each source its "
                    "own trailing 12 months) executed verbatim; freshness observation "
                    "only, no verdict adjustment"
                ),
            })
            if cross["disagreement"]:
                ch["status"] = "yellow"
                ch["cross_source_disagreement"] = True
        ch["cross_source"] = cross
    except Exception as e:  # noqa: BLE001
        ch["error"] = str(e)[:300]
    return ch


# ----------------------------------------------------------------------------
# C2 AMOC (RAPID 26.5N) - A1-8: maintain pending_data with route registration
# ----------------------------------------------------------------------------

def channel_C2(prereg, a1):
    cfg = prereg["channels"]["C2_amoc"]
    routes = a1["amendments"]["C2_C6_pending_routes"]["C2"]
    ch = {"id": "C2", "name": "amoc", "status": "pending_data"}
    candidates = [
        "https://rapid.ac.uk/rapidmoc/rapid_data/moc_transports.csv",
        "https://rapid.ac.uk/rapidmoc/rapid_data/datadl/moc_transports.csv",
        "https://rapid.ac.uk/rapidmoc/rapid_data/OSNAP/moc_transports.csv",
    ]
    text = None
    for url in candidates:
        try:
            text, prov = fetch(url, "C2_rapid_moc.csv")
            break
        except Exception:  # noqa: BLE001
            continue
    if text is None:
        ch["error"] = "RAPID 26.5N transports unreachable at registered candidates"
        ch["registered_blocked_routes"] = routes
        ch["verdict_rule"] = cfg["thresholds"]
        return ch
    head = text[:500].lower()
    if text.lstrip()[:15].lower().startswith("<!doctype html") or "<html" in head:
        ch["error"] = ("RAPID direct URL returns an HTML email-gated download form, "
                       "not data (A1-8). No semantic substitution permitted "
                       "(v1.0 §0.5: no proxy/reconstruction series).")
        ch["registered_blocked_routes"] = routes
        ch["verdict_rule"] = cfg["thresholds"]
        return ch
    # reachable data path (future FRED-like auto-recalc): tolerant parse
    pts = []
    for line in text.splitlines():
        parts = [p.strip() for p in line.split(",")]
        if len(parts) < 2:
            continue
        mth = re.match(r"^(\d{4})-(\d{2})", parts[0])
        if not mth:
            continue
        for v in parts[1:]:
            try:
                pts.append((int(mth.group(1)), int(mth.group(2)), float(v)))
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
    cross_year = (cfg["collapse_threshold_Sv"] - a) / b if b < 0 else None
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
        "numeric_z": {
            "margin_to_red": round(m2b - cfg["red_anchor_numeric"], 4),
            "sigma": round(sigma, 4),
            "z": round((m2b - cfg["red_anchor_numeric"]) / sigma, 4) if sigma > 0 else None,
        },
    })
    return ch


# ----------------------------------------------------------------------------
# C3 ice sheets - A1-6: IMBIE promotion (v1.0 registered cross-source)
# ----------------------------------------------------------------------------

def _parse_imbie_xlsx(path, sheet, col_name):
    import openpyxl
    wb = openpyxl.load_workbook(path, read_only=True, data_only=True)
    try:
        ws = wb[sheet]
        it = ws.iter_rows(values_only=True)
        header = next(it)
        header = [str(h).strip() if h is not None else "" for h in header]
        year_idx = None
        for i, h in enumerate(header):
            if h.lower() == "year":
                year_idx = i
                break
        cum_idx = None
        for i, h in enumerate(header):
            hl = h.lower()
            if "cumulative" in hl and "mass change (gt)" in hl and "uncert" not in hl:
                cum_idx = i
                break
        if cum_idx is None:
            for i, h in enumerate(header):
                if h == col_name:
                    cum_idx = i
                    break
        if year_idx is None or cum_idx is None:
            raise ValueError(f"IMBIE columns not found; header={header[:6]}")
        pts = []
        for r in it:
            if r is None:
                continue
            try:
                yy = float(r[year_idx])
                vv = float(r[cum_idx])
            except (TypeError, ValueError, IndexError):
                continue
            pts.append((yy, vv))
        return pts, header
    finally:
        wb.close()


def channel_C3(prereg, a1):
    cfg = prereg["channels"]["C3_icesheets"]
    promo = a1["amendments"]["C3_source_promotion"]
    ch = {"id": "C3", "name": "ice_sheets", "status": "pending_data"}
    try:
        import openpyxl  # noqa: F401
    except ImportError:
        ch["error"] = "openpyxl unavailable - IMBIE XLSX not parseable (A1-6 dependency)"
        return ch
    specs = {
        "greenland": (promo["greenland"], "C3_imbie_greenland_2020_02_28.xlsx"),
        "antarctica": (promo["antarctica"], "C3_imbie_2018_07_23.xlsx"),
    }
    sheets = {}
    for name, (spec, cache_key) in specs.items():
        try:
            path, prov = fetch_binary(spec["url"], cache_key, timeout=300)
            pts, header = _parse_imbie_xlsx(path, spec["sheet"], spec["column"])
            if len(pts) < 12 * 10:
                raise ValueError(f"series too short ({len(pts)} pts)")
            sheets[name] = {"pts": pts, "provenance": prov, "spec": spec}
        except Exception as e:  # noqa: BLE001
            ch.setdefault("sheet_errors", {})[name] = str(e)[:200]
    if len(sheets) < 2:
        ch["error"] = f"IMBIE series incomplete: {sorted(sheets)} (A1-6 requires both GIS and AIS)"
        ch["sheet_errors"] = ch.get("sheet_errors", {})
        return ch
    metrics = {}
    intermediates = {}
    extrap_mm = {}
    for name, d in sheets.items():
        pts = d["pts"]
        xs = [p[0] for p in pts]
        ys = [p[1] for p in pts]
        t_last = max(xs)
        win = [p for p in pts if p[0] >= t_last - 10.0]
        b10, _, sig10, t10, n10 = ols([p[0] for p in win], [p[1] for p in win])
        loss = -b10  # Gt/yr, positive = mass loss
        cum_last = ys[-1]
        cum_2100 = cum_last - loss * (2100.0 - t_last)
        slr_mm = abs(cum_2100) / promo["slr_conversion_Gt_per_mm"]
        extrap_mm[name] = slr_mm
        mkey = "M3a" if name == "greenland" else "M3b"
        metrics[f"{mkey}_{name}_loss_Gt_per_yr"] = round(loss, 2)
        intermediates[f"{name}"] = {
            "series_span": [round(min(xs), 2), round(t_last, 2)],
            "series_points": len(pts),
            "last10_window": [round(t_last - 10.0, 2), round(t_last, 2)],
            "last10_points": n10,
            "ols_slope_Gt_per_yr": round(b10, 2),
            "ols_t_stat": round(t10, 2),
            "sigma_residual_Gt": round(sig10, 2),
            "cumulative_mass_last_Gt": round(cum_last, 1),
            "extrapolated_2100_cum_Gt": round(cum_2100, 1),
            "extrapolated_2100_slr_mm": round(slr_mm, 2),
            "vintage": d["spec"]["vintage"],
            "provenance": d["provenance"],
        }
    gis = metrics["M3a_greenland_loss_Gt_per_yr"]
    ais = metrics["M3b_antarctica_loss_Gt_per_yr"]
    slr_total = sum(extrap_mm.values())
    anchors = promo["thresholds_unchanged"]
    if (gis > anchors["GIS_red"] or ais > anchors["AIS_red"]
            or slr_total > anchors["slr_red_mm"]):
        status = "red"
    elif gis > anchors["GIS_yellow"] or ais > anchors["AIS_yellow"]:
        status = "yellow"
    else:
        status = "green"
    gis_span = intermediates["greenland"]["series_span"]
    ais_span = intermediates["antarctica"]["series_span"]
    ch.update({
        "status": status,
        "metrics": metrics,
        "intermediates": {
            **intermediates,
            "slr_extrapolation_total_mm": round(slr_total, 2),
            "slr_extrapolation_rule": ("per-series extrapolation to 2100 "
                                       "(cum_last - loss*(2100 - t_last_series)); "
                                       "A1-6 formula with per-series t_last; "
                                       f"conversion {promo['slr_conversion_Gt_per_mm']} Gt/mm"),
            "slr_red_branch_triggered": slr_total > anchors["slr_red_mm"],
            "a1_span_note": (
                "A1-6 stated span '1980.0-2019.9, 469 points' describes the Year "
                "column (468 data rows, 1980.0-2018.92); the REGISTERED cumulative "
                "column is populated only from 1992.0 (pre-1992 cells are None; "
                "early-year values in the sheet belong to SMB/dynamics anomaly "
                "columns). Registered column name and metric rule executed "
                "verbatim; documentation observation only, no threshold/route change"
            ),
        },
        "verdict_rule": cfg["thresholds"],
        "source_promotion": "A1-6 [S]: IMBIE (v1.0 registered cross-source, UK Leeds); "
                            "NASA JPL mascon remains preferred future primary "
                            "(Earthdata credential-gated)",
        "gap_interpolated": True,
        "gap_note": "GRACE/GRACE-FO 2017-2018 mission gap interpolated inside IMBIE series",
        "data_cutoff_note": (f"different vintages: GIS 2020-02-28 (to {gis_span[1]}), "
                             f"AIS 2018-07-23 (to {ais_span[1]})"),
        "numeric_z": None,
        "z_exclusion_reason": "two-metric channel (M3a/M3b); no preregistered rule to "
                              "collapse two sheet z's into one channel z (v1.0 §2.3 is "
                              "per-channel; unchanged by A1)",
    })
    return ch


# ----------------------------------------------------------------------------
# C4 biosphere - A1-4 NCEI FTP NetCDF route + A1-5 partial decidability
# ----------------------------------------------------------------------------

def channel_C4(prereg, a1):
    cfg = prereg["channels"]["C4_biosphere"]
    route = a1["amendments"]["C4_route"]
    part = a1["amendments"]["C4_partial_decidability"]["M4a_only"]
    ch = {"id": "C4", "name": "biosphere", "status": "pending_data"}
    ch["m4b_status"] = route["M4b_status"]
    try:
        import h5py  # noqa: F401
    except ImportError:
        ch["error"] = "h5py unavailable (A1-4 dependency) - pending_data; " \
                      "substitution by text mirror forbidden"
        return ch
    try:
        path, prov = fetch_binary(route["url"], "C4_ncei_ohc_0-2000_yearly.nc", timeout=600)
        import h5py
        with h5py.File(path, "r") as hf:
            time_v = [float(t) for t in hf["time"][()]]
            ohc = [float(x) for x in hf[route["variable"]][()]]
            se = [float(x) for x in hf[route["se_variable"]][()]]
            units = hf[route["variable"]].attrs.get("units")
            units = units.decode() if isinstance(units, bytes) else str(units)
        years = [1955.0 + t / 12.0 for t in time_v]
        if len(years) < cfg["quality_gates"]["ohc_min_years"]:
            ch["error"] = f"OHC series too short ({len(years)} yr)"
            ch["provenance"] = prov
            return ch
        t_max = years[-1]
        win = [(x, v) for x, v in zip(years, ohc) if x >= t_max - 10.0]
        b10, _, sig10, t10, n10 = ols([x for x, _ in win], [v for _, v in win])
        m4a = b10 * 10.0  # 10^22 J/yr -> ZJ/yr
        # A1-5 partial decidability (literal OR semantics of frozen thresholds)
        if m4a > 10.0:
            status = "red"
            decidability = part["M4a_gt_10"]
        elif m4a >= 5.0:
            status = "yellow"
            decidability = part["M4a_in_5_10"]
        else:
            status = "pending_data"
            decidability = part["M4a_lt_5"]
        ch.update({
            "status": status,
            "metrics": {"M4a_ohc_trend_ZJ_per_yr": round(m4a, 3)},
            "intermediates": {
                "series_years": [round(years[0], 2), round(t_max, 2)],
                "series_points": len(years),
                "last10_window": [round(t_max - 10.0, 2), round(t_max, 2)],
                "last10_points": n10,
                "ols_slope_1e22J_per_yr": round(b10, 4),
                "ols_t_stat": round(t10, 2),
                "sigma_residual_1e22J": round(sig10, 3),
                "variable": route["variable"],
                "units": units,
                "se_variable_last": round(se[-1], 3),
                "partial_decidability_rule": decidability,
                "route_class": "A1-4 [R] same agency/dataset (NOAA NCEI), FTP archive path",
            },
            "verdict_rule": cfg["thresholds"],
            "provenance": prov,
        })
        if status != "pending_data":
            ch["numeric_z"] = {
                "margin_to_red": round(10.0 - m4a, 3),
                "sigma": round(sig10 * 10.0, 3),
                "z": round((10.0 - m4a) / (sig10 * 10.0), 4) if sig10 > 0 else None,
                "sign_note": "red boundary above metric; z sign inverted so larger = safer",
            }
        else:
            ch["error"] = ("M4a < 5 ZJ/yr: verdict depends on unavailable M4b "
                           "(A1-5 literal semantics) - pending_data")
    except Exception as e:  # noqa: BLE001
        ch["error"] = str(e)[:300]
    return ch


# ----------------------------------------------------------------------------
# C5 biogeochemical (NOAA GML CO2 + frozen PB count) - unchanged by A1
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
                "M5a_provenance": "literature_snapshot (PB2023 fixed), not recomputed observation",
            },
            "verdict_rule": cfg["thresholds"],
            "provenance": prov,
            "numeric_z": {
                "margin_to_red": round(85.0 - m5b, 2),
                "sigma": round(sigma, 3),
                "z": round((85.0 - m5b) / sigma, 3) if sigma > 0 else None,
                "sign_note": "red boundary above metric; z sign inverted so larger = safer",
            },
        })
    except Exception as e:  # noqa: BLE001
        ch["error"] = str(e)[:300]
    return ch


# ----------------------------------------------------------------------------
# C6 social structure (FRED) - A1-8: pending, auto-recalc when reachable
# ----------------------------------------------------------------------------

def channel_C6(prereg, a1):
    cfg = prereg["channels"]["C6_social_structure"]
    routes = a1["amendments"]["C2_C6_pending_routes"]["C6"]
    ch = {"id": "C6", "name": "social_structure", "status": "pending_data"}
    text = prov = None
    last_err = None
    for _ in range(2):
        try:
            text, prov = fetch(cfg["primary_source"]["url"], "C6_fred_MEHOINUSA672N.csv",
                               timeout=90)
            break
        except Exception as e:  # noqa: BLE001
            last_err = str(e)[:200]
            time.sleep(5)
    if text is None:
        ch["error"] = f"FRED unreachable (A1-8): {last_err}"
        ch["registered_blocked_routes"] = routes
        ch["verdict_rule"] = cfg["thresholds"]
        ch["auto_recalc_note"] = "recalculates automatically once FRED is reachable; no new amendment needed"
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
        m6a = 0 if latest_v >= 0.99 * peak_v else latest_y - peak_y
        if m6a > 15:
            status = "red"
        elif m6a >= 5:
            status = "yellow"
        else:
            status = "green"
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
# C7 energy unlock (OWID) - A1-3 unit annotation only
# ----------------------------------------------------------------------------

def _parse_owid_world(text, value_col=None):
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
            v = float(row.get(value_col))
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
        ch["error"] = "OWID solar LCOE or cumulative-capacity series not reachable"
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
    ys_lcoe = sorted(lcoe_pts)
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
            "lcoe_latest_usd_per_kWh": round(v1, 4),
            "lcoe_latest_usd_per_MWh": round(v1 * 1000.0, 2),
            "unit_note": "A1-3 [F]: OWID LCOE units are USD/kWh; x1000 = USD/MWh; "
                         "M7a/M7b are ratio/rate metrics, unit does not enter verdict",
        },
        "verdict_rule": cfg["thresholds"],
        "provenance": {"lcoe": lcoe, "capacity": cap},
        "numeric_z": {
            "margin_to_red": round(lr * 100.0 - 12.0, 2),
            "z": None,
            "z_exclusion_reason": "v1 deferred, A1 did not register a C7 z-program; "
                                  "post-hoc instantiation would violate the prereg "
                                  "discipline (auxiliary only, no verdict impact)",
        },
    })
    return ch


# ----------------------------------------------------------------------------
# C8 information-automation - A1-7 OECD SDMX route
# ----------------------------------------------------------------------------

def channel_C8(prereg, a1):
    cfg = prereg["channels"]["C8_information_automation"]
    route = a1["amendments"]["C8_route"]
    flt = route["filters"]
    ch = {"id": "C8", "name": "information_automation", "status": "pending_data"}
    text = None
    prov = None
    try:
        text, prov = fetch(route["url"], "C8_oecd_ictb.csv", timeout=900)
    except Exception as e:  # noqa: BLE001
        probe_path = os.path.join(CACHE_DIR, "C8_oecd_ictb_probe.csv")
        if os.path.exists(probe_path):
            with open(probe_path, "r", encoding="utf-8", errors="replace") as f:
                text = f.read()
            prov = {
                "url": route["url"],
                "fallback_artifact": probe_path,
                "raw_sha256": sha256_file(probe_path),
                "bytes": os.path.getsize(probe_path),
                "cache_hit": True,
                "note": "A1-registered URL download failed; probe-phase artifact "
                        "adopted (downloaded 2026-08-30 from same dataflow "
                        "DSD_ICT_B@DF_BUSINESSES,latest/all with startPeriod=2014; "
                        "probe computed no metrics - A1 §0.2)",
                "download_error": str(e)[:150],
            }
    if text is None:
        ch["error"] = f"OECD SDMX unreachable: {str(e)[:200]}"
        ch["verdict_rule"] = cfg["thresholds"]
        return ch
    pts_by_year = {}
    unit_seen = set()
    status_by_year = {}
    try:
        rd = csv.DictReader(io.StringIO(text))
        for r in rd:
            if (r.get("MEASURE") == flt["MEASURE"]
                    and r.get("REF_AREA") == flt["REF_AREA"]
                    and r.get("ACTIVITY") == flt["ACTIVITY"]
                    and r.get("SIZE_CLASS") == flt["SIZE_CLASS"]
                    and r.get("FREQ") == flt["FREQ"]):
                try:
                    y = int(r["TIME_PERIOD"])
                    v = float(r["OBS_VALUE"])
                except (TypeError, ValueError, KeyError):
                    continue
                pts_by_year[y] = v
                status_by_year[y] = r.get("OBS_STATUS", "")
                unit_seen.add(r.get("UNIT_MEASURE", ""))
    except Exception as e:  # noqa: BLE001
        ch["error"] = f"OECD CSV parse failed: {str(e)[:200]}"
        ch["provenance"] = prov
        return ch
    years = sorted(pts_by_year)
    if len(years) < cfg["quality_gates"]["min_observations"]:
        ch["error"] = f"OECD adoption series too short ({len(years)} obs)"
        ch["provenance"] = prov
        return ch
    m8a = pts_by_year[years[-1]]
    y1, y0 = years[-1], years[-2]
    gap = y1 - y0
    if gap > 5:
        ch["error"] = f"observation gap {gap} yr > 5 (A1-7 rule) - pending_data"
        ch["provenance"] = prov
        return ch
    m8b = (pts_by_year[y1] - pts_by_year[y0]) / gap
    if m8a >= 30.0 and m8b >= 3.0:
        status = "green"
    elif (15.0 <= m8a < 30.0) or (1.0 <= m8b < 3.0):
        status = "yellow"
    else:
        status = "red"
    ys = years
    vs = [pts_by_year[y] for y in ys]
    _, _, sigma, _, _ = ols(ys, vs)
    ch.update({
        "status": status,
        "metrics": {
            "M8a_adoption_pct": round(m8a, 3),
            "M8b_adoption_growth_pp_per_yr": round(m8b, 3),
            "series_years": [ys[0], ys[-1]],
            "series_points": len(ys),
        },
        "intermediates": {
            "obs_by_year": {str(y): round(pts_by_year[y], 3) for y in ys},
            "obs_status_by_year": {str(y): status_by_year[y] for y in ys},
            "obs_status_note": route["obs_status_note"],
            "unit_measure_observed": sorted(unit_seen),
            "filter": flt,
            "m8b_window": [y0, y1],
            "sigma_residual_pp": round(sigma, 3),
        },
        "verdict_rule": cfg["thresholds"],
        "provenance": prov,
        "excluded_background": cfg["excluded_background"],
        "numeric_z": {
            "margin_to_red": round(m8a - cfg["red_anchor_numeric"], 3),
            "sigma": round(sigma, 3),
            "z": round((m8a - cfg["red_anchor_numeric"]) / sigma, 4) if sigma > 0 else None,
            "sign_note": "unlock channel: red boundary below metric; larger z = stronger unlock",
        },
    })
    return ch


# ----------------------------------------------------------------------------
# Synthesis (preregistered state machine, separate pressure/unlock) - unchanged
# ----------------------------------------------------------------------------

def synthesize(channels):
    prereg_status = {ch["id"]: ch["status"] for ch in channels}
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

    z_pressure = {}
    z_unlock = {}
    for ch in channels:
        nz = ch.get("numeric_z")
        if not nz or nz.get("z") is None or ch["status"] == "pending_data":
            continue
        if ch["id"] in pressure_ids:
            z_pressure[ch["id"]] = nz["z"]
        elif ch["id"] in unlock_ids:
            z_unlock[ch["id"]] = nz["z"]
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
            "z_excluded": {
                "C3": "two-metric channel, no preregistered single-z rule",
                "C7": "no preregistered z-program (A1 unchanged)",
                "C6": "duration-count metric, no observable sigma",
            },
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
    with open(A1_JSON, "r", encoding="utf-8") as f:
        a1 = json.load(f)
    with open(A2_JSON, "r", encoding="utf-8") as f:
        a2 = json.load(f)
    # A2 implementation guard (A2 §4): frozen formula string must match code
    a2_formula = a2["amendments"]["C1_metric_definition"]["corrected_formula"]
    assert a2_formula == "M1 = 1.5 - T_12m", f"A2 formula mismatch: {a2_formula!r}"
    channels = [
        channel_C1(prereg, a1), channel_C2(prereg, a1), channel_C3(prereg, a1),
        channel_C4(prereg, a1), channel_C5(prereg), channel_C6(prereg, a1),
        channel_C7(prereg), channel_C8(prereg, a1),
    ]
    synthesis = synthesize(channels)
    out = {
        "pipeline": {
            "name": "CDD-ECS C-series channel pipeline",
            "version": "v3.0",
            "run_utc": utcnow_iso(),
            "preregistration": {
                "document": PREREG_MD,
                "md_sha256": sha256_file(PREREG_MD),
                "machine_readable": PREREG_JSON,
                "json_sha256": sha256_file(PREREG_JSON),
                "frozen_before_data_contact": True,
                "amendment_a1": {
                    "document": A1_MD,
                    "md_sha256": sha256_file(A1_MD),
                    "machine_readable": A1_JSON,
                    "json_sha256": sha256_file(A1_JSON),
                    "threshold_changes": a1["meta"]["threshold_changes"],
                    "registered_before_v2_metric_computation": True,
                },
                "amendment_a2": {
                    "document": A2_MD,
                    "md_sha256": sha256_file(A2_MD),
                    "machine_readable": A2_JSON,
                    "json_sha256": sha256_file(A2_JSON),
                    "threshold_changes": a2["meta"]["threshold_changes"],
                    "registered_before_v3_metric_computation": True,
                    "implementation_guard": f"asserted corrected_formula == {a2_formula!r} before C1 computation",
                },
                "event_order": a2["meta"]["event_order_disclosure"],
                "criteria_read_order": "v1.0 JSON thresholds (verbatim) -> A1 JSON routes/constants -> A2 JSON C1 definition",
            },
            "amendments_applied": {
                "A1-1": "C1 baseline offset derived at runtime from HadCRUT5 [F]",
                "A1-2": "C1 cross-source trailing mean (sum/12) [F]",
                "A1-3": "C7 LCOE unit USD/kWh, both units reported [F]",
                "A1-4": "C4 NCEI FTP NetCDF route, h5py [R]",
                "A1-5": "C4 partial decidability, literal OR semantics [F]",
                "A1-6": "C3 IMBIE source promotion, 360 Gt/mm SLR conversion [S]",
                "A1-7": "C8 OECD SDMX route with frozen filters [R]",
                "A1-8": "C2/C6 pending_data with route registration [R]",
                "A2-1": "C1 margin form M1 = 1.5 - T_12m (sign clarification; thresholds verbatim) [F]",
                "A2-2": "round13 review report Z_gap prose erratum registered (no value change) [F]",
            },
            "cache_dir": CACHE_DIR,
            "regeneration": "python H:\\cdd_lean4\\scripts\\cdd_ecs_channel_pipeline_v3.py",
            "v1_snapshot_frozen": "H:\\cdd_ecs_channel_pipeline_results_v1.json (not overwritten)",
            "v2_snapshot_frozen": ("H:\\cdd_ecs_channel_pipeline_results_v2.json (not overwritten; "
                                   "C1 verdict + downstream superseded by this v3 run per A2 §0.5)"),
        },
        "channels": {ch["id"]: ch for ch in channels},
        "synthesis": synthesis,
        "notes": [
            "All thresholds executed verbatim from frozen v1.0 preregistration JSON; "
            "A1 supplies routes/constants, A2 supplies the C1 margin-form definition "
            "(threshold_changes = 0 in both).",
            "A2-1 invariant: |M1_v2| = |M1_v3| (pure sign flip of the same T_12m); "
            "z_C1 same magnitude, flipped sign.",
            "pending_data channels are excluded from synthesis and reported explicitly.",
            "C5 M5a is a literature snapshot count (PB2023=6), not a recomputed observation.",
            "C8 excluded_background (NBER task-level effects) is not a mechanical criterion.",
            "C3/C4 data files adopted from probe-phase downloads carry honest provenance "
            "registration (sha256 + URL); probes computed no metrics before A1.",
            "No manual numeric values entered anywhere in this pipeline.",
        ],
    }
    with open(OUT_JSON, "w", encoding="utf-8") as f:
        json.dump(out, f, indent=2, ensure_ascii=False)
    print(f"snapshot written: {OUT_JSON}")
    print(f"prereg v1.0 md  sha256: {out['pipeline']['preregistration']['md_sha256']}")
    print(f"prereg v1.0 json sha256: {out['pipeline']['preregistration']['json_sha256']}")
    a1b = out["pipeline"]["preregistration"]["amendment_a1"]
    print(f"amendment A1 md  sha256: {a1b['md_sha256']}")
    print(f"amendment A1 json sha256: {a1b['json_sha256']}")
    a2b = out["pipeline"]["preregistration"]["amendment_a2"]
    print(f"amendment A2 md  sha256: {a2b['md_sha256']}")
    print(f"amendment A2 json sha256: {a2b['json_sha256']}")
    print()
    for ch in channels:
        m = ch.get("metrics", {})
        mv = " ".join(f"{k}={v}" for k, v in (m or {}).items())
        print(f"  {ch['id']:>3} {ch['name']:<22} {ch['status']:<14} {mv[:100]}")
        if "error" in ch:
            print(f"      err: {ch['error'][:110]}")
    print()
    s = synthesis
    print(f"  pressure: red={s['pressure_index']['red']} yellow={s['pressure_index']['yellow']}")
    print(f"  unlock:   red={s['unlock_index']['red']} yellow={s['unlock_index']['yellow']}")
    print(f"  state:    {s['state_machine']} (reported={s['global_state_reported']})")
    print(f"  pending:  {', '.join(s['pending_channels']) or 'none'}")
    aux = s["stouffer_auxiliary"]
    print(f"  Z_pressure={aux['Z_pressure']} Z_unlock={aux['Z_unlock']} Z_gap={aux['Z_gap']} "
          f"(k={aux['k_pressure']}+{aux['k_unlock']})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
