#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""CDD-ECS pipeline v5.0 (channel layer v4 verbatim re-run + claim layer v2.0 first computation).

Discipline:
  - Channel layer: the v4.0 module is imported and re-run VERBATIM (same frozen
    v1.0 thresholds, A1-A3 amendments, cache-first data, verdict rules and
    state machine). Channel z_level values, verdicts, synthesis and the state
    machine are produced by the same code on the same cached data.
  - Claim layer: FIRST computation under claim-layer preregistration v2.0
    (criteria frozen before data contact). All statistics, thresholds,
    confirmation rules and anti-inflation guards are executed verbatim from
    the frozen v2 JSON. Implementation guards assert the six frozen formula
    strings, cap_c = 5.0 and the z_traj s-sign table byte-exact BEFORE any
    claim-layer computation; any mismatch -> abort.
  - Event order (v2 sec 0.2): v1 freeze -> v1 run -> probes -> A1 -> v2 run ->
    C1 sign review -> A2 -> v3 run -> Z_gap direction review -> A3 -> v4 run
    -> 6sigma framework v1.0-draft -> v2 claim layer preregistration ->
    THIS v5 run (claim layer first computation, BASELINE SNAPSHOT 0).
  - Baseline snapshot 0: this first claim-layer reading enters NO confirmation
    count; all confirmations count from post-freeze annual snapshots
    (2027-09-30 onward). Intersection semantics, optional stopping forbidden.
  - Internal consistency guards: every claim-layer re-derivation must
    reproduce the channel-layer intermediates within their registered
    rounding (C1 sigma 4dp, C3/C4 trend t 2dp, C7 beta 4dp, C8 sigma 3dp),
    and ols_full must reproduce v4.ols exactly on identical inputs.
    Any mismatch -> abort (implementation failure registered).
  - Snapshot: H:\\cdd_ecs_channel_pipeline_results_v5.json (new file;
    v1-v4 snapshots frozen, not overwritten).
  - Download failure -> component 'pending_data'; manual numeric entry FORBIDDEN.
"""
import json
import math
import os
import sys

_SCRIPTS_DIR = os.path.dirname(os.path.abspath(__file__))
if _SCRIPTS_DIR not in sys.path:
    sys.path.insert(0, _SCRIPTS_DIR)

import cdd_ecs_channel_pipeline_v4 as v4  # noqa: E402  (channel layer, verbatim)

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")

PREREG_V2_MD = r"H:\cdd_ecs_claim_layer_preregistration_v2_20260830.md"
PREREG_V2_JSON = r"H:\cdd_ecs_claim_layer_preregistration_v2_20260830.json"
OUT_JSON = r"H:\cdd_ecs_channel_pipeline_results_v5.json"

# Frozen constants (prereg v2 sec 2.4 / sec 6; asserted against the v2 JSON)
CAP_C = 5.0
SQ10 = math.sqrt(10.0)
SQ2 = math.sqrt(2.0)
SIX_SIGMA_Z = 6.0

# Frozen z_traj direction signs (prereg v2 sec 2.2 table; asserted against JSON)
S_TRAJ = {
    "C1": -1.0,      # warming = danger
    "C3-GIS": 1.0,   # mass loss (declining series) = danger
    "C3-AIS": 1.0,
    "C4": -1.0,      # OHC rise = danger
    "C5": -1.0,      # CO2 rise = danger
    "C7": -1.0,      # beta >= 0 (no learning) = danger
    "C8": 1.0,       # adoption rise = safe
}

# Frozen family division (prereg v2 sec 3.1, guard (j))
FAMILY_OF = {
    "C1": "climate_carbon", "C3": "climate_carbon", "C4": "climate_carbon",
    "C5": "climate_carbon", "C6": "social", "C7": "energy", "C8": "information",
}

# Frozen tau target anchors (prereg v2 sec 4)
TAU_THETA = {"C1": 0.0, "C5": 85.0, "C8": 30.0}


def cap(z):
    """Contribution cap guard (a): sign(z) * min(|z|, c), c = 5.0 frozen."""
    return math.copysign(min(abs(z), CAP_C), z)


def ols_full(xs, ys):
    """OLS y = a + b*x returning slope, SE(b), t, residual SD, sxx, n.

    Core identical to v4.ols (cross-asserted at call sites); adds SE(b) for
    the C7 estimation-sigma program and the tau SE formula.
    """
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
    s2 = sum(r * r for r in resid) / dof
    s = math.sqrt(s2)
    se_b = s / math.sqrt(sxx)
    t = b / se_b
    return {"b": b, "a": a, "sigma": s, "se_b": se_b, "t": t, "sxx": sxx, "n": n}


def family_stouffer(zmap):
    """Guard (j): within-family Stouffer -> cross-family Stouffer.

    Additionally reports family means as the conservative bound under perfect
    within-family correlation (prereg v2 sec 3.1).
    """
    fams = {}
    for ch, z in zmap.items():
        fams.setdefault(FAMILY_OF[ch], []).append(z)
    within = {f: sum(v) / math.sqrt(len(v)) for f, v in fams.items()}
    cross = sum(within.values()) / math.sqrt(len(within)) if within else None
    means = {f: sum(v) / len(v) for f, v in fams.items()}
    bound = (sum(means.values()) / math.sqrt(len(means))) if means else None
    return {
        "within_family": {f: round(z, 4) for f, z in within.items()},
        "cross_family": None if cross is None else round(cross, 4),
        "family_means": {f: round(z, 4) for f, z in means.items()},
        "perfect_correlation_bound": None if bound is None else round(bound, 4),
        "family_sizes": {f: len(v) for f, v in fams.items()},
    }


def z_traj_of(s, t):
    """Frozen formula: z_traj_i = s_i * t_i / sqrt(10)."""
    return s * t / SQ10


# ----------------------------------------------------------------------------
# Claim-layer series re-derivations (same cache, same v4 parsers)
# ----------------------------------------------------------------------------

def claim_fit_C1(prereg):
    cfg = prereg["channels"]["C1_temperature"]
    text, prov = v4.fetch(cfg["primary_source"]["url"], "C1_gistemp_monthly.csv")
    rows = v4.parse_gistemp_monthly(text)
    ann = {}
    for y0, _m, val in rows:
        ann.setdefault(y0, []).append(val)
    years = sorted(ann)
    ann_mean = [sum(ann[y]) / len(ann[y]) for y in years]
    xs, ys = years[-30:], ann_mean[-30:]
    fit = ols_full(xs, ys)
    b4, _a4, s4, t4, _n4 = v4.ols(xs, ys)
    assert abs(fit["t"] - t4) < 1e-9 and abs(fit["b"] - b4) < 1e-12 \
        and abs(fit["sigma"] - s4) < 1e-12, "C1 ols_full != v4.ols"
    return fit, {"window": [xs[0], xs[-1]], "n": fit["n"],
                 "series_years": [years[0], years[-1]],
                 "provenance": {k: prov[k] for k in ("url", "raw_sha256", "cache_hit")}},


def claim_fit_C3(a1):
    promo = a1["amendments"]["C3_source_promotion"]
    specs = {
        "greenland": (promo["greenland"], "C3_imbie_greenland_2020_02_28.xlsx"),
        "antarctica": (promo["antarctica"], "C3_imbie_2018_07_23.xlsx"),
    }
    out = {}
    for name, (spec, cache_key) in specs.items():
        path, prov = v4.fetch_binary(spec["url"], cache_key, timeout=300)
        pts, _hdr = v4._parse_imbie_xlsx(path, spec["sheet"], spec["column"])
        t_last = max(p[0] for p in pts)
        win = [p for p in pts if p[0] >= t_last - 10.0]
        fit = ols_full([p[0] for p in win], [p[1] for p in win])
        out[name] = {"fit": fit, "window": [round(t_last - 10.0, 2), round(t_last, 2)],
                     "n": fit["n"],
                     "provenance": {k: prov[k] for k in ("url", "raw_sha256", "cache_hit")}}
    return out


def claim_fit_C4(a1):
    route = a1["amendments"]["C4_route"]
    path, prov = v4.fetch_binary(route["url"], "C4_ncei_ohc_0-2000_yearly.nc", timeout=600)
    import h5py
    with h5py.File(path, "r") as hf:
        time_v = [float(t) for t in hf["time"][()]]
        ohc = [float(x) for x in hf[route["variable"]][()]]
    years = [1955.0 + t / 12.0 for t in time_v]
    t_max = years[-1]
    win = [(x, v) for x, v in zip(years, ohc) if x >= t_max - 10.0]
    fit = ols_full([x for x, _ in win], [v for _, v in win])
    return fit, {"window": [round(t_max - 10.0, 2), round(t_max, 2)], "n": fit["n"],
                 "provenance": {k: prov[k] for k in ("url", "raw_sha256", "cache_hit")}}


def claim_fit_C5(prereg):
    cfg = prereg["channels"]["C5_biogeochemical"]
    text, prov = v4.fetch(cfg["primary_source"]["url"], "C5_noaa_co2_annmean_gl.txt")
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
    years = [p[0] for p in pts]
    vals = [p[1] for p in pts]
    xs, ys = years[-30:], vals[-30:]
    fit = ols_full(xs, ys)
    b4, _a4, s4, t4, _n4 = v4.ols(xs, ys)
    assert abs(fit["t"] - t4) < 1e-9 and abs(fit["b"] - b4) < 1e-12 \
        and abs(fit["sigma"] - s4) < 1e-12, "C5 ols_full != v4.ols"
    return fit, {"window": [xs[0], xs[-1]], "n": fit["n"],
                 "series_years": [years[0], years[-1]],
                 "provenance": {k: prov[k] for k in ("url", "raw_sha256", "cache_hit")}}


def claim_fit_C7(prereg):
    lcoe_pts = cap_pts = None
    for slug, col in (("levelized-cost-of-energy", "Solar photovoltaic"),
                      ("solar-lcoe", None), ("solar-pv-lcoe", None)):
        try:
            t, _p = v4.fetch(f"https://ourworldindata.org/grapher/{slug}.csv",
                             f"C7_owid_{slug}.csv")
            pts = v4._parse_owid_world(t, col)
            if len(pts) >= 8:
                lcoe_pts = pts
                break
        except Exception:  # noqa: BLE001
            continue
    for slug in ("cumulative-installed-solar-pv-capacity", "installed-solar-pv-capacity",
                 "cumulative-solar-pv-capacity"):
        try:
            t, _p = v4.fetch(f"https://ourworldindata.org/grapher/{slug}.csv",
                             f"C7_owid_{slug}.csv")
            pts = v4._parse_owid_world(t)
            if len(pts) >= 8:
                cap_pts = pts
                break
        except Exception:  # noqa: BLE001
            continue
    if lcoe_pts is None or cap_pts is None:
        raise RuntimeError("OWID solar LCOE or cumulative-capacity series not reachable")
    cap_map = dict(cap_pts)
    joined = [(y, v, cap_map[y]) for y, v in lcoe_pts
              if y in cap_map and v > 0 and cap_map[y] > 0]
    xs = [math.log(c) for _, _, c in joined]
    ys = [math.log(v) for _, v, _ in joined]
    fit = ols_full(xs, ys)
    return fit, {"n": fit["n"], "joined_points": len(joined),
                 "span": [joined[0][0], joined[-1][0]]}


def claim_fit_C8(prereg, a1):
    route = a1["amendments"]["C8_route"]
    flt = route["filters"]
    text = None
    prov = None
    try:
        text, prov = v4.fetch(route["url"], "C8_oecd_ictb.csv", timeout=900)
    except Exception as e:  # noqa: BLE001
        probe_path = os.path.join(v4.CACHE_DIR, "C8_oecd_ictb_probe.csv")
        if os.path.exists(probe_path):
            with open(probe_path, "r", encoding="utf-8", errors="replace") as f:
                text = f.read()
            prov = {"url": route["url"], "fallback_artifact": probe_path,
                    "raw_sha256": v4.sha256_file(probe_path),
                    "cache_hit": True,
                    "note": "same A1-registered URL + probe fallback as the channel layer"}
        else:
            raise RuntimeError(f"OECD SDMX unreachable: {str(e)[:200]}")
    import csv
    import io
    pts_by_year = {}
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
    years = sorted(pts_by_year)
    if not years:
        raise RuntimeError("OECD adoption series empty under frozen filters")
    vs = [pts_by_year[y] for y in years]
    fit = ols_full(years, vs)
    return fit, {"n_obs": len(years), "series_years": [years[0], years[-1]],
                 "obs_by_year": {str(y): pts_by_year[y] for y in years}}


# ----------------------------------------------------------------------------
# main
# ----------------------------------------------------------------------------

def main():
    # ---- load frozen configurations (v1.0 + A1 + A2 + A3 via the v4 module) ----
    with open(v4.PREREG_JSON, "r", encoding="utf-8") as f:
        prereg = json.load(f)
    with open(v4.A1_JSON, "r", encoding="utf-8") as f:
        a1 = json.load(f)
    with open(v4.A2_JSON, "r", encoding="utf-8") as f:
        a2 = json.load(f)
    a2_formula = a2["amendments"]["C1_metric_definition"]["corrected_formula"]
    assert a2_formula == "M1 = 1.5 - T_12m", f"A2 formula mismatch: {a2_formula!r}"
    with open(v4.A3_JSON, "r", encoding="utf-8") as f:
        a3 = json.load(f)
    a3_formula = a3["amendments"]["Z_gap_definition"]["corrected_formula"]
    assert a3_formula == "Z_gap = Z_unlock + Z_pressure", f"A3 formula mismatch: {a3_formula!r}"

    with open(PREREG_V2_JSON, "r", encoding="utf-8") as f:
        v2 = json.load(f)

    # ---- implementation guards (prereg v2 sec 6): frozen formula strings ----
    fs = v2["implementation_guards"]["formula_strings"]
    assert fs[0] == "z_traj_i = s_i * t_i / sqrt(10)", f"guard 0 mismatch: {fs[0]!r}"
    assert fs[1] == "cap_c = 5.0", f"guard 1 mismatch: {fs[1]!r}"
    assert fs[2] == "Z_R = (Z_unlock + Z_pressure) / sqrt(2)", f"guard 2 mismatch: {fs[2]!r}"
    assert fs[3] == "Z_L1 = sqrt(sum(t_i^2)) / sqrt(10)", f"guard 3 mismatch: {fs[3]!r}"
    assert fs[4] == "sigma_LR_pp = 100 * ln(2) * (1 - LR) * SE(beta)", f"guard 4 mismatch: {fs[4]!r}"
    assert fs[5] == "tau_i = (theta_i - M_i) / b_i", f"guard 5 mismatch: {fs[5]!r}"
    fs2 = v2["implementation_guards"]["secondary_formula_strings"]
    assert fs2[0] == "z_level_C7 = (LR_pct - 12) / sigma_LR_pp", f"secondary 0 mismatch: {fs2[0]!r}"
    assert fs2[1] == "Z_R_traj = (Z_unlock_traj + Z_pressure_traj) / sqrt(2)", f"secondary 1 mismatch: {fs2[1]!r}"
    assert fs2[2] == "Z_T = (Z_Tunlock + Z_Tpressure) / sqrt(2)", f"secondary 2 mismatch: {fs2[2]!r}"
    assert fs2[3] == "z_entering_synthesis = sign(z) * min(|z|, c)", f"secondary 3 mismatch: {fs2[3]!r}"
    assert fs2[4] == "sigma_tau = (1/|b|) * sqrt(sigma_M^2 + tau^2 * SE(b)^2)", f"secondary 4 mismatch: {fs2[4]!r}"
    assert fs2[5] == "z_C3 = min(z_GIS, z_AIS)", f"secondary 5 mismatch: {fs2[5]!r}"
    assert v2["guards"]["cap_c"]["c"] == CAP_C, "cap_c value mismatch"
    fw = v2["sigma_programs"]["z_traj"]["frozen_windows"]
    for k, s in S_TRAJ.items():
        assert fw[k]["s"] == s, f"s-sign mismatch for {k}: JSON {fw[k]['s']} vs code {s}"

    run_utc = v4.utcnow_iso()

    # ---- channel layer: v4 verbatim re-run ----
    channels = [
        v4.channel_C1(prereg, a1), v4.channel_C2(prereg, a1), v4.channel_C3(prereg, a1),
        v4.channel_C4(prereg, a1), v4.channel_C5(prereg), v4.channel_C6(prereg, a1),
        v4.channel_C7(prereg), v4.channel_C8(prereg, a1),
    ]
    synthesis = v4.synthesize(channels)
    ch = {c["id"]: c for c in channels}

    # ---- claim layer: series re-derivations (fail -> pending, no crash) ----
    errors = {}
    fits = {}
    meta_notes = {}
    try:
        fits["C1"], meta_notes["C1"] = claim_fit_C1(prereg)
    except Exception as e:  # noqa: BLE001
        errors["C1"] = str(e)[:300]
    try:
        fits["C3"] = claim_fit_C3(a1)
    except Exception as e:  # noqa: BLE001
        errors["C3"] = str(e)[:300]
    try:
        fits["C4"], meta_notes["C4"] = claim_fit_C4(a1)
    except Exception as e:  # noqa: BLE001
        errors["C4"] = str(e)[:300]
    try:
        fits["C5"], meta_notes["C5"] = claim_fit_C5(prereg)
    except Exception as e:  # noqa: BLE001
        errors["C5"] = str(e)[:300]
    try:
        fits["C7"], meta_notes["C7"] = claim_fit_C7(prereg)
    except Exception as e:  # noqa: BLE101
        errors["C7"] = str(e)[:300]
    try:
        fits["C8"], meta_notes["C8"] = claim_fit_C8(prereg, a1)
    except Exception as e:  # noqa: BLE001
        errors["C8"] = str(e)[:300]

    # ---- internal consistency guards (claim re-derivation == channel layer) ----
    checks = {}
    if "C1" in fits and ch["C1"].get("intermediates"):
        exp = ch["C1"]["intermediates"]["sigma_annual_residual_C"]
        got = round(fits["C1"]["sigma"], 4)
        checks["C1_sigma"] = {"expected": exp, "got": got, "pass": exp == got}
    if "C3" in fits and ch["C3"].get("intermediates"):
        for name in ("greenland", "antarctica"):
            exp = ch["C3"]["intermediates"][name]["ols_t_stat"]
            got = round(fits["C3"][name]["fit"]["t"], 2)
            checks[f"C3_{name}_t"] = {"expected": exp, "got": got, "pass": exp == got}
    if "C4" in fits and ch["C4"].get("intermediates"):
        exp = ch["C4"]["intermediates"]["ols_t_stat"]
        got = round(fits["C4"]["t"], 2)
        checks["C4_t"] = {"expected": exp, "got": got, "pass": exp == got}
    if "C5" in fits and ch["C5"].get("intermediates"):
        exp = ch["C5"]["intermediates"]["sigma_annual_residual_ppm"]
        got = round(fits["C5"]["sigma"], 3)
        checks["C5_sigma"] = {"expected": exp, "got": got, "pass": exp == got}
    if "C7" in fits and ch["C7"].get("intermediates"):
        exp = ch["C7"]["intermediates"]["loglog_slope_beta"]
        got = round(fits["C7"]["b"], 4)
        checks["C7_beta"] = {"expected": exp, "got": got, "pass": exp == got}
        exp_n = ch["C7"]["intermediates"]["joined_points"]
        checks["C7_joined_points"] = {"expected": exp_n,
                                      "got": meta_notes["C7"]["joined_points"],
                                      "pass": exp_n == meta_notes["C7"]["joined_points"]}
    if "C8" in fits and ch["C8"].get("intermediates"):
        exp = ch["C8"]["intermediates"]["sigma_residual_pp"]
        got = round(fits["C8"]["sigma"], 3)
        checks["C8_sigma"] = {"expected": exp, "got": got, "pass": exp == got}
        exp_obs = ch["C8"]["intermediates"]["obs_by_year"]
        got_obs = {k: round(v, 3) for k, v in meta_notes["C8"]["obs_by_year"].items()}
        checks["C8_obs_by_year"] = {"pass": exp_obs == got_obs}
    failed = [k for k, c in checks.items() if not c["pass"]]
    assert not failed, f"internal consistency guards failed: {failed}"

    # ---- z_traj components (frozen windows, s signs, 1/sqrt(10) reduction) ----
    zt = {}
    traj_detail = {}
    if "C1" in fits:
        zt["C1"] = z_traj_of(S_TRAJ["C1"], fits["C1"]["t"])
        traj_detail["C1"] = {"t": round(fits["C1"]["t"], 2), "s": S_TRAJ["C1"],
                             "window": meta_notes["C1"]["window"], "n": meta_notes["C1"]["n"]}
    if "C3" in fits:
        zg = z_traj_of(S_TRAJ["C3-GIS"], fits["C3"]["greenland"]["fit"]["t"])
        za = z_traj_of(S_TRAJ["C3-AIS"], fits["C3"]["antarctica"]["fit"]["t"])
        zt["C3-GIS"] = zg
        zt["C3-AIS"] = za
        zt["C3"] = min(zg, za)  # frozen fold: worst basin
        traj_detail["C3-GIS"] = {"t": round(fits["C3"]["greenland"]["fit"]["t"], 2),
                                 "s": S_TRAJ["C3-GIS"],
                                 "window": fits["C3"]["greenland"]["window"],
                                 "n": fits["C3"]["greenland"]["n"]}
        traj_detail["C3-AIS"] = {"t": round(fits["C3"]["antarctica"]["fit"]["t"], 2),
                                 "s": S_TRAJ["C3-AIS"],
                                 "window": fits["C3"]["antarctica"]["window"],
                                 "n": fits["C3"]["antarctica"]["n"]}
        traj_detail["C3-fold"] = {"rule": "z_C3 = min(z_GIS, z_AIS)"}
    if "C4" in fits:
        zt["C4"] = z_traj_of(S_TRAJ["C4"], fits["C4"]["t"])
        traj_detail["C4"] = {"t": round(fits["C4"]["t"], 2), "s": S_TRAJ["C4"],
                             "window": meta_notes["C4"]["window"], "n": meta_notes["C4"]["n"]}
    if "C5" in fits:
        zt["C5"] = z_traj_of(S_TRAJ["C5"], fits["C5"]["t"])
        traj_detail["C5"] = {"t": round(fits["C5"]["t"], 2), "s": S_TRAJ["C5"],
                             "window": meta_notes["C5"]["window"], "n": meta_notes["C5"]["n"]}
    if "C7" in fits:
        zt["C7"] = z_traj_of(S_TRAJ["C7"], fits["C7"]["t"])
        traj_detail["C7"] = {"t": round(fits["C7"]["t"], 2), "s": S_TRAJ["C7"],
                             "window": "full linkage (log-log slope statistic)",
                             "n": meta_notes["C7"]["n"]}
    if "C8" in fits:
        zt["C8"] = z_traj_of(S_TRAJ["C8"], fits["C8"]["t"])
        traj_detail["C8"] = {"t": round(fits["C8"]["t"], 2), "s": S_TRAJ["C8"],
                             "window": "full series", "n": meta_notes["C8"]["n_obs"]}
    zt_capped = {k: cap(z) for k, z in zt.items()}

    # ---- C7 z_level (estimation-sigma program, frozen) ----
    c7_level = None
    if "C7" in fits:
        beta = fits["C7"]["b"]
        se_beta = fits["C7"]["se_b"]
        t_beta = fits["C7"]["t"]
        lr = 1.0 - 2.0 ** beta
        # frozen: sigma_LR_pp = 100 * ln(2) * (1 - LR) * SE(beta)
        sigma_lr_pp = 100.0 * math.log(2.0) * (1.0 - lr) * se_beta
        lr_pct = lr * 100.0
        # frozen: z_level_C7 = (LR_pct - 12) / sigma_LR_pp
        z_level_c7 = (lr_pct - 12.0) / sigma_lr_pp
        c7_level = {
            "beta": round(beta, 4), "SE_beta": round(se_beta, 6),
            "t_beta": round(t_beta, 2), "LR": round(lr, 6), "LR_pct": round(lr_pct, 2),
            "sigma_LR_pp": round(sigma_lr_pp, 4),
            "z_level_C7": round(z_level_c7, 4),
            "z_level_C7_capped": cap(z_level_c7),
            "sigma_program": "estimation-uncertainty propagation (delta method on LR = 1 - 2^beta); "
                             "distinct from series-residual programs, explicitly annotated",
        }

    # ---- L1: pressure trend reality ----
    l1 = None
    if all(k in fits for k in ("C1", "C3", "C4", "C5")):
        t_l1 = {
            "C1": fits["C1"]["t"],
            "C3-GIS": fits["C3"]["greenland"]["fit"]["t"],
            "C3-AIS": fits["C3"]["antarctica"]["fit"]["t"],
            "C4": fits["C4"]["t"],
            "C5": fits["C5"]["t"],
        }
        # frozen: Z_L1 = sqrt(sum(t_i^2)) / sqrt(10)
        z_l1 = math.sqrt(sum(t * t for t in t_l1.values())) / SQ10
        chi2 = sum((t / SQ10) ** 2 for t in t_l1.values())
        l1 = {
            "roster": ["C1", "C3-GIS", "C3-AIS", "C4", "C5"],
            "t_values": {k: round(t, 2) for k, t in t_l1.items()},
            "Z_L1": round(z_l1, 4),
            "chi2_reading": round(chi2, 2),
            "chi2_df": len(t_l1),
            "chi2_note": "sum((t_i/sqrt(10))^2) is chi-square-type under H0 and independence; "
                         "the sqrt form is the project-registered reading; both reported",
            "reduction": "1/sqrt(10) autocorrelation conservative, uniform",
            "threshold": SIX_SIGMA_Z,
            "threshold_met": z_l1 >= SIX_SIGMA_Z,
            "confirmation": "decidable from current data (in-sample history); annual snapshot "
                            "recheck (cancellation system); baseline snapshot 0 not counted",
        }

    # ---- L2a: energy learning curve ----
    l2a = None
    if "C7" in fits:
        # frozen: z_L2a = -t_beta / sqrt(10)
        z_l2a = -fits["C7"]["t"] / SQ10
        l2a = {
            "t_beta": round(fits["C7"]["t"], 2),
            "SE_beta": round(fits["C7"]["se_b"], 6),
            "z_L2a": round(z_l2a, 4),
            "cap_exempt": "single-channel proposition; uncapped value reported",
            "threshold": SIX_SIGMA_Z,
            "threshold_met": z_l2a >= SIX_SIGMA_Z,
            "confirmation": "decidable from current data; annual recheck (learning stall -> cancellation)",
        }

    # ---- L2b: information adoption trend ----
    l2b = None
    if "C8" in fits:
        n_obs = meta_notes["C8"]["n_obs"]
        if n_obs < 8:
            l2b = {"status": "series_short", "n_obs": n_obs,
                   "note": "decidability gate (>= 8 annual observations) not met; "
                           "undecidable, not a failure"}
        else:
            z_l2b = fits["C8"]["t"] / SQ10
            l2b = {
                "status": "decidable",
                "n_obs": n_obs,
                "t_adoption": round(fits["C8"]["t"], 2),
                "z_L2b": round(z_l2b, 4),
                "cap_exempt": "single-channel proposition; uncapped value reported",
                "threshold": SIX_SIGMA_Z,
                "threshold_met": z_l2b >= SIX_SIGMA_Z,
                "confirmation": "single decidable snapshot; annual recheck",
            }

    # ---- L3: R direction (level + trajectory composites) ----
    def ch_z(cid):
        nz = ch[cid].get("numeric_z")
        return None if (not nz or nz.get("z") is None) else nz["z"]

    z_lvl = {cid: ch_z(cid) for cid in ("C1", "C4", "C5", "C8")}
    l3 = {}

    # L3-level(v1-roster): pressure {C1, C4, C5}, unlock {C8}; v1.0 z_level verbatim
    if all(z_lvl[c] is not None for c in ("C1", "C4", "C5", "C8")):
        zp = {"C1": cap(z_lvl["C1"]), "C4": cap(z_lvl["C4"]), "C5": cap(z_lvl["C5"])}
        zu = {"C8": cap(z_lvl["C8"])}
        fp = family_stouffer(zp)
        fu = family_stouffer(zu)
        # frozen: Z_R = (Z_unlock + Z_pressure) / sqrt(2)
        z_r = (fu["cross_family"] + fp["cross_family"]) / SQ2
        z_r_bound = (fu["perfect_correlation_bound"] + fp["perfect_correlation_bound"]) / SQ2
        l3["level_v1_roster"] = {
            "pressure_roster": ["C1", "C4", "C5"], "unlock_roster": ["C8"],
            "z_entering": {**zp, **zu},
            "z_uncapped": {"C1": z_lvl["C1"], "C4": z_lvl["C4"], "C5": z_lvl["C5"],
                           "C8": z_lvl["C8"]},
            "Z_pressure": fp["cross_family"], "Z_unlock": fu["cross_family"],
            "Z_R": round(z_r, 4),
            "perfect_correlation_bound": round(z_r_bound, 4),
            "family_detail": {"pressure": fp, "unlock": fu},
            "sigma_program": "v1.0 z_level verbatim (continuity reading vs v4; "
                             "trend-blindness defect registered A3-2; retained as control)",
            "threshold": SIX_SIGMA_Z,
            "threshold_met": z_r >= SIX_SIGMA_Z,
            "confirmation": ">= 3 consecutive post-freeze annual snapshots (from 2027-09-30) "
                            "all >= 6; baseline snapshot 0 not counted",
        }

    # L3-level(v2-roster): pressure {C1, C4, C5}, unlock {C7, C8}
    if (all(z_lvl[c] is not None for c in ("C1", "C4", "C5", "C8"))
            and c7_level is not None):
        zp = {"C1": cap(z_lvl["C1"]), "C4": cap(z_lvl["C4"]), "C5": cap(z_lvl["C5"])}
        zu = {"C7": c7_level["z_level_C7_capped"], "C8": cap(z_lvl["C8"])}
        fp = family_stouffer(zp)
        fu = family_stouffer(zu)
        z_r = (fu["cross_family"] + fp["cross_family"]) / SQ2
        z_r_bound = (fu["perfect_correlation_bound"] + fp["perfect_correlation_bound"]) / SQ2
        l3["level_v2_roster"] = {
            "pressure_roster": ["C1", "C4", "C5"], "unlock_roster": ["C7", "C8"],
            "z_entering": {**zp, **zu},
            "z_uncapped": {"C1": z_lvl["C1"], "C4": z_lvl["C4"], "C5": z_lvl["C5"],
                           "C7": c7_level["z_level_C7"], "C8": z_lvl["C8"]},
            "C7_program": c7_level,
            "Z_pressure": fp["cross_family"], "Z_unlock": fu["cross_family"],
            "Z_R": round(z_r, 4),
            "perfect_correlation_bound": round(z_r_bound, 4),
            "family_detail": {"pressure": fp, "unlock": fu},
            "sigma_program": "v1.0 z_level for {C1,C4,C5,C8} + C7 estimation-sigma program; "
                             "THE claim-layer level reading from v2 onward",
            "threshold": SIX_SIGMA_Z,
            "threshold_met": z_r >= SIX_SIGMA_Z,
            "confirmation": ">= 3 consecutive post-freeze annual snapshots all >= 6",
        }

    # L3-traj: pressure {C1, C3-fold, C4, C5}, unlock {C7, C8}
    if all(k in zt_capped for k in ("C1", "C3", "C4", "C5", "C7", "C8")):
        zp = {"C1": zt_capped["C1"], "C3": zt_capped["C3"],
              "C4": zt_capped["C4"], "C5": zt_capped["C5"]}
        zu = {"C7": zt_capped["C7"], "C8": zt_capped["C8"]}
        fp = family_stouffer(zp)
        fu = family_stouffer(zu)
        # frozen: Z_R_traj = (Z_unlock_traj + Z_pressure_traj) / sqrt(2)
        z_rt = (fu["cross_family"] + fp["cross_family"]) / SQ2
        z_rt_bound = (fu["perfect_correlation_bound"]
                      + fp["perfect_correlation_bound"]) / SQ2
        l3["traj"] = {
            "pressure_roster": ["C1", "C3-fold", "C4", "C5"], "unlock_roster": ["C7", "C8"],
            "z_traj_uncapped": {k: round(z, 4) for k, z in zt.items()},
            "z_entering": {**zp, **zu},
            "Z_pressure_traj": fp["cross_family"], "Z_unlock_traj": fu["cross_family"],
            "Z_R_traj": round(z_rt, 4),
            "perfect_correlation_bound": round(z_rt_bound, 4),
            "family_detail": {"pressure": fp, "unlock": fu},
            "component_detail": traj_detail,
            "threshold": SIX_SIGMA_Z,
            "threshold_met": z_rt >= SIX_SIGMA_Z,
            "negative_reading_semantics": "negative = proposition NOT supported: pressure-side "
                                          "deterioration certainty exceeds unlock-side improvement "
                                          "certainty; consistent with verdict-layer CRITICAL and the "
                                          "theory's critical-band positioning (R ~ 1); NOT a refutation "
                                          "of the theory - support for the factual statement 'the current "
                                          "global system has not yet entered an unlock-leading trajectory'",
            "breadth_note": "under cap c=5, huge trend t (e.g. C5 CO2) is truncated; the composite "
                            "approaches a breadth measure of decisively-crossing channels - the "
                            "registered cost of guard (a)",
            "confirmation": ">= 3 consecutive post-freeze annual snapshots all >= 6",
        }

    # ---- tau readings (report layer, not test statistics) ----
    taus = {}
    if "C1" in fits and ch["C1"].get("metrics"):
        m1 = ch["C1"]["metrics"]["M1_margin_to_1.5C_C"]
        b_m1 = -fits["C1"]["b"]  # M1 = 1.5 - T -> d(M1)/dt = -dT/dt
        sigma_m = fits["C1"]["sigma"] / math.sqrt(12.0)
        tau = (TAU_THETA["C1"] - m1) / b_m1
        sigma_tau = (1.0 / abs(b_m1)) * math.sqrt(sigma_m ** 2 + tau ** 2 * fits["C1"]["se_b"] ** 2)
        taus["C1"] = {"theta": TAU_THETA["C1"], "theta_meaning": "M1 red line (margin 0)",
                      "M": m1, "b_per_yr": round(b_m1, 6), "tau_yr": round(tau, 2),
                      "sigma_tau_yr": round(sigma_tau, 2),
                      "sigma_M": round(sigma_m, 4),
                      "sigma_M_note": "annual-mean residual / sqrt(12) (12-month trailing "
                                      "mean measurement sigma)"}
    if "C5" in fits and ch["C5"].get("metrics"):
        m5b = ch["C5"]["metrics"]["M5b_co2_margin_to_350ppm"]
        b = fits["C5"]["b"]
        tau = (TAU_THETA["C5"] - m5b) / b
        sigma_tau = (1.0 / abs(b)) * math.sqrt(fits["C5"]["sigma"] ** 2
                                               + tau ** 2 * fits["C5"]["se_b"] ** 2)
        taus["C5"] = {"theta": TAU_THETA["C5"], "theta_meaning": "M5b red boundary",
                      "M": m5b, "b_per_yr": round(b, 4), "tau_yr": round(tau, 2),
                      "sigma_tau_yr": round(sigma_tau, 2),
                      "sigma_M": round(fits["C5"]["sigma"], 3)}
    if "C8" in fits and ch["C8"].get("metrics"):
        m8a = ch["C8"]["metrics"]["M8a_adoption_pct"]
        b = fits["C8"]["b"]
        tau = (TAU_THETA["C8"] - m8a) / b
        sigma_tau = (1.0 / abs(b)) * math.sqrt(fits["C8"]["sigma"] ** 2
                                               + tau ** 2 * fits["C8"]["se_b"] ** 2)
        taus["C8"] = {"theta": TAU_THETA["C8"], "theta_meaning": "M8a GREEN line (unlock side "
                      "reads years-to-green)", "M": m8a, "b_per_yr": round(b, 4),
                      "tau_yr": round(tau, 2), "sigma_tau_yr": round(sigma_tau, 2),
                      "sigma_M": round(fits["C8"]["sigma"], 3)}
    tau_state = {}
    for cid, name in (("C3-GIS", "GIS"), ("C3-AIS", "AIS"), ("C4", "OHC")):
        if ch["C3" if "GIS" in name or "AIS" in name else "C4"].get("status"):
            tau_state[cid] = ch["C3" if cid != "C4" else "C4"]["status"]
    tau_readings = {
        "role": "interpretability reading (years-to-threshold +/- error); NOT a test statistic; "
                "tau-difference tests registered as v3 candidate only",
        "formula": "tau_i = (theta_i - M_i) / b_i",
        "se_formula": "sigma_tau = (1/|b|) * sqrt(sigma_M^2 + tau^2 * SE(b)^2)",
        "level_type": taus,
        "rate_type_state_readings": {
            "C3-GIS": ch["C3"].get("status"), "C3-AIS": ch["C3"].get("status"),
            "C4": ch["C4"].get("status"),
            "note": "rate-type indicators (C3, C4): tau requires second-order trend, not "
                    "registered; channel verdict serves as the reading",
        },
    }

    # ---- Bonferroni channel-level reporting (guard (c), frozen values) ----
    bonf_frozen = v2["guards"]["multiple_comparison"]["bonferroni_frozen_values"]
    channel_level = []
    fam_size = {"climate_carbon": 4, "social": 1, "energy": 1, "information": 1}
    for cid in ("C1", "C4", "C5", "C7", "C8"):
        z = z_lvl.get(cid) if cid != "C7" else (c7_level or {}).get("z_level_C7")
        if z is None:
            continue
        fam = FAMILY_OF[cid]
        m = fam_size[fam]
        thr = bonf_frozen[f"m={m}"]
        channel_level.append({"channel": cid, "program": "z_level", "family": fam, "m": m,
                              "bonferroni_threshold": thr, "z": round(z, 4),
                              "significant": z >= thr})
    for cid in ("C1", "C3", "C4", "C5", "C7", "C8"):
        if cid not in zt:
            continue
        fam = FAMILY_OF[cid]
        m = fam_size[fam]
        thr = bonf_frozen[f"m={m}"]
        channel_level.append({"channel": cid, "program": "z_traj", "family": fam, "m": m,
                              "bonferroni_threshold": thr, "z": round(zt[cid], 4),
                              "significant": zt[cid] >= thr})

    # ---- claim layer assembly ----
    claim_layer = {
        "preregistration": {
            "document": PREREG_V2_MD,
            "md_sha256": v4.sha256_file(PREREG_V2_MD),
            "machine_readable": PREREG_V2_JSON,
            "json_sha256": v4.sha256_file(PREREG_V2_JSON),
            "frozen_before_claim_layer_computation": True,
            "additive_scope": v2["meta"]["additive_scope"],
        },
        "baseline_snapshot": {
            "index": 0,
            "run_utc": run_utc,
            "first_eligible_confirmation_snapshot": "2027-09-30",
            "note": "first claim-layer reading; enters NO confirmation count; all confirmations "
                    "from post-freeze annual snapshots (intersection semantics, optional "
                    "stopping forbidden); L3 earliest confirmation 2029-09-30, L4 ~2035",
        },
        "implementation_guards": {
            "status": "passed",
            "asserted_formula_strings": fs,
            "asserted_secondary_formula_strings": fs2,
            "cap_c": CAP_C,
            "s_table": S_TRAJ,
            "internal_consistency_checks": checks,
        },
        "components": {
            "z_traj": {k: round(z, 4) for k, z in zt.items()},
            "z_traj_capped": {k: round(z, 4) for k, z in zt_capped.items()},
            "z_traj_detail": traj_detail,
            "z_level_C7": c7_level,
            "rederivation_errors": errors,
        },
        "L1_pressure_trend_reality": l1,
        "L2a_energy_learning_curve": l2a,
        "L2b_information_adoption_trend": l2b,
        "L3_R_direction": l3,
        "L4_transition_rate": {
            "status": "not_computable",
            "reason": "T-series data form does not yet exist (~2030+, first base statistical "
                      "system); frozen criteria preregistered in v2 sec 5 (native position)",
            "statistic": "Z_T = (Z_Tunlock + Z_Tpressure) / sqrt(2)",
            "partition": {"governance_pressure": ["T2", "T5", "T6"],
                          "transition_unlock": ["T1", "T3", "T4", "T7", "T8"]},
            "threshold": SIX_SIGMA_Z,
            "confirmation": ">= 5 consecutive annual snapshots after first base statistics year",
        },
        "L5_P1_closure": {
            "status": "far_future_placeholder",
            "criteria_freeze_rule": "freeze when the data form becomes describable, NOT LATER "
                                    "than completion of the first candidate base",
        },
        "tau_readings": tau_readings,
        "bonferroni_channel_level": {
            "frozen_values": bonf_frozen,
            "alpha": "9.9e-10 one-sided",
            "statements": channel_level,
            "composite_policy": "composites on frozen rosters: no selection -> no correction; "
                                "conjunctive ladder semantics conservative; disjunctive claims "
                                "banned (v2 sec 3.2)",
        },
        "family_structure": {
            "families": v2["guards"]["family_aggregation"]["families"],
            "rule": v2["guards"]["family_aggregation"]["rule"],
            "structural_note": v2["guards"]["family_aggregation"]["structural_note"],
            "perfect_correlation_bound_rule": v2["guards"]["family_aggregation"][
                "perfect_correlation_bound"],
        },
        "foreseeability": {
            "register": v2["meta"]["foreseeability_register"],
            "baseline_consequence": "this v5 reading is baseline snapshot 0; no confirmation count",
        },
    }

    # ---- snapshot ----
    out = {
        "pipeline": {
            "name": "CDD-ECS C-series channel pipeline",
            "version": "v5.0",
            "run_utc": run_utc,
            "channel_layer": "v4.0 module imported and re-run verbatim (same frozen thresholds, "
                             "amendments A1-A3, cache-first data, verdict rules, state machine)",
            "claim_layer": "prereg v2.0 first computation (baseline snapshot 0)",
            "preregistration": {
                "document": v4.PREREG_MD,
                "md_sha256": v4.sha256_file(v4.PREREG_MD),
                "machine_readable": v4.PREREG_JSON,
                "json_sha256": v4.sha256_file(v4.PREREG_JSON),
                "frozen_before_data_contact": True,
                "amendment_a1": {
                    "document": v4.A1_MD,
                    "md_sha256": v4.sha256_file(v4.A1_MD),
                    "machine_readable": v4.A1_JSON,
                    "json_sha256": v4.sha256_file(v4.A1_JSON),
                    "threshold_changes": a1["meta"]["threshold_changes"],
                    "registered_before_v2_metric_computation": True,
                },
                "amendment_a2": {
                    "document": v4.A2_MD,
                    "md_sha256": v4.sha256_file(v4.A2_MD),
                    "machine_readable": v4.A2_JSON,
                    "json_sha256": v4.sha256_file(v4.A2_JSON),
                    "threshold_changes": a2["meta"]["threshold_changes"],
                    "registered_before_v3_metric_computation": True,
                    "implementation_guard": f"asserted corrected_formula == {a2_formula!r} before C1 computation",
                },
                "amendment_a3": {
                    "document": v4.A3_MD,
                    "md_sha256": v4.sha256_file(v4.A3_MD),
                    "machine_readable": v4.A3_JSON,
                    "json_sha256": v4.sha256_file(v4.A3_JSON),
                    "threshold_changes": a3["meta"]["threshold_changes"],
                    "channel_verdict_changes": a3["meta"]["channel_verdict_changes"],
                    "state_machine_changes": a3["meta"]["state_machine_changes"],
                    "scope": a3["meta"]["scope"],
                    "registered_before_v4_metric_computation": True,
                    "implementation_guard": f"asserted corrected_formula == {a3_formula!r} before synthesis computation",
                },
                "claim_layer_prereg_v2": {
                    "document": PREREG_V2_MD,
                    "md_sha256": v4.sha256_file(PREREG_V2_MD),
                    "machine_readable": PREREG_V2_JSON,
                    "json_sha256": v4.sha256_file(PREREG_V2_JSON),
                    "frozen_before_claim_layer_computation": True,
                    "threshold_changes_to_verdict_layer": 0,
                    "scope": "claim layer (L1-L5) + T-series preregistration ONLY; "
                             "verdict layer (red/yellow/green + state machine) unchanged",
                    "implementation_guard": "asserted 6 primary + 6 secondary frozen formula "
                                            "strings, cap_c = 5.0 and the z_traj s-sign table "
                                            "byte-exact before claim-layer computation",
                },
                "event_order": (a3["meta"]["event_order_disclosure"]
                                + " -> 6sigma framework v1.0-draft -> v2 claim layer "
                                "preregistration -> v5 run (claim layer first computation, "
                                "baseline snapshot 0)"),
                "criteria_read_order": "v1.0 JSON thresholds (verbatim) -> A1 JSON routes/constants "
                                       "-> A2 JSON C1 definition -> A3 JSON Z_gap synthesis formula "
                                       "-> v2 JSON claim layer criteria (dual sigma, cap, ladder, "
                                       "T-series, tau)",
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
                "A3-1": "Z_gap sum form Z_unlock + Z_pressure (safe-direction unified; aux layer only) [F]",
                "A3-2": "C5 dominance (96.6%) + sigma-program trend blindness registered as disclosure [F]",
                "V2-CL": "claim layer criteria freeze: dual sigma programs, C7 z_level program, "
                         "C3 trajectory fold, contribution cap c=5, family aggregation, ladder "
                         "L1-L5 with confirmation rules, Bonferroni frozen values, T-series T1-T8, "
                         "tau readings [additive only; verdict layer byte-unchanged]",
            },
            "cache_dir": v4.CACHE_DIR,
            "regeneration": "python H:\\cdd_lean4\\scripts\\cdd_ecs_channel_pipeline_v5.py",
            "snapshots_frozen": ["v1", "v2", "v3", "v4 (Z_gap authoritative per A3)"],
        },
        "channels": ch,
        "synthesis": synthesis,
        "claim_layer": claim_layer,
        "notes": [
            "Channel layer = v4.0 code imported and re-run verbatim on the same cache; verdicts, "
            "z_level values, synthesis and state machine by the same code on the same data.",
            "Claim layer = FIRST computation under prereg v2.0 (frozen before data contact); "
            "this reading is BASELINE SNAPSHOT 0 and enters no confirmation count.",
            "Internal consistency guards: every claim-layer re-derivation reproduces the "
            "channel-layer intermediates within registered rounding; ols_full reproduces "
            "v4.ols exactly; any mismatch aborts the run.",
            "z_traj uses frozen windows, frozen direction signs and the uniform 1/sqrt(10) "
            "autocorrelation reduction; C3 enters via the worst-basin fold z_C3 = min(z_GIS, z_AIS).",
            "Contribution cap c=5 applies at synthesis entry only; single-channel propositions "
            "(L2a, L2b) report uncapped values.",
            "L3-traj negative reading is a within-design outcome (see negative_reading_semantics), "
            "not a refutation of the theory.",
            "tau readings are interpretability readings, not test statistics.",
            "T-series (T1-T8) criteria frozen in v2 sec 5; data form does not exist (~2030+); "
            "L4 not computable at this snapshot; L5 far-future placeholder.",
            "No manual numeric values entered anywhere in this pipeline.",
        ],
    }
    with open(OUT_JSON, "w", encoding="utf-8") as f:
        json.dump(out, f, indent=2, ensure_ascii=False)

    # ---- console report ----
    print(f"snapshot written: {OUT_JSON}")
    cl = out["pipeline"]["preregistration"]["claim_layer_prereg_v2"]
    print(f"prereg v2 md   sha256: {cl['md_sha256']}")
    print(f"prereg v2 json sha256: {cl['json_sha256']}")
    print(f"implementation guards: passed ({len(fs)} primary + {len(fs2)} secondary strings)")
    print(f"internal consistency checks: {len(checks)}/{len(checks)} passed")
    print()
    for c in channels:
        m = c.get("metrics", {})
        mv = " ".join(f"{k}={v}" for k, v in (m or {}).items())
        print(f"  {c['id']:>3} {c['name']:<22} {c['status']:<14} {mv[:100]}")
    print()
    s = synthesis
    print(f"  pressure: red={s['pressure_index']['red']} yellow={s['pressure_index']['yellow']}")
    print(f"  unlock:   red={s['unlock_index']['red']} yellow={s['unlock_index']['yellow']}")
    print(f"  state:    {s['state_machine']} (reported={s['global_state_reported']})")
    aux = s["stouffer_auxiliary"]
    print(f"  Z_pressure={aux['Z_pressure']} Z_unlock={aux['Z_unlock']} Z_gap={aux['Z_gap']}")
    print()
    print("  claim layer (baseline snapshot 0; confirmation clock starts 2027-09-30):")
    if l1:
        print(f"    L1      Z_L1={l1['Z_L1']}  (chi2={l1['chi2_reading']}, df={l1['chi2_df']})  "
              f"threshold 6: {'MET' if l1['threshold_met'] else 'not met'}")
    if l2a:
        print(f"    L2a     z={l2a['z_L2a']}  (t_beta={l2a['t_beta']}, SE={l2a['SE_beta']})  "
              f"threshold 6: {'MET' if l2a['threshold_met'] else 'not met'}")
    if l2b:
        if l2b.get("status") == "series_short":
            print(f"    L2b     series_short (n={l2b['n_obs']})")
        else:
            print(f"    L2b     z={l2b['z_L2b']}  (n_obs={l2b['n_obs']}, t={l2b['t_adoption']})  "
                  f"threshold 6: {'MET' if l2b['threshold_met'] else 'not met'}")
    for key, label in (("level_v1_roster", "L3-lvl(v1)"), ("level_v2_roster", "L3-lvl(v2)")):
        if key in l3:
            d = l3[key]
            print(f"    {label}  Z_R={d['Z_R']}  (Zu={d['Z_unlock']}, Zp={d['Z_pressure']}, "
                  f"pc-bound={d['perfect_correlation_bound']})  "
                  f"threshold 6: {'MET' if d['threshold_met'] else 'not met'}")
    if "traj" in l3:
        d = l3["traj"]
        print(f"    L3-traj Z_R_traj={d['Z_R_traj']}  (Zu={d['Z_unlock_traj']}, "
              f"Zp={d['Z_pressure_traj']})  "
              f"{'MET' if d['threshold_met'] else 'not met (negative = not supported; design note)'}")
    print(f"    L4      not_computable (T-series ~2030+)   L5 far_future_placeholder")
    print()
    print("  tau readings (years to threshold, report layer):")
    for cid, d in taus.items():
        print(f"    {cid}: tau={d['tau_yr']} +/- {d['sigma_tau_yr']} yr "
              f"(theta={d['theta']}, b={d['b_per_yr']}/yr)")
    if errors:
        print(f"  rederivation errors: {errors}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
