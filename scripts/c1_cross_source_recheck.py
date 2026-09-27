"""J12 [2026-09-25]: C1 cross-source aligned-window recheck.

Purpose: the preregistered C1 rule (each source its own trailing 12 months)
compared GISTEMP [2025-08..2026-07] against HadCRUT5 [2024-03..2025-02] --
a 17-month offset. This recheck recomputes both sources on the aligned
intersection window [2024-03..2025-02] from the SAME cached raw files the
v5 pipeline used (data-processing route first, then the data).

Pipeline fidelity: parse functions are verbatim copies of
cdd_ecs_channel_pipeline_v4.py (parse_gistemp_monthly / _parse_hadcrut5);
offset derivation is the A1-1 runtime scheme (off_pi = -mean(1850..1900),
off_5180 = -mean(1951..1980), off_gistemp = off_pi - off_5180).

This file is a disclosure-grade alignment sensitivity check. It does NOT
overwrite the preregistered verdict in the frozen v5 snapshot.

[A4, 2026-09-27] Amendment A4 (registered BEFORE this data contact:
cdd_ecs_channel_preregistration_A4_20260927.md + JSON twin) is executed
here: when the two sources' trailing windows are offset, the cross-source
verdict reads INDETERMINATE (verdict-grade, three-valued). The aligned-
window numbers remain disclosure-grade. A repo-evidence copy is dual-
written to H:\cdd_lean4\scripts\c1_cross_source_recheck_latest.json.
"""
import hashlib
import json
import re
from pathlib import Path

CACHE = Path(r"H:\cdd_ecs_data")
OUT = Path(r"H:\c1_cross_source_recheck.json")
OUT_REPO = Path(r"H:\cdd_lean4\scripts\c1_cross_source_recheck_latest.json")  # [A4] repo-evidence copy

REGISTERED_SHA = {
    "gistemp": "6CFA44E7BBACD9B12CB10BDD64B3182C2735FA3F3A95688E1F7BC8E5DFCECE93",
    "hadcrut5": "75673ADDE85C4A3A52C8BD987D4FF643C6FC4FC3174A6168ACE10DC1B5A70A99",
}
GATE_C = 0.1  # v1.0 cross_disagreement_gate, verbatim


def lf_sha256(path):
    raw = path.read_bytes()
    return hashlib.sha256(raw.replace(b"\r\n", b"\n")).hexdigest().upper()


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


def parse_hadcrut5(text):
    pts = []
    for line in text.splitlines():
        parts = line.split(",")
        if len(parts) >= 2 and re.match(r"^\d{4}-\d{2}$", parts[0].strip()):
            try:
                pts.append((parts[0].strip(), float(parts[1])))
            except ValueError:
                pass
    return pts


def gistemp_window_mean(by_ym, y_end, m_end):
    vals, used, y, m = [], [], y_end, m_end
    for _ in range(12):
        vals.append(by_ym[(y, m)])
        used.append((y, m))
        m -= 1
        if m == 0:
            m, y = 12, y - 1
    return sum(vals) / 12.0, used


def main():
    g_path = CACHE / "C1_gistemp_monthly.csv"
    h_path = CACHE / "C1_hadcrut5_monthly.csv"

    g_sha, h_sha = lf_sha256(g_path), lf_sha256(h_path)
    provenance = {
        "gistemp": {
            "file": str(g_path),
            "lf_normalized_sha256": g_sha,
            "registered_sha256_v5": REGISTERED_SHA["gistemp"],
            "match": g_sha == REGISTERED_SHA["gistemp"],
            "note": "cache file stores CRLF; registered hash is of the original LF response body",
        },
        "hadcrut5": {
            "file": str(h_path),
            "lf_normalized_sha256": h_sha,
            "registered_sha256_v5": REGISTERED_SHA["hadcrut5"],
            "match": h_sha == REGISTERED_SHA["hadcrut5"],
        },
    }
    if not (provenance["gistemp"]["match"] and provenance["hadcrut5"]["match"]):
        out = {
            "recheck_id": "J12",
            "status": "ABORTED_CACHE_MISMATCH",
            "provenance": provenance,
        }
        OUT.write_text(json.dumps(out, indent=2, ensure_ascii=False), encoding="utf-8")
        print(json.dumps(out, indent=2)[:2000])
        return

    g_rows = parse_gistemp_monthly(g_path.read_text(encoding="utf-8", errors="replace"))
    h_pts = parse_hadcrut5(h_path.read_text(encoding="utf-8", errors="replace"))

    by_ym = {(y, m): v for y, m, v in g_rows}
    last_g = max(by_ym)
    last_h = h_pts[-1][0]

    # A1-1 offsets, derived at runtime from HadCRUT5 (verbatim v4 scheme)
    def mean_band(y0, y1):
        vals = [v for d, v in h_pts if y0 <= int(d[:4]) <= y1]
        return sum(vals) / len(vals) if vals else None

    m_pi = mean_band(1850, 1900)
    m_51 = mean_band(1951, 1980)
    off_pi = -m_pi
    off_5180 = -m_51
    off_gistemp = off_pi - off_5180

    # aligned intersection window = HadCRUT5 trailing 12 months
    y_end, m_end = int(last_h[:4]), int(last_h[5:7])
    g_t12, used = gistemp_window_mean(by_ym, y_end, m_end)
    h_t12_raw = sum(v for d, v in h_pts[-12:]) / 12.0

    g_t12_1850 = g_t12 + off_gistemp
    h_t12_1850 = h_t12_raw + off_pi
    diff = abs(g_t12_1850 - h_t12_1850)

    # [A4] v1.0 preregistered rule recomputed: each source its OWN trailing 12m
    g_own_t12, g_own_used = gistemp_window_mean(by_ym, last_g[0], last_g[1])
    g_own_1850 = g_own_t12 + off_gistemp
    diff_misaligned = abs(g_own_1850 - h_t12_1850)
    offset_months = (last_g[0] * 12 + last_g[1]) - (y_end * 12 + m_end)

    out = {
        "recheck_id": "J12",
        "date": "2026-09-27 (A4 execution re-run; first computation 2026-09-25)",
        "status": "computed",
        "purpose": "C1 cross-source recheck on the ALIGNED intersection window; preregistered v5 rule (each source its own trailing 12 months) remains the verdict of record",
        "provenance": provenance,
        "offsets_A1_1": {
            "mode": "derived_at_runtime_from_hadcrut5 (A1-1, verbatim v4 scheme)",
            "off_1850_1900_C": round(off_pi, 4),
            "off_1951_1980_C": round(off_5180, 4),
            "gistemp_pi_offset_C": round(off_gistemp, 4),
            "v5_registered_gistemp_pi_offset_C": 0.2799,
            "offset_matches_v5": abs(round(off_gistemp, 4) - 0.2799) < 0.0005,
        },
        "aligned_window": {
            "months": [f"{used[-1][0]}-{used[-1][1]:02d}", f"{y_end}-{m_end:02d}"],
            "n_months": 12,
            "gistemp_months_available": all((y, m) in by_ym for y, m in used),
        },
        "readings": {
            "gistemp_t12_C_vs_1951_1980": round(g_t12, 4),
            "gistemp_t12_C_vs_1850_1900": round(g_t12_1850, 4),
            "hadcrut5_t12_C_vs_1961_1990": round(h_t12_raw, 4),
            "hadcrut5_t12_C_vs_1850_1900": round(h_t12_1850, 4),
            "abs_diff_C_aligned": round(diff, 4),
            "abs_diff_C_preregistered_misaligned_v5_record": 0.0656,
            "abs_diff_C_preregistered_rule_recomputed": round(diff_misaligned, 4),
            "preregistered_rule_recomputed_matches_v5": abs(round(diff_misaligned, 4) - 0.0656) < 0.0002,
            "gistemp_own_window_months": [f"{g_own_used[-1][0]}-{g_own_used[-1][1]:02d}", f"{last_g[0]}-{last_g[1]:02d}"],
            "misalignment_months": offset_months,
            "disagreement_gate_C": GATE_C,
            "disagreement_aligned": diff > GATE_C,
            "series_extent": {
                "gistemp_last_month": f"{last_g[0]}-{last_g[1]:02d}",
                "hadcrut5_last_month": last_h,
            },
        },
        "verdict_A4": {
            "amendment": "A4 executed 2026-09-27; registered in cdd_ecs_channel_preregistration_A4_20260927.md (+ machine-readable JSON twin) BEFORE this data contact; same sha256-gated cached raw files as v5",
            "rule": "window offset > 0 months => cross_source verdict = INDETERMINATE (boolean forbidden); aligned-window recomputation is disclosure-grade only",
            "window_offset_months": offset_months,
            "cross_source_verdict": "INDETERMINATE" if offset_months > 0 else ("DISAGREEMENT" if diff > GATE_C else "AGREEMENT"),
        },
        "verdict_semantics": {
            "preregistered_rule": "each source its own trailing 12 months (v1.0 verbatim, A1-2 sum/12) — v5 abs_diff 0.0656 with 17-month offset stands as the verdict of record, annotated INDETERMINATE per A4 (annotation layer, values unchanged)",
            "j12_recheck": f"aligned-window abs_diff = {round(diff, 4)} C; disclosure-grade alignment sensitivity only, does NOT overwrite the frozen v5 snapshot",
            "recommended_amendment": "A4 (EXECUTED 2026-09-27; was 'proposed, not yet executed' in the 2026-09-25 output): window alignment upgraded to verdict-grade — trailing windows offset => cross_source verdict reads INDETERMINATE instead of a plain boolean; registration preceded this re-run per preregistration discipline",
        },
    }
    OUT.write_text(json.dumps(out, indent=2, ensure_ascii=False), encoding="utf-8")
    OUT_REPO.write_text(json.dumps(out, indent=2, ensure_ascii=False), encoding="utf-8")
    print(json.dumps(out["provenance"], indent=2))
    print(json.dumps(out["verdict_A4"], indent=2))
    print(json.dumps(out["offsets_A1_1"], indent=2))
    print(json.dumps(out["readings"], indent=2))


if __name__ == "__main__":
    main()
