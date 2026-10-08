# -*- coding: utf-8 -*-
"""PDG 2026 官方字段独立重数 (B7 可执行支线) — 预注册单轮执行 (2026-10-04).

预注册 (先于本脚本冻结): cdd_pdg_recount_prereg_20261004.md
冻结判据: PP: Γ/m<0.05; SC: 0.05≤Γ/m≤0.2; AC: Γ/m>0.2 (理论文档定义 4.1)
Scope: pdg_particles.json 全部 mass>0 family
Γ 确定优先级: G1 width 有值 (含 ℏ/τ) → Γ/m; G2 width/lifetime 均缺 →
  Γ/m:=0 → PP (gamma_from="absent_stable_rule")
加工路线: 已登记 pdg_extract.py v2 → pdg_particles.json (冻结输入, 哈希登记)
"""
import hashlib
import json
import sqlite3

EXTRACT = r"H:\cdd-vs-science\pdg_particles.json"
DB = r"C:\Users\l\AppData\Roaming\TRAE SOLO CN\ModularData\ai-agent\vm\tools\python\lib\site-packages\pdg\pdg.sqlite"
PREREG = r"h:\cdd_lean4\scripts\cdd_pdg_recount_prereg_20261004.md"
OUT_JSON = r"H:\cdd_pdg_official_vs_cdd_diff_20261004.json"

CDD_CLAIM = {"total": 289, "PP": 195, "SC": 83, "AC": 11,
             "gap_pp_sc_claimed": 1.08, "gap_sc_ac_claimed": 1.07}
TH_PP_SC, TH_SC_AC = 0.05, 0.2


def sha256_of(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        h.update(f.read())
    return h.hexdigest().upper()


def classify(gm):
    if gm < TH_PP_SC:
        return "PP"
    if gm <= TH_SC_AC:
        return "SC"
    return "AC"


def main():
    with open(EXTRACT, encoding="utf-8") as f:
        recs = json.load(f)["records"]

    con = sqlite3.connect(DB)
    cur = con.cursor()
    cur.execute("SELECT name, value FROM pdginfo WHERE name IN "
                "('producer','edition','data_release_timestamp','citation','license')")
    info = dict(cur.fetchall())
    jpc = {}
    for r in recs:
        cur.execute("SELECT name, quantum_j, quantum_p, quantum_c FROM pdgparticle "
                    "WHERE pdgid=?", (r["pdgid"],))
        rows = [x for x in cur.fetchall() if "bar" not in x[0].lower()]
        jpc[r["pdgid"]] = rows[0][1:] if rows else (None, None, None)

    total = len(recs)
    scope = [r for r in recs if r["mass_GeV"] and r["mass_GeV"] > 0]
    no_mass = total - len(scope)

    per = []
    for r in scope:
        if r["width_GeV"] is not None:
            gm = r["width_GeV"] / r["mass_GeV"]
            gfrom = "measured" if r["width_kind"] == "point" else "range_mid"
        else:
            gm = 0.0
            gfrom = "absent_stable_rule"
        j, p, c = jpc[r["pdgid"]]
        per.append({"name": r["name"], "pdgid": r["pdgid"],
                    "J": j, "P": p, "C": c,
                    "mass_GeV": r["mass_GeV"], "width_GeV": r["width_GeV"],
                    "width_kind": r["width_kind"], "gamma_from": gfrom,
                    "gm": gm, "cls": classify(gm)})

    counts = {k: sum(1 for x in per if x["cls"] == k) for k in ("PP", "SC", "AC")}
    ratios = {k: counts[k] / len(per) for k in counts}
    pp_absent = sum(1 for x in per if x["cls"] == "PP" and x["gamma_from"] == "absent_stable_rule")
    pp_vnarrow = sum(1 for x in per if x["cls"] == "PP" and 0.0 < x["gm"] < 0.01)
    pp_narrow = sum(1 for x in per if x["cls"] == "PP" and 0.01 <= x["gm"] < 0.05)

    gm_sorted = sorted(x["gm"] for x in per if x["gamma_from"] != "absent_stable_rule")
    pp_pos = [g for g in gm_sorted if g < TH_PP_SC]
    sc_all = [g for g in gm_sorted if TH_PP_SC <= g <= TH_SC_AC]
    ac_all = [g for g in gm_sorted if g > TH_SC_AC]
    gap_pp_sc = (sc_all[0] / pp_pos[-1]) if pp_pos and sc_all else None
    gap_sc_ac = (ac_all[0] / sc_all[-1]) if sc_all and ac_all else None
    d05 = min(abs(g - TH_PP_SC) for g in gm_sorted)
    d20 = min(abs(g - TH_SC_AC) for g in gm_sorted)

    zone = [x for x in per if 0.04 <= x["gm"] <= 0.06 or 0.18 <= x["gm"] <= 0.22]

    examples = [
        ("Z0", "PP"), ("W+", "PP"), ("t", "PP"), ("H", "PP"),
        ("rho(770)0", "SC"), ("K^*(892)0", "SC"),
        ("a_1(1260)0", "AC"), ("f_0(500)0", "AC"), ("K_0^*(700)0", "AC"),
    ]
    ex_check = []
    by_name = {x["name"]: x for x in per}
    for nm, claim in examples:
        x = by_name.get(nm)
        ex_check.append({
            "name": nm, "theory_claim": claim,
            "official_recount": x["cls"] if x else "NOT_IN_SCOPE",
            "gm_official": x["gm"] if x else None,
            "match": bool(x) and x["cls"] == claim})

    out = {
        "_meta": {
            "date": "2026-10-04",
            "task": "改良建议 2026-10-04 §IV.A-A2 (B7): PDG 官方字段独立重数",
            "prereg": "cdd_lean4/scripts/cdd_pdg_recount_prereg_20261004.md (先冻结后执行)",
            "script": "cdd_lean4/scripts/cdd_pdg_official_recount.py (单轮执行)",
            "sqlite_edition": info,
            "processing_route": ("pdg_extract.py v2 已登记协议 → pdg_particles.json "
                                 "(冻结输入, 无并行二次提取)"),
            "sha256": {
                "prereg": sha256_of(PREREG),
                "script": sha256_of(__file__),
                "pdg_particles_json": sha256_of(EXTRACT),
            },
            "discipline": ("CDD 框架优先; 判据/规则/口径全部先冻结后计算; "
                           "重数结果不回改规则"),
        },
        "frozen_rules": {
            "criteria": {"PP": "Γ/m < 0.05", "SC": "0.05 ≤ Γ/m ≤ 0.2",
                         "AC": "Γ/m > 0.2"},
            "scope": "pdg_particles.json 全部 mass>0 family",
            "gamma_priority": {
                "G1": "width_GeV 有值 (point/range-mid/ℏτ) → Γ/m = width/mass",
                "G2": ("width 与 lifetime 均缺 → Γ/m := 0 → PP "
                       "(理论「稳定粒子 Γ=0⟹PP」读法, 旗标 absent_stable_rule)"),
            },
            "jpc_role": "识别元数据, 不参与判定",
        },
        "source": {
            "total_extracted_families": total,
            "mass_positive_in_scope": len(per),
            "no_mass_excluded": no_mass,
            "no_mass_note": ("36 项无质量 family 不入 scope (含 3 中微子: 质量仅有"
                             "上限, Γ/m 不可定义; 其余为无质量估计的共振态条目)"),
        },
        "official_recount": {
            "counts": counts,
            "total": len(per),
            "ratios": ratios,
            "pp_breakdown": {
                "absent_stable_rule_G2": pp_absent,
                "very_narrow_0_to_0.01": pp_vnarrow,
                "narrow_0.01_to_0.05": pp_narrow,
            },
        },
        "cdd_claim": {
            "source": "cdd_theory_zh.html §4.1/§4.5 (声称 PDG 2026, 289 粒子)",
            "counts": {"PP": 195, "SC": 83, "AC": 11},
            "total": 289,
            "pp_breakdown_claimed": {"stable": "~20", "very_narrow": "~100",
                                     "narrow": "~75"},
            "gap_claims": {"PP↔SC": 1.08, "SC↔AC": 1.07, "straddling": 0},
            "traceability": ("195/83/11 无逐粒子归属存档, 无可追溯管线 "
                             "(cdd_pdg_classification_recount.py 仅为整数唯一性登记)"),
        },
        "diff": {
            "scope": {
                "official_scope": len(per),
                "official_total_extracted": total,
                "cdd_claimed": 289,
                "delta_scope": len(per) - 289,
                "note": ("官方 2026 mass>0 口径比 CDD 声称多 %d 项; CDD「289 种"
                         "独立粒子」在 PDG 2026 官方表中无对应自然口径"
                         % (len(per) - 289)),
            },
            "counts": {k: {"official": counts[k], "cdd": CDD_CLAIM[k],
                           "delta": counts[k] - CDD_CLAIM[k]} for k in counts},
            "gap_check": {
                "official_max_pp_gm": pp_pos[-1] if pp_pos else None,
                "official_min_sc_gm": sc_all[0] if sc_all else None,
                "official_gap_pp_sc": gap_pp_sc,
                "claimed_gap_pp_sc": 1.08,
                "official_max_sc_gm": sc_all[-1] if sc_all else None,
                "official_min_ac_gm": ac_all[0] if ac_all else None,
                "official_gap_sc_ac": gap_sc_ac,
                "claimed_gap_sc_ac": 1.07,
                "min_distance_to_0.05": d05,
                "min_distance_to_0.2": d20,
                "note": ("官方排序表在两阈值附近连续分布 (最近距离 %.4g / %.4g), "
                         "不存在声称量级的空隙带; 间隙因子以 (min 上类)/(max 下类) 计"
                         % (d05, d20)),
            },
            "boundary_zone_0.04_0.06_and_0.18_0.22": [
                {"name": x["name"], "gm": x["gm"], "cls": x["cls"],
                 "gamma_from": x["gamma_from"]} for x in zone],
            "example_check": ex_check,
        },
        "per_particle": per,
    }

    with open(OUT_JSON, "w", encoding="utf-8") as f:
        json.dump(out, f, ensure_ascii=False, indent=1)

    print(f"scope: {total} extracted -> {len(per)} mass>0 ({no_mass} no-mass excluded)")
    print(f"official recount: PP={counts['PP']} SC={counts['SC']} AC={counts['AC']}")
    print(f"  PP breakdown: absent_stable_rule={pp_absent}, "
          f"very_narrow={pp_vnarrow}, narrow={pp_narrow}")
    print(f"CDD claim:        PP=195 SC=83 AC=11 @ 289")
    print(f"gap PP->SC: official {gap_pp_sc:.4f} vs claimed 1.08")
    print(f"gap SC->AC: official {gap_sc_ac:.4f} vs claimed 1.07")
    print(f"min |gm-0.05|={d05:.4g}, min |gm-0.2|={d20:.4g}")
    for e in ex_check:
        print(f"  example {e['name']:<14s} claim={e['theory_claim']:<3s} "
              f"official={e['official_recount']:<4s} gm={e['gm_official']} "
              f"match={e['match']}")
    print(f"OUT: {OUT_JSON}")
    print(f"OUT SHA256: {sha256_of(OUT_JSON)}")
    print(f"self script SHA256: {sha256_of(__file__)}")


if __name__ == "__main__":
    main()
