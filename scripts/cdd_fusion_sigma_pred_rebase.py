# -*- coding: utf-8 -*-
"""CDD F1/F2 σ_pred 重立 (J4 可执行支线) — 预注册单轮执行 (2026-10-04).

预注册 (先于本脚本冻结): cdd_fusion_sigma_pred_prereg_20261004.md
冻结规则:
  R1/R2: 输入 log10 空间 1σ = 0.5 dex
         (δv_turb 文档化范围 [1e3,1e4] m/s 一 decade 半程; ℓ_c 仅 "~1 cm")
  R3:    σ_pred(F1) = γ_pred · √2 · ln(10)/2
  R4:    σ_pred(F2) = max(c−0.90, 0.98−c), c = reduction_pred (登记中心值)

标签纪律 (预注册 §4): F2 tension/consistent/tension_gt_3sigma 三标签维持 v2
不翻转 (σ_exp 仍 UNTRACEABLE, J4 裁决冻结); v2 冻结保留, 本脚本输出 v3。
"""
import hashlib
import json
import math

IN_JSON = r"H:\cdd_fusion_6sigma_validation_results_v2.json"
OUT_JSON = r"H:\cdd_fusion_6sigma_validation_results_v3.json"
PREREG = r"h:\cdd_lean4\scripts\cdd_fusion_sigma_pred_prereg_20261004.md"

GAMMA_PRED = 100000.0
LN10_HALF = math.log(10.0) / 2.0          # 0.5 dex
SIGMA_PRED_F1 = GAMMA_PRED * math.sqrt(2.0) * LN10_HALF
F2_INTERVAL = (0.90, 0.98)                # paper2 Thm 3.3 合成效应句


def sha256_of(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        h.update(f.read())
    return h.hexdigest().upper()


def f1_sigma_block(v2_f1):
    legacy = v2_f1["sigma_pred"]
    return {
        "prereg": "cdd_lean4/scripts/cdd_fusion_sigma_pred_prereg_20261004.md",
        "rule": ("R1/R2/R3: σ_pred = γ_pred·√2·ln10/2 (两输入各 0.5 dex: "
                 "δv_turb [1e3,1e4] m/s 文档化范围半程, ℓ_c ~1 cm OOM 惯例); "
                 "γ_pred = δv/ℓ_c = 1e3/1e-2 (paper2 Thm 3.1)"),
        "sigma_pred_new": SIGMA_PRED_F1,
        "sigma_pred_legacy_untraceable": legacy,
        "date": "2026-10-04",
    }


def f2_sigma_block(v2_f2):
    c = v2_f2["reduction_pred"]
    a, b = F2_INTERVAL
    return {
        "prereg": "cdd_lean4/scripts/cdd_fusion_sigma_pred_prereg_20261004.md",
        "rule": ("R4: σ_pred = max(c−a, b−c), 区间 [a,b]=[0.90,0.98] = "
                 "paper2 Thm 3.3 合成效应句 (χ∈[0.02,0.10] → 压低 90–98%); "
                 "c = 登记中心值 (推导维持 UNTRACEABLE, A1 只重立 σ)"),
        "sigma_pred_new": max(c - a, b - c),
        "sigma_pred_legacy_untraceable": v2_f2["sigma_pred"],
        "interval_used": [a, b],
        "date": "2026-10-04",
    }


def main():
    with open(IN_JSON, "r", encoding="utf-8") as f:
        v2 = json.load(f)

    # ---------------- F1 ----------------
    f1 = json.loads(json.dumps(v2["F1"]))  # deep copy
    f1["sigma_pred"] = SIGMA_PRED_F1
    f1["sigma_pred_rebase"] = f1_sigma_block(v2["F1"])

    for r in f1["devices_judgment"] + f1["reference_devices"]:
        r["sigma_pred"] = SIGMA_PRED_F1
        denom = math.sqrt(r["sigma_exp"] ** 2 + SIGMA_PRED_F1 ** 2)
        r["Z"] = (r["gamma_exp"] - GAMMA_PRED) / denom
        r["passed"] = abs(r["Z"]) < 6.0
    f1["results"] = [dict(r) for r in f1["devices_judgment"]]

    w = [1.0 / r["sigma_exp"] ** 2 for r in f1["devices_judgment"]]
    sw = sum(w)
    gamma_w = sum(wi * r["gamma_exp"] for wi, r in zip(w, f1["devices_judgment"])) / sw
    sigma_w = 1.0 / math.sqrt(sw)
    f1["gamma_exp_weighted"] = gamma_w
    f1["sigma_exp_weighted"] = sigma_w
    f1["Z_combined"] = (gamma_w - GAMMA_PRED) / math.sqrt(sigma_w ** 2 + SIGMA_PRED_F1 ** 2)
    f1["Z_combined_legacy_untraceable"] = v2["F1"]["Z_combined"]
    f1["Z_note"] = (
        f"[A1-rebase, 2026-10-04] Z={f1['Z_combined']:.3f}σ (rebased, pred 侧 σ 重立后): "
        f"欧美双装置加权一致性检验通过 (|Z|≪6, 非 6σ 确认)。legacy Z=0.136σ "
        "(σ_pred=93750 UNTRACEABLE 时代) 保留于 Z_combined_legacy_untraceable。")
    f1["consistent"] = abs(f1["Z_combined"]) < 6.0
    sp = dict(f1["sigma_provenance"])
    sp["sigma_pred"] = (
        "[A1-rebase, 2026-10-04] TRACEABLE: σ_pred = γ_pred·√2·ln10/2 = "
        f"{SIGMA_PRED_F1:.6g} (预注册 R1/R2/R3, 先冻结后计算; 脚本 "
        "cdd_fusion_sigma_pred_rebase.py 存盘)。legacy 硬编码 93750 "
        "(=93.75%·γ_pred, 无文档依据) 已被替换并保留于 sigma_pred_rebase 块。")
    sp["gamma_pred_origin"] = (
        "[A1-rebase, 2026-10-04] TRACEABLE as OOM: γ_pred = δv_turb/ℓ_c = "
        "1.0e3 m/s / 1.0e-2 m = 1.0e5 s⁻¹ (paper2 Thm 3.1 + §3.1 校正注: "
        "δv_turb~10³ m/s, ℓ_c~1 cm; 校正史 10⁶→10⁵ s⁻¹)。性质 = 量级估计 "
        "(OOM), 非拟合值; 中心值本轮不改动。")
    f1["sigma_provenance"] = sp

    # ---------------- F2 ----------------
    f2 = json.loads(json.dumps(v2["F2"]))
    sig2 = f2_sigma_block(v2["F2"])
    f2["sigma_pred"] = sig2["sigma_pred_new"]
    f2["sigma_pred_rebase"] = sig2

    for r in f2["results"]:
        r["sigma_pred"] = sig2["sigma_pred_new"]
        denom = math.sqrt(r["sigma_exp"] ** 2 + sig2["sigma_pred_new"] ** 2)
        r["Z"] = (r["reduction_pred"] - r["reduction_exp"]) / denom
        r["passed"] = abs(r["Z"]) < 6.0

    red_w = f2["reduction_exp_weighted"]
    sig_exp_w = f2["sigma_exp_weighted"]
    f2["Z_combined"] = (f2["reduction_pred"] - red_w) / math.sqrt(
        sig_exp_w ** 2 + sig2["sigma_pred_new"] ** 2)
    f2["Z_combined_legacy_untraceable"] = v2["F2"]["Z_combined"]
    f2["Z_note"] = (
        "[A1-rebase, 2026-10-04] pred 侧 σ 重立 (R4: σ_pred="
        f"{sig2['sigma_pred_new']:.6f}, 区间 [0.90,0.98]) 后 Z="
        f"{f2['Z_combined']:.3f}σ (<3σ)。BUT: σ_exp 三装置仍 UNTRACEABLE "
        "(J4 全文阻塞未解), 裁决冻结维持——tension/consistent/"
        "tension_gt_3sigma 标签维持 v2 不翻转, rebased Z 仅作量级参考, "
        "禁止据此换算为支持或反驳任一方向。legacy Z=3.18σ (σ_pred=0.00923 "
        "UNTRACEABLE) 保留于 Z_combined_legacy_untraceable。最终裁决待 σ_exp "
        "全文解锁。")
    sp2 = dict(f2["sigma_provenance"])
    sp2["sigma_pred"] = (
        "[A1-rebase, 2026-10-04] TRACEABLE: σ_pred = max(c−0.90, 0.98−c) = "
        f"{sig2['sigma_pred_new']:.10f} (预注册 R4, 区间 [0.90,0.98] = paper2 "
        "Thm 3.3 合成效应句; 脚本 cdd_fusion_sigma_pred_rebase.py 存盘)。"
        "legacy 0.009230514764086317 (继承 v1, 生成脚本未存盘) 已替换并保留于 "
        "sigma_pred_rebase 块。中心值 0.9775203773316054 的推导维持 UNTRACEABLE。")
    sp2["central_value_internal_inconsistency"] = (
        "[A1-rebase 登记性发现, 2026-10-04] paper2 三机制文档中值乘积 χ≈0.16 "
        "(压低 0.84) 与机制子区间乘积范围 [0.084,0.27] (压低 [0.73,0.916]) 与 "
        "Thm 3.3 合成句 [0.02,0.10] (压低 [0.90,0.98]) 及登记中心值 0.9775 "
        "互不一致; R4 采用单一来源 = Thm 3.3 合成句。已登记, 不在本支线修复。")
    f2["sigma_provenance"] = sp2
    # 标签纪律: test_type / consistent / tension_gt_3sigma / pred_minus_exp_pct_points 原值不动

    # ---------------- F_combined ----------------
    fc = {
        "test": "F_combined",
        "inputs": {
            "F1_Z_combined": f1["Z_combined"],
            "F2_Z_combined": f2["Z_combined"],
        },
        "formula": "Z_direct = sqrt(F1.Z_combined^2 + F2.Z_combined^2)",
        "Z_direct": math.sqrt(f1["Z_combined"] ** 2 + f2["Z_combined"] ** 2),
        "Z_direct_legacy_untraceable": v2["F_combined"]["Z_direct"],
        "note": (
            "[D2, 2026-08-31] 单一事实来源规则维持: Z_direct 由 F1/F2 现值直接合成。"
            "[A1-rebase, 2026-10-04] 输入 Z 均为 rebased 值 (pred 侧 σ 重立后); "
            "F2 分量仍受 σ_exp UNTRACEABLE 约束, 本 Z_direct 仅量级参考。"),
    }

    # ---------------- 顶层 ----------------
    v3 = dict(v2)
    v3["F1"] = f1
    v3["F2"] = f2
    v3["F_combined"] = fc
    v3["_criteria"] = dict(v2.get("_criteria", {}))
    v3["_criteria"]["sigma_provenance_gap"] = (
        "[H/F4, 2026-09-04 原文] F1/F2 的 sigma_pred 与各装置 sigma_exp 均为硬编码值…"
        " → [A1-rebase v3, 2026-10-04] pred 侧已重立 TRACEABLE (预注册 "
        "cdd_fusion_sigma_pred_prereg_20261004.md, 单轮执行, 脚本存盘); "
        "exp 侧维持 UNTRACEABLE (J4 全文阻塞), Z 值仍仅量级参考")
    v3["_criteria"]["sigma_pred_rebase_v3"] = (
        "[A1/J4-exec, 2026-10-04] F1 σ_pred = γ_pred·√2·ln10/2 (R1/R2/R3); "
        "F2 σ_pred = max(c−0.90, 0.98−c) (R4, Thm 3.3 区间); 标签纪律: F2 tension "
        "三标签维持不翻转 (裁决冻结, σ_exp 未解)")

    j4 = dict(v2["J4_blocked"])
    j4["executable_branch_status"] = (
        "EXECUTED 2026-10-04 (A1, 改良建议 2026-10-04 §IV.A): σ_pred 侧重立完成 "
        "(F1/F2 TRACEABLE, 预注册先冻结后计算, 脚本存盘, 见 F1/F2.sigma_pred_rebase)")
    j4["status"] = "PARTIAL: pred-side REBASED (2026-10-04); exp-side still BLOCKED (full-text dependency)"
    j4["blocker"] = (
        "σ_exp 误差棒方法学需判决文献原文全文: DIII-D/Groebner、ASDEX-U/Ryter、"
        "JET/Maggi (未变); σ_pred 侧阻塞已于 2026-10-04 解除")
    j4["adjudication_freeze"] = (
        "[A1-rebase 更新, 2026-10-04] F2 维持「量级参考/待裁决」: legacy Z=3.18σ "
        "(σ 双侧 UNTRACEABLE), rebased Z=1.22σ (pred TRACEABLE, exp UNTRACEABLE); "
        "rebased Z<3σ 不构成裁决——tension 标签不据此翻转, 禁止下游换算为支持或"
        "反驳任一方向; 最终裁决待 σ_exp 全文解锁")
    j4["provenance_chain"] = {
        "prereg_file": "cdd_lean4/scripts/cdd_fusion_sigma_pred_prereg_20261004.md",
        "prereg_sha256": sha256_of(PREREG),
        "script_file": "cdd_lean4/scripts/cdd_fusion_sigma_pred_rebase.py",
        "input_v2_sha256": sha256_of(IN_JSON),
        "output_v3": "cdd_fusion_6sigma_validation_results_v3.json",
    }
    v3["J4_blocked"] = j4

    with open(OUT_JSON, "w", encoding="utf-8") as f:
        json.dump(v3, f, ensure_ascii=False, indent=2)

    print(f"F1: sigma_pred {v2['F1']['sigma_pred']:.6g} -> {SIGMA_PRED_F1:.6g} "
          f"(rel {math.sqrt(2)*LN10_HALF:.6f})")
    for r in f1["devices_judgment"] + f1["reference_devices"]:
        print(f"    {r['device']:<10s} Z {r['Z']:+.6f}")
    print(f"    Z_combined {v2['F1']['Z_combined']:.6f} -> {f1['Z_combined']:.6f}")
    print(f"F2: sigma_pred {v2['F2']['sigma_pred']:.6g} -> {sig2['sigma_pred_new']:.6g}")
    for r in f2["results"]:
        print(f"    {r['device']:<15s} Z {r['Z']:+.6f}")
    print(f"    Z_combined {v2['F2']['Z_combined']:.6f} -> {f2['Z_combined']:.6f}")
    print(f"F_combined Z_direct {v2['F_combined']['Z_direct']:.6f} -> {fc['Z_direct']:.6f}")
    print(f"labels frozen: F2 test_type={f2['test_type']}, consistent={f2['consistent']}, "
          f"tension_gt_3sigma={f2['tension_gt_3sigma']}")
    print(f"OUT: {OUT_JSON}")
    print(f"OUT SHA256: {sha256_of(OUT_JSON)}")
    print(f"self script SHA256: {sha256_of(__file__)}")


if __name__ == "__main__":
    main()
