# -*- coding: utf-8 -*-
"""CDD F1 critical shear rate — Western-devices-only recalculation (2026-08-30).

[改良清单 C3, improvement_suggestions_20260830.md] F1 原加权平均混入东亚装置
(EAST/KSTAR), 违反"优先采集欧美实验数据"的既定原则。本脚本:
  1. 仅用欧美装置 (DIII-D, ASDEX-U) 重算 gamma_exp 加权均值与 Z_combined;
  2. EAST/KSTAR 降级为 reference_devices (参考/暂存, 不进入判决性加权);
  3. 输出新快照 cdd_fusion_6sigma_validation_results_v2.json (旧 v1 冻结保留)。

方法论 (与 v1 管线一致):
  - 装置级 Z_i = (gamma_exp_i - gamma_pred) / sqrt(sigma_exp_i^2 + sigma_pred^2)
  - 加权均值: 逆方差权重 w_i = 1/sigma_exp_i^2 (仅实验方差)
  - 合成 Z = (gamma_exp_w - gamma_pred) / sqrt(sigma_exp_w^2 + sigma_pred^2)

输入 (文献参数级, 与 v1 相同来源):
  - DIII-D:   gamma_exp = 1.5e5, sigma_exp = 5.0e4  (Burrell et al. 1997; Schmitz et al. 2012)
  - ASDEX-U:  gamma_exp = 1.0e5, sigma_exp = 3.0e4  (Happel et al. 2009; Conway et al. 2015)
  - 理论预测: gamma_pred = 1.0e5, sigma_pred = 9.375e4
JET (欧美) 无 E×B 临界剪切率独立报告, 不强行并入; 登记为可扩展项。
"""
import hashlib
import json
import math
import sys

IN_JSON = r"H:\cdd_fusion_6sigma_validation_results.json"
OUT_JSON = r"H:\cdd_fusion_6sigma_validation_results_v2.json"

GAMMA_PRED = 100000.0
SIGMA_PRED = 93750.0

WESTERN = [
    {"device": "DIII-D", "gamma_exp": 150000.0, "sigma_exp": 50000.0,
     "source": "Burrell et al. 1997; Schmitz et al. 2012"},
    {"device": "ASDEX-U", "gamma_exp": 100000.0, "sigma_exp": 30000.0,
     "source": "Happel et al. 2009; Conway et al. 2015"},
]
REFERENCE = [
    {"device": "EAST", "gamma_exp": 80000.0, "sigma_exp": 40000.0,
     "source": "Xu et al. 2019"},
    {"device": "KSTAR", "gamma_exp": 120000.0, "sigma_exp": 60000.0,
     "source": "Lee et al. 2021"},
]


def device_z(r):
    denom = math.sqrt(r["sigma_exp"] ** 2 + SIGMA_PRED ** 2)
    return (r["gamma_exp"] - GAMMA_PRED) / denom


def main():
    with open(IN_JSON, "r", encoding="utf-8") as f:
        v1 = json.load(f)

    for r in WESTERN + REFERENCE:
        r["gamma_pred"] = GAMMA_PRED
        r["sigma_pred"] = SIGMA_PRED
        r["Z"] = device_z(r)
        r["passed"] = abs(r["Z"]) < 6.0

    w = [1.0 / r["sigma_exp"] ** 2 for r in WESTERN]
    sw = sum(w)
    gamma_w = sum(wi * r["gamma_exp"] for wi, r in zip(w, WESTERN)) / sw
    sigma_w = 1.0 / math.sqrt(sw)
    z_comb = (gamma_w - GAMMA_PRED) / math.sqrt(sigma_w ** 2 + SIGMA_PRED ** 2)

    f1_v2 = {
        "test": "F1_critical_shear_rate",
        "gamma_pred": GAMMA_PRED,
        "sigma_pred": SIGMA_PRED,
        "gamma_exp_weighted": gamma_w,
        "sigma_exp_weighted": sigma_w,
        "Z_combined": z_comb,
        "devices_judgment": WESTERN,
        "reference_devices": REFERENCE,
        "reference_note": ("EAST/KSTAR 为东亚装置, 按欧美优先原则降级为参考/暂存, "
                           "不进入判决性加权 (改良清单 C3, 2026-08-30)"),
        "jet_extension_note": "JET (欧美) 无独立 gamma_crit 报告, 登记为可扩展项",
        "results": WESTERN,
        "test_type": "consistency",
        "Z_note": (f"Z={z_comb:.3f}σ: 欧美双装置 (DIII-D/ASDEX-U) 加权一致 "
                   "(一致性通过, 非 6σ 确认)"),
        "consistent": abs(z_comb) < 6.0,
        "passed_6sigma": False,
        "supersedes": {
            "file": "cdd_fusion_6sigma_validation_results.json",
            "Z_combined_v1": v1["F1"]["Z_combined"],
            "change": "F1 加权剔除 EAST/KSTAR (C3), 其余 F2-F5 未改动",
        },
    }

    # [D2, 2026-08-31] 合成层同步重算 (单一事实来源):
    # C3 只重算了 F1 本体, F_combined 仍持 v1 旧拷贝
    # (individual_Z[0].Z = 0.056377, Z_direct 由旧值合成 = 3.181061),
    # 同一文件内 F1 出现两个 Z 值。改为删除逐测试重复 Z, 仅保留
    # Z_direct (由 F1.Z_combined 与 F2.Z_combined 现值直接合成) 并
    # 显式标注输入来源。
    z_f2 = v1["F2"]["Z_combined"]
    z_direct = math.sqrt(z_comb ** 2 + z_f2 ** 2)
    f_combined_v2 = {
        "test": "F_combined",
        "inputs": {
            "F1_Z_combined": z_comb,
            "F2_Z_combined": z_f2,
        },
        "formula": "Z_direct = sqrt(F1.Z_combined^2 + F2.Z_combined^2)",
        "Z_direct": z_direct,
        "note": ("[D2, 2026-08-31] v2 旧 F_combined.individual_Z[0].Z = 0.056377 "
                 "为 v1 遗留拷贝 (C3 未同步合成层), 旧 Z_direct = 3.181061 "
                 "由旧值合成; 逐测试重复 Z 已删除 (单一事实来源), "
                 "由 F1/F2 现值直接重算。"),
    }

    v2 = dict(v1)
    v2["F1"] = f1_v2
    v2["F_combined"] = f_combined_v2
    v2["_criteria"] = dict(v1.get("_criteria", {}))
    v2["_criteria"]["F1_device_policy"] = (
        "v2: 仅欧美装置 (DIII-D/ASDEX-U) 判决; EAST/KSTAR 参考 (C3, 2026-08-30)")
    v2["_criteria"]["F_combined_single_source"] = (
        "v2: F_combined 不再复制 F1/F2 逐测试 Z, Z_direct 由 "
        "F1.Z_combined/F2.Z_combined 直接合成 (D2, 2026-08-31)")

    with open(OUT_JSON, "w", encoding="utf-8") as f:
        json.dump(v2, f, ensure_ascii=False, indent=2)

    sha = hashlib.sha256()
    with open(OUT_JSON, "rb") as f:
        sha.update(f.read())

    print(f"F1 v2 (Western only): gamma_exp_w = {gamma_w:.6f}")
    print(f"                     sigma_exp_w  = {sigma_w:.6f}")
    print(f"                     Z_combined   = {z_comb:.6f}")
    print(f"                     centi-snap   = {round(z_comb * 100)}")
    print(f"F_combined v2 [D2]:   Z_direct     = {z_direct:.6f} "
          f"(sqrt(F1^2 + F2^2), F2 = {z_f2:.6f})")
    print(f"v1 Z_combined (4 devices, superseded): {v1['F1']['Z_combined']:.6f}")
    print(f"v1 F_combined Z_direct (superseded):   {v1['F_combined']['Z_direct']:.6f}")
    print(f"OUT: {OUT_JSON}")
    print(f"SHA256: {sha.hexdigest().upper()}")


if __name__ == "__main__":
    sys.exit(main())
