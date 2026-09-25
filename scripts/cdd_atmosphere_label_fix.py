# -*- coding: utf-8 -*-
"""CDD atmosphere A-series label correction (2026-08-30).

[改良清单 C3, improvement_suggestions_20260830.md] A1-A5 全部是典型参数代入
公式的模型计算值 (输入 T, L, n_e → 算 epsilon_Q, sigma_C, Gamma_d), 无实验
原始观测数据参与对比, 却标记 all_passed:true / A5 "观测一致" — 属 claim
inflation。本脚本把标签语义改为「模型自洽检查通过」并补诚实边界注记。

输出: cdd_atmosphere_6sigma_validation_results_v2.json (旧 v1 冻结保留)。
数值本身不变 — 本轮仅修正标签语义, 无数值重绑。
"""
import hashlib
import json
import sys

IN_JSON = r"H:\cdd_atmosphere_6sigma_validation_results.json"
OUT_JSON = r"H:\cdd_atmosphere_6sigma_validation_results_v2.json"

HONESTY_NOTE = ("A1-A5 为模型参数代入公式的计算值 (输入 T, L, n_e 等典型参数, "
                "计算 lambda_dB, sigma_C, Gamma_d 等), 属量纲/数量级自洽检查, "
                "非与大规模物理实验观测数据的对比 (改良清单 C3, 2026-08-30)。 "
                "真实观测对比需补欧美原位数据源: 电离层非相干散射雷达 "
                "(Arecibo/EISCAT), 闪电通道光谱与温度诊断, 并沿 B3 纪律记录 "
                "URL/DOI 与加工管线哈希。")

LABEL_MAP = {
    "A4: 电离层观测": "A4: 电离层参数模型自洽",
    "A4: Ionosphere observation consistency": "A4: Ionosphere parameter model consistency",
    "A5: 闪电参数": "A5: 闪电参数模型自洽",
}
RESULT_MAP = {"观测一致": "模型自洽检查通过"}


def relabel(node):
    if isinstance(node, dict):
        out = {}
        for k, v in node.items():
            if k == "name":
                v = LABEL_MAP.get(v, v)
            elif k == "result":
                v = RESULT_MAP.get(v, v)
            elif k == "all_passed":
                out["model_consistency_all_passed"] = v
                out["all_passed_semantics"] = "模型自洽检查 (非观测对比)"
                continue
            out[k] = relabel(v)
        return out
    if isinstance(node, list):
        return [relabel(x) for x in node]
    return node


def main():
    with open(IN_JSON, "r", encoding="utf-8") as f:
        v1 = json.load(f)

    v2 = relabel(v1)
    v2["_criteria"] = dict(v1.get("_criteria", {}))
    v2["_criteria"]["label_semantics_v2"] = (
        "v2: A 系列 'passed' 语义 = 模型自洽检查通过, 非 '实验观测验证' (C3)")
    v2["_meta"] = {
        "honesty_note": HONESTY_NOTE,
        "supersedes": {
            "file": "cdd_atmosphere_6sigma_validation_results.json",
            "change": "标签语义修正 (C3): all_passed→模型自洽, A5 '观测一致'→"
                      "'模型自洽检查通过'; 数值未变",
        },
    }

    with open(OUT_JSON, "w", encoding="utf-8") as f:
        json.dump(v2, f, ensure_ascii=False, indent=2)

    sha = hashlib.sha256()
    with open(OUT_JSON, "rb") as f:
        sha.update(f.read())

    print(f"OUT: {OUT_JSON}")
    print(f"SHA256: {sha.hexdigest().upper()}")
    print("changes: all_passed -> model_consistency_all_passed; "
          "A4/A5 names/results relabeled; honesty note added")


if __name__ == "__main__":
    sys.exit(main())
