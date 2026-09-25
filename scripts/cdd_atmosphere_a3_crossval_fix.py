# -*- coding: utf-8 -*-
"""CDD atmosphere A3 Z_cross_validation 自洽化重算 (2026-08-31).

[改良清单 D4, improvement_suggestions_20260831.md] A3 记录
Z_cross_validation = 0.181725, 但由同记录字段直接验算
|gamma_pred − gamma_ocean| / sigma_gamma ≈ 0.188842 (差 3.8%):
分子/σ 口径未文档化 (v8 P0-4 生成脚本未存盘, 全项目无生成代码,
label_fix.py 明确 "数值不变"), 不可复算 — 与 V7 旧值 (4.099397)
同类 "公式口径未存盘" 缺陷, 但 A3 未纳入该诚实边界。

本脚本按可复算口径重算并显式登记公式:
  Z_cross_validation = |gamma_pred − gamma_ocean| / sigma_gamma
(σ 用 A3 自身的大气 sigma_gamma, 与同记录 Z_vs_K41 同口径;
Z_vs_K41 验算与记录完全一致, 佐证该 σ 口径为记录本义)。
旧值 0.181725 → 登记 superseded (口径不可复现, 生成脚本未存盘)。

就地修正 cdd_atmosphere_6sigma_validation_results_v2.json
(v1 快照 3FBF67B6… 冻结不变; v2 为规范快照, D2/D4 数值修订)。
Lean 侧 A3 快照 18 → 19 centi 同步 (T2_Validation)。
"""
import hashlib
import json
import sys

JSON_PATH = r"H:\cdd_atmosphere_6sigma_validation_results_v2.json"


def main():
    with open(JSON_PATH, "r", encoding="utf-8") as f:
        v2 = json.load(f)

    a3 = v2["A3"]
    old = a3["Z_cross_validation"]
    fresh = abs(a3["gamma_pred"] - a3["gamma_ocean"]) / a3["sigma_gamma"]

    # 佐证: Z_vs_K41 同口径复算必须与记录一致 (改前自检)
    zk41 = abs(a3["gamma_pred"] - a3["gamma_K41"]) / a3["sigma_gamma"]
    assert abs(zk41 - a3["Z_vs_K41"]) < 1e-9, f"Z_vs_K41 口径自检失败: {zk41}"

    a3["Z_cross_validation"] = fresh
    a3["Z_cross_validation_formula"] = (
        "|gamma_pred - gamma_ocean| / sigma_gamma "
        "(A3 atmosphere sigma, same sigma as Z_vs_K41)")
    a3["Z_cross_validation_supersedes"] = {
        "value_v1": old,
        "note": ("[D4, 2026-08-31] v8 P0-4 记录值由记录字段复算不可得 "
                 "(0.188842 != 0.181725, 生成脚本未存盘, 分子/σ 口径"
                 "未文档化); 按可复算口径重算并登记公式。"),
    }
    a3["Z_note"] = (f"Z={fresh:.2f}σ (海洋-大气交叉验证, D4 重算口径) / "
                    f"{a3['Z_vs_K41']:.2f}σ (vs K41): 一致性通过, 非 6σ 确认")

    with open(JSON_PATH, "w", encoding="utf-8") as f:
        json.dump(v2, f, ensure_ascii=False, indent=2)

    sha = hashlib.sha256()
    with open(JSON_PATH, "rb") as f:
        sha.update(f.read())
    print(f"Z_vs_K41 口径自检: 复算 {zk41:.9f} == 记录 {a3['Z_vs_K41']:.9f} OK")
    print(f"A3 Z_cross_validation: {old} -> {fresh}")
    print(f"centi: {round(old * 100)} -> {round(fresh * 100)} (Lean 快照 18 -> 19)")
    print(f"OUT: {JSON_PATH}")
    print(f"SHA256: {sha.hexdigest().upper()}")


if __name__ == "__main__":
    sys.exit(main())
