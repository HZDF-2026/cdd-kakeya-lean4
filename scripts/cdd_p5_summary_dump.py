#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""P5 v28.4 结果摘要提取 (验证用, 不改数据)."""
import json

d = json.load(open(r"H:\cdd_p5_v28_4_results.json", encoding="utf-8"))

A = d["A_swuf3d_corrected"]
print("=== A: SWUF-3D 修正 ===")
print(f"  alpha_u = {A['alpha_u']}, sigma = {A['sigma_alpha']}")
print(f"  delta = {A['delta_alpha']}, Z_vs_K41 = {A['Z_vs_K41']}")
print(f"  Re_lambda mean = {A['Re_lambda_mean']}, range = {A['Re_lambda_range']}")
print(f"  n_files = {A['n_files']}")
print(f"  erratum_vs_P4 = {json.dumps(A['erratum_vs_P4'], ensure_ascii=False)[:400]}")

print()
print("=== B: ABL 通道 Z 值 ===")
for name, ch in d["B_abl_channels"].items():
    keys = {k: ch.get(k) for k in ("alpha_u", "sigma_alpha", "delta_alpha",
                                    "Z_vs_K41", "Re_lambda", "n_probes")}
    print(f"  {name}: {keys}")

print()
print("=== C: 轨迹律 v28.4 ===")
C = d["C_trajectory_v28_4"]
print("  keys:", list(C.keys()))
for k, v in C.items():
    if isinstance(v, dict):
        print(f"  {k}:")
        for kk, vv in v.items():
            if isinstance(vv, (int, float, str, bool)):
                print(f"    {kk} = {vv}")
    elif isinstance(v, list):
        print(f"  {k}: list[{len(v)}]")
        for it in v[:12]:
            if isinstance(it, dict):
                print("    " + ", ".join(
                    f"{a}={b:.4g}" if isinstance(b, float) else f"{a}={b}"
                    for a, b in list(it.items())[:6]))
    else:
        print(f"  {k} = {v}")

print()
print("=== D: V6d 合成 ===")
D = d["D_v6d_synthesis"]
for k, v in D.items():
    if isinstance(v, dict):
        print(f"  {k}:")
        for kk, vv in v.items():
            if isinstance(vv, (int, float, str, bool)):
                print(f"    {kk} = {vv}")
            elif isinstance(vv, list) and vv and not isinstance(vv[0], dict):
                print(f"    {kk} = {vv}")
    elif isinstance(v, list):
        print(f"  {k}: list[{len(v)}]")
        for it in v[:12]:
            if isinstance(it, dict):
                print("    " + ", ".join(
                    f"{a}={b:.4g}" if isinstance(b, float) else f"{a}={b}"
                    for a, b in list(it.items())[:5]))
    else:
        print(f"  {k} = {v}")

print()
print("=== E: gamma 匹配对 ===")
E = d["E_gamma_matched"]
for k, v in E.items():
    if isinstance(v, dict):
        print(f"  {k}:")
        for kk, vv in v.items():
            if isinstance(vv, (int, float, str, bool)):
                print(f"    {kk} = {vv}")
    else:
        print(f"  {k} = {v}")
