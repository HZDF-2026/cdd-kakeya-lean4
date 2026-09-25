#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""ABL DATA_test_4.nc 探针数据质量扫描 + 频谱诊断."""

import h5py

import numpy as np

f = h5py.File(r"H:\tmp\abl\DATA_test_4.nc", "r")
probes = sorted(list(f["FlowData"].keys()),
                key=lambda s: int(s.replace("Probe", "")))
good = []
for pr in probes:
    g = f["FlowData/" + pr]
    ux = np.asarray(g["ux"][:], dtype=float)
    valid = np.isfinite(ux)
    n_ok = int(valid.sum())
    if n_ok > 100:
        v = ux[valid]
        good.append(pr)
        print(f"{pr:9s} n_valid={n_ok:6d}  U={v.mean():7.3f}  "
              f"sigma={v.std():6.3f}  y={g['Position/y'][0]:8.1f}  "
              f"z={g['Position/z'][0]:7.1f}")
    else:
        print(f"{pr:9s} ALL-NAN/empty")
print("good probes:", len(good), "of", len(probes))

# 取第一个好探针做频谱诊断
if good:
    g = f["FlowData/" + good[0]]
    ux = np.asarray(g["ux"][:], dtype=float)
    ux = ux[np.isfinite(ux)]
    n = len(ux)
    print(f"\n{good[0]}: n={n}")
    # 自相关 → 采样间隔无法直接得; 尝试不同 fs 假设下 PSD
    # 先看时间序列的差分统计判断噪声水平
    d1 = np.diff(ux)
    print(f"std(ux)={ux.std():.4f}  std(diff)={d1.std():.4f}  "
          f"ratio={d1.std()/ux.std()/np.sqrt(2):.4f} (白噪声→~1)")
    # lag-1 自相关
    ac1 = np.corrcoef(ux[:-1], ux[1:])[0, 1]
    print(f"lag-1 autocorr = {ac1:.4f}")
    # 4 阶差分噪声检验: 白噪声时 std(d^k) 增长按 binomial 系数
    d4 = ux[4:] - 4 * ux[3:-1] + 6 * ux[2:-2] - 4 * ux[1:-3] + ux[:-4]
    print(f"std(d4)/std(ux) = {d4.std()/ux.std():.3f} "
          f"(纯白噪声: sqrt(256)={256**0.5:.1f})")
f.close()
