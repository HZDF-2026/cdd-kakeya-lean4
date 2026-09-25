#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""SWUF-3D 深度诊断 (P5 前置): 低频污染来源 + 惯性区客观定位 + ESS 窗口敏感性.

诊断项:
  1. Welch PSD 分段斜率 (0.05–500 Hz) → 低频能量占比
  2. 无混叠自相关 R(τ) → 真实积分尺度
  3. S3(τ)/τ 平台 (4/5 律精确惯性区定位)
  4. ESS 局部斜率 ζ(1)/ζ(3)(τ) → 自洽平台
  5. 多窗口 ESS 拟合 → α_u 敏感性
"""

import importlib.util

import numpy as np

_spec = importlib.util.spec_from_file_location(
    "cdd_p2", r"H:\cdd_lean4\scripts\cdd_p2_pipeline.py")
_p2 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_p2)

FILES = [
    r"H:\turbulence_obs_data\SWUF3D\turbulence__V0_11__I_11p5__20221007__f_cta_1000.txt",
    r"H:\turbulence_obs_data\SWUF3D\turbulence__V0_5__I_11p5__20221007__f_cta_1000.txt",
    r"H:\turbulence_obs_data\SWUF3D\turbulence__V0_15__I_11p5__20221012__f_cta_1000.txt",
    r"H:\turbulence_obs_data\SWUF3D\turbulence__V0_fan__I_15p0__20221007__f_cta_1000.txt",
]


def autocorr_fft(x):
    """线性自相关 (零填充至 >= 2n, 无循环混叠)."""
    n = len(x)
    n2 = 1 << (2 * n - 1).bit_length()
    f = np.fft.rfft(x - x.mean(), n2)
    return np.fft.irfft(f * np.conj(f), n2)[:n] / n


for fp in FILES:
    t, u = _p2.load_swuf3d(fp)
    dt = float(np.median(np.diff(t)))
    fs = 1.0 / dt
    n = len(u)
    U0 = float(np.mean(u))
    idx = np.arange(n)
    u_det = u - np.polyval(np.polyfit(idx, u, 1), idx)
    sig = float(np.std(u_det))
    print("=" * 76)
    print(f"{fp.split(chr(92))[-1][:56]}")
    print(f"  n={n}  U0={U0:.2f} m/s  I={sig/U0*100:.2f}%  fs={fs:.1f} Hz")

    # --- 1. PSD 分段 ---
    freqs, psd = _p2.welch_psd(u_det, fs, 1 << 16)
    bands = [(0.05, 0.5), (0.5, 2), (2, 10), (10, 100), (100, 400), (400, 499)]
    for lo, hi in bands:
        m = (freqs >= lo) & (freqs <= hi)
        b = float(np.polyfit(np.log(freqs[m]), np.log(psd[m]), 1)[0])
        print(f"  PSD [{lo:6g},{hi:4g}] Hz  slope={b:+.3f}  <E>={psd[m].mean():.3e}")
    var_tot = np.trapz(psd, freqs)
    for lo, hi in [(0.05, 0.5), (0.5, 2), (2, 100), (100, 499)]:
        m = (freqs >= lo) & (freqs <= hi)
        print(f"    var-frac [{lo:g},{hi:g}] Hz = {np.trapz(psd[m], freqs[m])/var_tot*100:6.2f}%")

    # --- 2. 自相关 ---
    ac = autocorr_fft(u_det)
    R = ac / ac[0]
    lags_ms = [1, 2, 5, 10, 20, 50, 100, 200, 500, 1000, 2000]
    print("  R(τ): " + "  ".join(f"{l}ms:{float(R[l]):.3f}" for l in lags_ms))
    zc = np.where(R < 0)[0]
    tau_int = zc[0] * dt if len(zc) else float("nan")
    print(f"  首过零 τ_int = {tau_int*1e3:.1f} ms → L = {U0*tau_int:.3f} m")

    # --- 3+4. 结构函数, S3/τ 平台, ESS 局部斜率 ---
    taus = np.unique(np.clip(
        (np.logspace(-2.7, 0.3, 60) * fs).astype(int), 1, n // 10))
    S1 = np.empty(len(taus))
    S2 = np.empty(len(taus))
    S3 = np.empty(len(taus))
    for i, k in enumerate(taus):
        du = u_det[k:] - u_det[:-k]
        S1[i] = np.mean(np.abs(du))
        S2[i] = np.mean(du ** 2)
        S3[i] = np.mean(du ** 3)
    tau_s = taus * dt
    c3 = S3 / tau_s                      # 4/5 律: = -(4/5)ε (常数)
    c2 = S2 / (tau_s ** (2.0 / 3.0))     # K41 补偿谱
    print("  τ[s]      S3/τ         S2/τ^{2/3}     dESS(1/3)")
    for i in range(len(taus)):
        # 局部 ESS 斜率 (相邻对数点)
        if 0 < i < len(taus) - 1:
            dS3 = np.log(S3[i + 1]) - np.log(S3[i - 1])
            dS1 = np.log(S1[i + 1]) - np.log(S1[i - 1])
            dess = dS1 / dS3 if abs(dS3) > 1e-12 else float("nan")
        else:
            dess = float("nan")
        print(f"  {tau_s[i]:8.4f}  {c3[i]:+.4e}  {c2[i]:.4e}  {dess:8.4f}")

    # --- 5. 多窗口 ESS 拟合 ---
    print("  ESS 窗口拟合 (ζ(1)/ζ(3), ζ(2)/ζ(3)):")
    for wlo, whi in [(0.01, 0.05), (0.02, 0.1), (0.05, 0.1), (0.05, 0.2),
                     (0.05, 0.5), (0.1, 0.5), (0.2, 0.5), (0.5, 2.0),
                     (0.05, 2.0), (0.002, 0.02)]:
        m = (tau_s >= wlo) & (tau_s <= whi)
        if m.sum() < 5:
            continue
        S = {1: S1[m], 2: S2[m], 3: S3[m]}
        x = np.log(S[3])
        a1 = float(np.polyfit(x, np.log(S[1]), 1)[0])
        a2 = float(np.polyfit(x, np.log(S[2]), 1)[0])
        print(f"    τ∈[{wlo:g},{whi:g}]s  r∈[{U0*wlo:.2f},{U0*whi:.2f}]m"
              f"  npts={int(m.sum()):2d}  α_u={a1:.4f}  ζ2/ζ3={a2:.4f}")
    print()
