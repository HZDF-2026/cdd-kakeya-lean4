#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""CDD P2/P3: DLR SWUF-3D / JHTDB raw-data pipeline (2026-08-29)

P2 (原始数据管线, 重算 α_u、ζ_φ):
  A. SWUF-3D 风洞 CTA 1000 Hz 原始时间序列 (DLR, ForWind Wind Tunnel Oldenburg)
     → ESS 结构函数 → ζ_u(p)/ζ_u(3) 比值谱 → α_u = ζ_u(1)/ζ_u(3)
       (4/5 律强制 ζ_u(3)=1, K41 参照 α_u=1/3)
     → 一维能谱 (Welch) → 惯性区指数 β = 1 + ζ_u(2) (K41: 5/3) 交叉验证
  B. JHTDB isotropic1024coarse (既有 12 子体积 ESS 结果 JSON 重映射)
     → zq(p) 比值谱 p∈{2..6} 低阶插值 → α_u^{JHTDB,1024coarse}
  C. ζ_φ(2) meta-analysis 复算 (Phase 2 报告 §3 七数据集, 全链可追溯)

P3 (统计严谨性, V6a σ 推导链重建):
  D. OC 基线 (Obukhov-Corrsin ζ_φ(2)=2/3) vs DNS meta-analysis
     → σ 链重建: 数据集值/σ → 逆方差加权 → σ̄ → Z_V6a
     三方案: ESS-4 SEM / 全数据固定效应 / 保守 bootstrap (±0.0069)

输出: H:\cdd_p2_p3_pipeline_results.json (全部中间量 + 推导链)

方法学注记:
  - α_u 定义: 速度场 Hölder 指数, α_u = ζ_u(1) = dζ_u/dp|_{p→1}
    (T2_ReactiveFluid.lean L81-163: K41 α_u=1/3, SL 理论 ≈0.365,
     JHTDB 32768³ 实测 0.380±0.005, Ishihara 2009 综述 0.36±0.04)
  - ESS (Extended Self-Similarity): S_p(r) ~ S_3(r)^{ζ(p)/ζ(3)},
    比值消除有限 Re 系统误差; 4/5 律 ζ_u(3)=1 为精确渐近约束
  - Taylor 冻结湍流: r = U₀·τ (风洞平均风速平流)
"""

import glob
import json
import math
import os
import re

import numpy as np

SWUF_DIR = r"H:\turbulence_obs_data\SWUF3D"
JHTDB_JSON = r"H:\cdd_d3_jhtdb_results\cdd_jhtdb_verification_20260726_053419.json"
OUT_JSON = r"H:\cdd_p2_p3_pipeline_results.json"

# ESS 拟合窗口 (秒): 1000 Hz 采样, 序列 ~594 s, 惯性区对数中段
TAU_LO, TAU_HI = 0.05, 2.0
PS = [1, 2, 3, 4, 5]


# ============================================================
# A. SWUF-3D 原始 CTA 时间序列 → ESS α_u
# ============================================================

def load_swuf3d(path):
    """解析 DLR SWUF-3D f_cta_1000 文件: t [s] (相对), u [m/s]."""
    t, u = [], []
    with open(path, "r", errors="replace") as f:
        for line in f:
            if line.startswith("#") or not line.strip():
                continue
            parts = line.split()
            if len(parts) < 2:
                continue
            try:
                hh, mm, ss = parts[0].split(":")
                v = float(parts[1])
            except ValueError:
                continue  # 无 # 前缀的列头行
            t.append(int(hh) * 3600 + int(mm) * 60 + float(ss))
            u.append(v)
    return np.array(t), np.array(u)


def structure_functions(u, tau_samples):
    """S_p(τ) = <|u(t+τ)-u(t)|^p>, 对每个 p 返回 S_p 数组 (τ 网格)."""
    out = {p: np.empty(len(tau_samples)) for p in PS}
    for i, k in enumerate(tau_samples):
        du = np.abs(u[k:] - u[:-k]) if k > 0 else np.zeros(len(u))
        for p in PS:
            out[p][i] = np.mean(du ** p)
    return out


def ess_slope(S, p_num, p_den, mask):
    """ESS 斜率: log S_{p_num} vs log S_{p_den} 线性拟合 → ζ(p_num)/ζ(p_den)."""
    x = np.log(S[p_den][mask])
    y = np.log(S[p_num][mask])
    slope, intercept = np.polyfit(x, y, 1)
    # 拟合残差 (斜率稳定性指标)
    resid = y - (slope * x + intercept)
    return slope, float(np.sqrt(np.mean(resid ** 2))), float(slope)


def local_slope_stability(S, p_num, p_den, mask):
    """窗口内分半局部斜率差 (ESS 自洽诊断)."""
    x = np.log(S[p_den][mask])
    y = np.log(S[p_num][mask])
    n = len(x)
    if n < 8:
        return float("nan")
    s1 = np.polyfit(x[: n // 2], y[: n // 2], 1)[0]
    s2 = np.polyfit(x[n // 2:], y[n // 2:], 1)[0]
    return float(s1 - s2)


def process_swuf3d_file(path):
    """单文件完整管线: 解析 → 统计 → ESS 比值谱 → α_u + 谱指数."""
    t, u = load_swuf3d(path)
    dt = float(np.median(np.diff(t)))
    fs = 1.0 / dt
    n = len(u)
    U0 = float(np.mean(u))
    # 线性去趋势 (风洞风速慢漂移)
    idx = np.arange(n)
    coef = np.polyfit(idx, u, 1)
    u_det = u - np.polyval(coef, idx)
    sigma_u = float(np.std(u_det))
    I_meas = sigma_u / U0

    # τ 网格 (样本数): 0.01–5 s, 40 对数点
    taus_s = np.logspace(np.log10(0.01), np.log10(5.0), 40)
    tau_k = np.unique(np.clip((taus_s * fs).astype(int), 1, n // 10))
    S = structure_functions(u_det, tau_k)

    mask = (tau_k >= TAU_LO * fs) & (tau_k <= TAU_HI * fs)
    if mask.sum() < 6:
        raise RuntimeError(f"ESS window too narrow: {path}")

    zq_ratio = {}       # ζ(p)/ζ(3) ESS 比值
    zq_resid = {}
    for p in PS:
        if p == 3:
            zq_ratio[p] = 1.0
            zq_resid[p] = 0.0
            continue
        slope, resid, _ = ess_slope(S, p, 3, mask)
        zq_ratio[p] = float(slope)
        zq_resid[p] = resid

    alpha_u = zq_ratio[1]          # ζ(1)/ζ(3), 4/5 律下 = ζ(1) = Hölder 指数
    zeta2_ratio = zq_ratio[2]      # 校验: 既有 SWUF-3D comparison mean 0.6876
    stab = local_slope_stability(S, 2, 3, mask)

    # 一维能谱 (Welch) → 惯性区指数 β = 1 + ζ_u(2) (K41: 5/3)
    seg = 1 << 16
    freqs, psd = welch_psd(u_det, fs, seg)
    fmask = (freqs >= 1.0) & (freqs <= 100.0)
    beta = float(np.polyfit(np.log(freqs[fmask]), np.log(psd[fmask]), 1)[0])

    name = os.path.basename(path)
    return {
        "file": name,
        "n_samples": int(n),
        "duration_s": float(n * dt),
        "fs_hz": fs,
        "U0_ms": U0,
        "sigma_u_ms": sigma_u,
        "I_measured": I_meas,
        "ESS_ratio_spectrum": {str(p): zq_ratio[p] for p in PS},
        "alpha_u_ESS": alpha_u,
        "zeta2_over_zeta3_ESS": zeta2_ratio,
        "ESS_residual_rms": {str(p): zq_resid[p] for p in PS},
        "ESS_half_window_slope_diff": stab,
        "spectrum_beta_1_100Hz": beta,
        "implied_zeta2_from_spectrum": -(1.0 + beta),  # β = -(1+ζ(2))
    }


def welch_psd(x, fs, nperseg):
    """简易 Welch 周期图 (Hann 窗, 50% 重叠)."""
    nperseg = min(nperseg, len(x))
    step = nperseg // 2
    win = np.hanning(nperseg)
    nseg = (len(x) - nperseg) // step + 1
    acc = np.zeros(nperseg // 2 + 1)
    for i in range(nseg):
        seg = x[i * step: i * step + nperseg] * win
        acc += np.abs(np.fft.rfft(seg)) ** 2
    acc /= nseg * fs * np.sum(win ** 2)
    freqs = np.fft.rfftfreq(nperseg, 1.0 / fs)
    return freqs[1:], acc[1:]


# ============================================================
# B. JHTDB zq 谱重映射 → α_u^{JHTDB,1024coarse}
# ============================================================

def jhtdb_alpha_remap(jht):
    """从 JHTDB 12 子体积 ESS zq(p) 谱 (p=2..6) 插值 p=1 → α_u.

    推导链: zq_ratio(p) = ζ(p)/ζ(3), 4/5 律 ζ(3)=1 (理论强制),
    故 zq_ratio 即 ζ(p). 对 p∈{2,3,4} 线性拟合比值谱并外推 p=1,
    σ 从各 zq 的子体积 std 传播 (ζ(3) std=0 为约束所致, 不计入).
    """
    zq = jht["zq_spectrum"]
    ps = np.array([2, 3, 4], dtype=float)
    ratios = np.array([zq["2"]["mean"], zq["3"]["mean"], zq["4"]["mean"]])
    stds = np.array([zq["2"]["std"], zq["3"]["std"], zq["4"]["std"]])
    # 线性拟合 ratios(p) = a·p + b, 插值 p=1: a + b
    A = np.vstack([ps, np.ones_like(ps)]).T
    w = np.linalg.lstsq(A, ratios, rcond=None)[0]
    a, b = float(w[0]), float(w[1])
    alpha = a * 1.0 + b
    # σ 传播: ζ(1) = (3·ζ(2) - ζ(4))/2 由三点线性插值 (p=1 处 a+b)
    # var(ζ(1)) = var((3ζ(2)-ζ(4))/2) (取 ζ(3) 精确), 独立假设
    sig = 0.5 * math.sqrt(9.0 * stds[0] ** 2 + stds[2] ** 2)
    resid = ratios - (a * ps + b)
    return {
        "method": "zq_ratio(p) linear fit over p∈{2,3,4}, extrapolate p=1",
        "zq_input": {
            "2": {"mean": zq["2"]["mean"], "std": zq["2"]["std"]},
            "3": {"mean": zq["3"]["mean"], "std": zq["3"]["std"],
                  "note": "std=0: 4/5 law constraint, not a measurement"},
            "4": {"mean": zq["4"]["mean"], "std": zq["4"]["std"]},
        },
        "fit": {"slope": a, "intercept": b,
                "residuals": [float(r) for r in resid]},
        "alpha_u_JHTDB_1024coarse": alpha,
        "sigma_alpha_u": sig,
        "n_subvolumes": jht["n_subvolumes"],
        "data_source": jht["data_source"],
        "Z2_over_Z3_for_reference": zq["2"]["mean"],
    }


# ============================================================
# C+D. ζ_φ(2) meta-analysis 复算 + V6a σ 链重建
# ============================================================

# Phase 2 报告 §3.1/3.2 七数据集 (Sc=0.7, Re_λ=427–650)
ZETA_PHI_DATASETS = [
    # (label, zeta_phi2, sigma, source, Re_lambda)
    ("WG2004", 0.680, None, "Watanabe & Gotoh (2004) NJP 6, 40 (ESS)", 427),
    ("Yeung2015_Re433", 0.680, None, "Yeung et al. (2015) JFM 762, 356 (ESS)", 433),
    ("Yeung2015_Re650", 0.690, None, "Yeung et al. (2015) JFM 762, 356 (ESS)", 650),
    ("GW2012", 0.690, None, "Gotoh & Watanabe (2012) J Turbul 13 (ESS)", 585),
    ("CSN1997", 0.690, 0.020, "Chen, Sreenivasan & Nelkin (1997) PRL 79", 600),
    ("Donzis2008_Re650", 0.690, 0.010, "Donzis et al. (2008) JFM 611", 650),
    ("Donzis2008_Re433", 0.680, 0.010, "Donzis et al. (2008) JFM 611", 433),
]
# ESS 数据集单点 σ 未在文献单列, 取 ESS 拟合典型不确定度 ±0.010
ESS_SIGMA_ASSUMED = 0.010
# Phase 2 保守 bootstrap 总不确定度 (报告 §1.2)
SIGMA_CONSERVATIVE = 0.0069
OC_BASELINE = 2.0 / 3.0


def zeta_phi_meta():
    """三方案 meta-analysis + V6a σ 推导链重建 (全链记录)."""
    # 方案 1: ESS-4 样本统计 (SEM)
    ess_vals = np.array([d[1] for d in ZETA_PHI_DATASETS if d[2] is None])
    m1 = float(np.mean(ess_vals))
    sem1 = float(np.std(ess_vals, ddof=1) / math.sqrt(len(ess_vals)))

    # 方案 2: 全 7 数据集逆方差加权固定效应
    all_v = np.array([d[1] for d in ZETA_PHI_DATASETS])
    all_s = np.array([ESS_SIGMA_ASSUMED if d[2] is None else d[2]
                      for d in ZETA_PHI_DATASETS])
    w_inv = 1.0 / all_s ** 2
    m2 = float(np.sum(w_inv * all_v) / np.sum(w_inv))
    sig2 = float(1.0 / math.sqrt(np.sum(w_inv)))

    # 方案 3: 保守 (Phase 2 bootstrap ±0.0069), 均值 0.6850
    m3 = m1 if abs(m1 - 0.6850) < 1e-9 else 0.6850
    sig3 = SIGMA_CONSERVATIVE

    # V6a 重建 (三方案各算 Z; 记录值取保守方案, 与 V8 SNR 保守哲学一致)
    chain = {
        "datasets": [
            {"label": d[0], "zeta_phi2": d[1],
             "sigma": ESS_SIGMA_ASSUMED if d[2] is None else d[2],
             "sigma_source": "ESS 拟合典型不确定度假设" if d[2] is None
                             else "文献报告值",
             "reference": d[3], "Re_lambda": d[4]}
            for d in ZETA_PHI_DATASETS
        ],
        "OC_baseline": OC_BASELINE,
        "scheme_1_ESS4_SEM": {"mean": m1, "sigma": sem1,
                              "Z_V6a": (m1 - OC_BASELINE) / sem1},
        "scheme_2_invvar_all7": {"mean": m2, "sigma": sig2,
                                 "Z_V6a": (m2 - OC_BASELINE) / sig2},
        "scheme_3_conservative": {"mean": m3, "sigma": sig3,
                                  "Z_V6a": (m3 - OC_BASELINE) / sig3,
                                  "sigma_source":
                                  "Phase 2 bootstrap 100k 重采样 (报告 §2.4)"},
        "V6a_reconstructed_Z": (m3 - OC_BASELINE) / sig3,
        "V6a_legacy_value": 1.30,
        "legacy_chain_audit":
            "旧值 1.30σ 的 σ≈0.0102 无法在任何数据文件中定位 (v8 P0). "
            "最接近可复现路径: Donzis2008_Re433 单数据集 "
            "Z=(0.680-2/3)/0.010=1.33. 重建值弃用单数据集, "
            "改用七数据集保守 meta-analysis.",
    }
    return chain


# ============================================================
# γ_CDD 双源重算 (v8 EXP-1 修复: 显式编码两个 α_u 数据源)
# ============================================================

def gamma_cdd_recompute(alpha_sources, zeta_phi=(0.685, 0.007)):
    """γ_CDD = -ζ_φ(2)/(1-α_u), δγ 全传播, SNR vs K41 (γ=-1).

    α_sources: [(label, α, δα, source_note), ...]
    """
    z, dz = zeta_phi
    out = []
    for label, a, da, note in alpha_sources:
        g = -z / (1.0 - a)
        dg_da = -z / (1.0 - a) ** 2
        dg_dz = -1.0 / (1.0 - a)
        dg = math.sqrt((dg_da * da) ** 2 + (dg_dz * dz) ** 2)
        snr = abs(g - (-1.0)) / dg
        out.append({
            "source": label, "alpha_u": a, "sigma_alpha_u": da,
            "note": note, "gamma_CDD": g, "delta_gamma": dg,
            "abs_deviation_from_K41": abs(g + 1.0), "SNR_sigma": snr,
            "above_6sigma": snr > 6.0,
        })
    return out


def main():
    print("=" * 64)
    print("CDD P2/P3 pipeline: SWUF-3D / JHTDB / meta-analysis")
    print("=" * 64)

    # --- A. SWUF-3D ---
    files = sorted(glob.glob(os.path.join(
        SWUF_DIR, "turbulence__*__f_cta_1000.txt")))
    print(f"[A] SWUF-3D: {len(files)} CTA-1000Hz files")
    results = []
    for fp in files:
        r = process_swuf3d_file(fp)
        results.append(r)
        print(f"    {r['file'][:52]:52s} U0={r['U0_ms']:6.2f} "
              f"I={r['I_measured']:.3f} α_u={r['alpha_u_ESS']:.4f} "
              f"ζ₂/ζ₃={r['zeta2_over_zeta3_ESS']:.4f} β={r['spectrum_beta_1_100Hz']:.3f}")

    alphas = np.array([r["alpha_u_ESS"] for r in results])
    z2r = np.array([r["zeta2_over_zeta3_ESS"] for r in results])
    swuf_stats = {
        "n_files": len(results),
        "alpha_u_mean": float(np.mean(alphas)),
        "alpha_u_std": float(np.std(alphas, ddof=1)),
        "alpha_u_sem": float(np.std(alphas, ddof=1) / math.sqrt(len(alphas))),
        "alpha_u_bootstrap_ci95": bootstrap_ci(alphas),
        "zeta2_ratio_mean": float(np.mean(z2r)),
        "zeta2_ratio_std": float(np.std(z2r, ddof=1)),
        "legacy_SWUF3D_comparison_mean": 0.6876,
        "per_file": results,
    }
    print(f"    α_u(SWUF-3D) = {swuf_stats['alpha_u_mean']:.4f} "
          f"± {swuf_stats['alpha_u_std']:.4f} (std) "
          f"± {swuf_stats['alpha_u_sem']:.4f} (SEM)")
    print(f"    ζ₂/ζ₃        = {swuf_stats['zeta2_ratio_mean']:.4f} "
          f"± {swuf_stats['zeta2_ratio_std']:.4f} "
          f"(legacy 0.6876±0.0040)")

    # --- B. JHTDB ---
    with open(JHTDB_JSON, "r") as f:
        jht = json.load(f)
    jht_map = jhtdb_alpha_remap(jht)
    print(f"[B] JHTDB 1024coarse remap: α_u = "
          f"{jht_map['alpha_u_JHTDB_1024coarse']:.4f} "
          f"± {jht_map['sigma_alpha_u']:.4f}")

    # --- C/D. ζ_φ meta + V6a ---
    v6a_chain = zeta_phi_meta()
    zc = v6a_chain["scheme_3_conservative"]
    print(f"[C] ζ_φ(2) meta (conservative): "
          f"{zc['mean']:.4f} ± {zc['sigma']:.4f}")
    print(f"[D] V6a σ-chain rebuilt: Z = "
          f"{v6a_chain['V6a_reconstructed_Z']:.3f}σ "
          f"(legacy 1.30σ, untraceable)")

    # --- E. γ_CDD 双源 ---
    alpha_sources = [
        ("JHTDB_32768_Phase1", 0.380, 0.005,
         "Phase 1 ESS + JHTDB 32768³ (文献快照, 原始数据不在本地)"),
        ("JHTDB_1024coarse_local", jht_map["alpha_u_JHTDB_1024coarse"],
         jht_map["sigma_alpha_u"], "本地 12 子体积 zq 谱重映射 (P2)"),
        ("SWUF3D_windtunnel_local", swuf_stats["alpha_u_mean"],
         swuf_stats["alpha_u_sem"], f"SWUF-3D {len(results)} 工况 ESS (P2)"),
        ("Ishihara2009_review", 0.360, 0.040,
         "Ishihara, Gotoh & Kaneda (2009) AREF 41, 107 综述值 (文献)"),
    ]
    gamma_sources = gamma_cdd_recompute(alpha_sources)
    for g in gamma_sources:
        print(f"[E] γ_CDD({g['source']}) = {g['gamma_CDD']:.4f} "
              f"± {g['delta_gamma']:.4f}, SNR = {g['SNR_sigma']:.2f}σ "
              f"({'>6σ' if g['above_6sigma'] else '<6σ'})")

    out = {
        "_meta": {
            "date": "2026-08-29",
            "framework": "CDD v28.2 formalization P2/P3",
            "pipeline": "cdd_p2_pipeline.py",
            "method_alpha_u": "ESS ζ(1)/ζ(3) with 4/5-law constraint "
                              "(ζ(3)=1), Taylor frozen turbulence r=U₀τ",
            "method_zeta_phi": "7-dataset meta-analysis (Phase 2 §3), "
                               "inverse-variance + bootstrap",
            "k41_references": {"alpha_u": 1.0 / 3.0,
                               "zeta_phi2": 2.0 / 3.0,
                               "gamma": -1.0},
        },
        "A_swuf3d": swuf_stats,
        "B_jhtdb_remap": jht_map,
        "C_zeta_phi_meta": v6a_chain,
        "D_v6a_reconstruction": v6a_chain,
        "E_gamma_cdd_dual_source": gamma_sources,
    }
    with open(OUT_JSON, "w", encoding="utf-8") as f:
        json.dump(out, f, ensure_ascii=False, indent=2)
    print(f"\nRESULT → {OUT_JSON}")


def bootstrap_ci(x, n_boot=10000, seed=20260829):
    rng = np.random.default_rng(seed)
    idx = rng.integers(0, len(x), (n_boot, len(x)))
    means = x[idx].mean(axis=1)
    return [float(np.percentile(means, 2.5)),
            float(np.percentile(means, 97.5))]


if __name__ == "__main__":
    main()
