#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""R12-7 两层 MC 预演 (旧 JSON 数据, 与主管线同算法/同 seed, 预估 Z)."""
import json
import math

import numpy as np

d = json.load(open(r"H:\cdd_p5_v28_4_results.json", encoding="utf-8"))
pts = d["C_trajectory_v28_4"]["points"]
swuf_range = d["A_swuf3d_corrected"]["Re_lambda_range"]
RE_C = 433.0

rng = np.random.default_rng(20260829)
dd = np.array([p["delta"] for p in pts], float)
w = np.array([1.0 / p["sigma"] ** 2 for p in pts], float)


def make_prior(mode):
    pri = []
    for p in pts:
        if p["source"] == "SWUF-3D(v28.4)":
            if mode == "main":
                pri.append(("lognormal", float(p["Re_lambda"]), math.log(1.31)))
            else:
                pri.append(("loguniform", float(swuf_range[0]),
                            float(swuf_range[1])))
        elif p["source"].startswith("ABL-"):
            pri.append(("lognormal", float(p["Re_lambda"]), math.log(1.15)))
        else:
            pri.append(("lognormal", float(p["Re_lambda"]), math.log(1.05)))
    return pri


def run(prior, n_mc=20000):
    samples = np.empty(n_mc)
    for t in range(n_mc):
        g = np.empty(len(pts))
        for i, (kind, a, b) in enumerate(prior):
            if kind == "loguniform":
                re_i = math.exp(rng.uniform(math.log(a), math.log(b)))
            else:
                re_i = a * math.exp(rng.normal(0.0, b))
            g[i] = 1.0 - RE_C / re_i
        sw = float(np.sum(w * g ** 2))
        samples[t] = float(np.sum(w * g * dd) / sw)
    return samples


sig_stat = 0.004207298030339656
for mode in ("main", "stress"):
    s = run(make_prior(mode))
    sig_mc = float(np.std(s, ddof=1))
    d_mc = float(np.mean(s))
    sig_tot = math.sqrt(sig_stat ** 2 + sig_mc ** 2)
    print(f"[{mode:6s}] D∞_mc = {d_mc:.6f}  σ_横 = {sig_mc:.6f}  "
          f"σ_总 = {sig_tot:.6f}  Z = {d_mc/sig_tot:.3f}  "
          f">6σ: {d_mc/sig_tot > 6.0}")
