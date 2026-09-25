# -*- coding: utf-8 -*-
"""Verify D2/D3/D4 claims against the actual JSON files (round D audit)."""
import json
import math

# ---- D2: fusion F_combined vs F1 ----
f = json.load(open(r"H:\cdd_fusion_6sigma_validation_results_v2.json", encoding="utf-8"))
f1 = f["F1"]
f2 = f["F2"]
fc = f["F_combined"]
print("=== D2 fusion ===")
print("F1.Z_combined      =", f1.get("Z_combined"))
print("F1 supersedes      =", f1.get("supersedes"))
print("F_combined ind[0] Z=", fc["individual_Z"][0]["Z"])
print("F_combined ind[1] Z=", fc["individual_Z"][1]["Z"])
print("Z_direct recorded  =", fc.get("Z_direct"))
old = math.sqrt(fc["individual_Z"][0]["Z"]**2 + fc["individual_Z"][1]["Z"]**2)
new = math.sqrt(f1["Z_combined"]**2 + f2["Z_combined"]**2)
print("sqrt(a^2+b^2) from ind list =", round(old, 6))
print("sqrt(F1^2+F2^2) from fresh  =", round(new, 6))
print("=> mismatch" if abs(old - fc["Z_direct"]) > 1e-9 else "=> consistent with ind list")

# ---- D3: ocean V3 six conditions ----
o = json.load(open(r"H:\cdd_ocean_dns_validation_v2_results.json", encoding="utf-8"))
v3 = o.get("V3_multifractal")
print("\n=== D3 ocean V3 ===")
if isinstance(v3, dict):
    cases = v3.get("cases") or v3.get("runs") or v3
else:
    cases = v3
vals = []
if isinstance(cases, list):
    for c in cases:
        print(" case:", {k: c[k] for k in c if k in ("Sc", "Re_lambda", "Re_lam", "Z_vs_K41")})
        if "Z_vs_K41" in c:
            vals.append(c["Z_vs_K41"])
elif isinstance(cases, dict):
    for k, v in cases.items():
        z = v.get("Z_vs_K41") if isinstance(v, dict) else v
        print(f" {k}: Z_vs_K41 = {z}")
        if z is not None:
            vals.append(z)
print("centi values (x100 rounded):", [round(z * 100) for z in vals])
print("max:", round(max(vals) * 100) if vals else "n/a")

# ---- D4: atmosphere A3 ----
a = json.load(open(r"H:\cdd_atmosphere_6sigma_validation_results_v2.json", encoding="utf-8"))
a3 = a.get("A3")
print("\n=== D4 atmosphere A3 ===")
for k in ("gamma_pred", "gamma_ocean", "sigma_gamma", "Z_vs_K41", "Z_cross_validation"):
    if k in a3:
        print(f" {k} = {a3[k]}")
if all(k in a3 for k in ("gamma_pred", "gamma_ocean", "sigma_gamma")):
    zc = abs(a3["gamma_pred"] - a3["gamma_ocean"]) / a3["sigma_gamma"]
    print(" recomputed |gp-go|/s =", round(zc, 6),
          " recorded =", a3.get("Z_cross_validation"))
    print(" Z_vs_K41 recomputed =",
          round(abs(a3["gamma_pred"] - (-1.0)) / a3["sigma_gamma"], 6))
print("\nkeys A3:", list(a3.keys()))
