# -*- coding: utf-8 -*-
import json
a = json.load(open(r"H:\cdd_atmosphere_6sigma_validation_results_v2.json", encoding="utf-8"))
a3 = a["A3"]
print("keys:", list(a3.keys()))
for k in ("gamma_pred", "gamma_ocean", "sigma_gamma", "Z_vs_K41", "Z_cross_validation"):
    if k in a3:
        print(f" {k} = {a3[k]}")
zc = abs(a3["gamma_pred"] - a3["gamma_ocean"]) / a3["sigma_gamma"]
print("recomputed |gp-go|/s =", round(zc, 9))
print("recorded Z_cross_val =", a3["Z_cross_validation"])
print("diff =", round(abs(zc - a3["Z_cross_validation"]), 9))
zk = abs(a3["gamma_pred"] - (-1.0)) / a3["sigma_gamma"]
print("recomputed Z_vs_K41 =", round(zk, 9), " recorded =", a3.get("Z_vs_K41"))
# try alternative sigma: maybe sigma from combining both sigma fields
o = json.load(open(r"H:\cdd_ocean_dns_validation_v2_results.json", encoding="utf-8"))
r = o["V3_multifractal"]["results"][0]  # Sc=0.7 Re 433
print("ocean V3 Sc=0.7 sigma_gamma =", r["sigma_gamma"])
# combined sigma?
import math
s_c = math.sqrt(a3["sigma_gamma"]**2 + r["sigma_gamma"]**2)
print("combined sigma =", s_c, "-> Z =", abs(a3["gamma_pred"] - a3["gamma_ocean"]) / s_c)
