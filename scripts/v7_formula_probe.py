"""Reverse-engineer V7 Z_consistency = 4.099397153770709 from the frozen snapshot.

Reads the 9 individual_Z channels and tests standard meta-analytic
combination formulas to identify the one that reproduces the recorded
value exactly.  Read-only with respect to the frozen snapshot.
"""
import json
import math

SNAP = r"H:\cdd_ocean_dns_validation_v2_results.json"
d = json.load(open(SNAP))
v7 = d["V7_combined"]
target = v7["Z_consistency"]
ch = v7["individual_Z"]
cons = [c["Z"] for c in ch if c["type"] != "充分性"]
suff = [c["Z"] for c in ch if c["type"] == "充分性"]

# p-values: V3 six have explicit p_value fields; V4/V6 recomputed from Z.
v3_p = [r["p_value"] for r in d["V3_multifractal"]["results"]]


def phi(z):
    return 0.5 * (1 + math.erf(z / math.sqrt(2)))


def p_two(z):
    return 2 * (1 - phi(abs(z)))


def p_one(z):
    return 1 - phi(z)


v4_Z = [c["Z"] for c in ch if c["name"].startswith("V4")][0]
v6_Z = [c["Z"] for c in ch if c["name"].startswith("V6")][0]
p_all_two = v3_p + [p_two(v4_Z), p_two(v6_Z)]
p_all_one = [p_one(z) for z in cons]

n = len(cons)
sumZ = sum(cons)
sumZ2 = sum(z * z for z in cons)

print(f"target = {target!r}")
print(f"n_cons = {n}, sumZ = {sumZ!r}, sumZ2 = {sumZ2!r}")
print()

cands = {}

# Stouffer family
cands["stouffer n=8"] = sumZ / math.sqrt(n)
cands["stouffer n=7 (no V6)"] = (sumZ - v6_Z) / math.sqrt(n - 1)
cands["stouffer n=7 (no V4)"] = (sumZ - v4_Z) / math.sqrt(n - 1)
cands["stouffer all9"] = (sumZ + sum(suff)) / math.sqrt(n + 1)

# L2 family
cands["sqrt(sumZ2)"] = math.sqrt(sumZ2)
cands["sqrt(sumZ2/2)"] = math.sqrt(sumZ2 / 2)
cands["sqrt(sumZ2/8)*sqrt(8)"] = math.sqrt(sumZ2 / n) * math.sqrt(n)

# Fisher family
chi_two = -2 * sum(math.log(p) for p in p_all_two)
chi_one = -2 * sum(math.log(p) for p in p_all_one)
cands["fisher two -> sqrt(chi2/2)"] = math.sqrt(chi_two / 2)
cands["fisher one -> sqrt(chi2/2)"] = math.sqrt(chi_one / 2)
cands["fisher two -> sqrt(chi2)"] = math.sqrt(chi_two)
# Fisher minus one channel
chi_no_v6 = chi_two + 2 * math.log(p_two(v6_Z))
cands["fisher 7ch(no V6) sqrt(chi2/2)"] = math.sqrt(chi_no_v6 / 2)
chi_no_v4 = chi_two + 2 * math.log(p_two(v4_Z))
cands["fisher 7ch(no V4) sqrt(chi2/2)"] = math.sqrt(chi_no_v4 / 2)

# Weighted Stouffer with w = 1/sigma (V3 sigmas + DNS sigma for V4/V6)
v3_sig = [r["sigma_gamma"] for r in d["V3_multifractal"]["results"]]
sig_dns = d["V6_SL"]["sigma_gamma_DNS"]
w = [1 / s for s in v3_sig] + [1 / sig_dns, 1 / sig_dns]
zw = sum(wi * zi for wi, zi in zip(w, cons)) / math.sqrt(sum(wi * wi for wi in w))
cands["weighted stouffer 1/sigma"] = zw

# Weighted Stouffer with w = sqrt(n datasets) unknown; try equal 1
# max |Z|, mean |Z|
cands["max Z"] = max(cons)
cands["mean Z * sqrt(8)"] = (sumZ / n) * math.sqrt(n)

# chi-based normal approx
cands["(chi2-k)/sqrt(2k)"] = (chi_two - 2 * n) / math.sqrt(4 * n)
cands["sqrt(2 chi2)-sqrt(2k-1)"] = math.sqrt(2 * chi_two) - math.sqrt(2 * 2 * n - 1)

for name, val in cands.items():
    diff = abs(val - target)
    tag = "  <<< EXACT" if diff < 1e-9 else ("  ~close" if diff < 0.05 else "")
    print(f"{name:38s} = {val!r:24s} diff={diff:.6f}{tag}")

print()
print("p_all_two =", p_all_two)
print("chi_two =", chi_two)
