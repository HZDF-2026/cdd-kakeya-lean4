"""V7 联合一致性 OC 基线并入重算 (v9, 2026-08-30).

背景: 冻结快照 cdd_ocean_dns_validation_v2_results.json 的
V7_combined.Z_consistency = 4.099397 (8 一致性通道, 不含 OC 基线)
自 v8 起挂"pending recalculation" — 待将 v8 重建的 V6a OC 基线
(Z = 550/207, cdd_p2_p3_pipeline_results.json#D_v6a_reconstruction)
并入合成。本脚本执行该收口并生成新快照 v3 (冻结 v2 不就地修改)。

诚实边界: v2 的 Z_consistency 生成脚本未存盘, 其合成公式无法从
磁盘工件精确复现 (Stouffer-8ch = 3.930, Fisher-8ch = 4.120, 均
不等于 4.0994)。v9 起合成方法显式化为 Stouffer (Z = ΣZᵢ/√k,
与 cdd_p5_theory_advance_v28_4.py::stouffer 同一惯例), 输入哈希
在运行时强制核对 (不匹配即中止), 新快照全量登记。

用法: python cdd_v7_oc_recalc.py
输出: H:\cdd_ocean_dns_validation_v3_results.json (新冻结快照)
"""
import hashlib
import json
import math

V2_SNAP = r"H:\cdd_ocean_dns_validation_v2_results.json"
V2_SHA256 = ("B74B55A2131577AF5464CEAEFD1DB6F59131249"
             "AA3AEC72C97842F3715AAE832")
P2_SNAP = r"H:\cdd_p2_p3_pipeline_results.json"
P2_SHA256 = ("ACB004388E5DFF3AD9FBC85BBA5E2ADEBC20754"
             "B7BDEA5ECF73D318451DC5A97")
OUT = r"H:\cdd_ocean_dns_validation_v3_results.json"


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for blk in iter(lambda: f.read(1 << 20), b""):
            h.update(blk)
    return h.hexdigest().upper()


def phi(z):
    return 0.5 * (1 + math.erf(z / math.sqrt(2)))


def p_two(z):
    return 2 * (1 - phi(abs(z)))


# --- 门 1: 输入哈希强制核对 (冻结链条不可破坏) ---
h2, hp = sha256(V2_SNAP), sha256(P2_SNAP)
assert h2 == V2_SHA256, f"v2 snapshot hash drift: {h2}"
assert hp == P2_SHA256, f"p2 snapshot hash drift: {hp}"
print(f"[gate] v2 snapshot SHA256 OK  ({h2[:16]}...)")
print(f"[gate] p2 snapshot SHA256 OK  ({hp[:16]}...)")

v2 = json.load(open(V2_SNAP))
p2 = json.load(open(P2_SNAP))

# --- 通道提取 ---
chans = []
for c in v2["V7_combined"]["individual_Z"]:
    if c["type"] == "充分性":
        v2_suff = c
        continue
    chans.append({
        "name": c["name"], "Z": c["Z"], "type": "一致性",
        "source": "cdd_ocean_dns_validation_v2_results.json#V7_combined.individual_Z",
    })
v6a = p2["D_v6a_reconstruction"]["scheme_3_conservative"]
oc_z = v6a["Z_V6a"]
chans.append({
    "name": "V6a: OC 基线一致性 (七数据集保守 meta-analysis)",
    "Z": oc_z, "type": "一致性",
    "source": ("cdd_p2_p3_pipeline_results.json#D_v6a_reconstruction."
               "scheme_3_conservative.Z_V6a (mean 0.685, sigma 0.0069, "
               "OC 基线 2/3)"),
})
k = len(chans)
assert k == 9, f"channel count {k} != 9"

# --- 门 2: 旧值复算对照 (诚实记录, 非断言) ---
sum_z = sum(c["Z"] for c in chans)
z_new = sum_z / math.sqrt(k)
chi2 = -2 * sum(math.log(p_two(c["Z"])) for c in chans)
z_fisher = math.sqrt(chi2 / 2)
old = v2["V7_combined"]["Z_consistency"]
print(f"[recalc] k = {k}  sumZ = {sum_z:.9f}")
print(f"[recalc] Stouffer Z = {z_new:.9f}  -> centi {round(z_new * 100)}")
print(f"[recalc] Fisher chi2({2 * k}) = {chi2:.6f}  Z = {z_fisher:.6f}")
print(f"[old]    v2 Z_consistency = {old} (8ch, 公式未存盘, 不可复现)")

# --- 门 3: 一致性判据 (|Z| < 6σ) ---
assert z_new < 6.0, f"Stouffer Z {z_new} >= 6sigma"
assert z_fisher < 6.0, f"Fisher Z {z_fisher} >= 6sigma"
print(f"[gate] Stouffer {z_new:.4f} < 6σ 且 Fisher {z_fisher:.4f} < 6σ — 一致性结论两种合成法下均成立")

out = {
    "_meta": {
        "date": "2026-08-30",
        "revision": ("v9 P0 (2026-08-30): V7 OC 基线并入收口 "
                     "(T2_Validation F4 / improvement_suggestions E5 待办)"),
        "pipeline": "cdd_lean4/scripts/cdd_v7_oc_recalc.py",
        "inputs": [
            {"file": V2_SNAP, "sha256": h2,
             "role": "8 一致性通道 + V2 充分性 (冻结快照, 只读)"},
            {"file": P2_SNAP, "sha256": hp,
             "role": "V6a OC 基线 Z (D_v6a_reconstruction.scheme_3_conservative)"},
        ],
        "method": "Stouffer: Z = ΣZᵢ/√k, k=9 (6×V3 + V4 + V6_SL + V6a OC)",
        "method_convention": ("与 cdd_p5_theory_advance_v28_4.py::stouffer "
                              "同一惯例 (V6d 合成已验证)"),
        "honesty_note": ("v2 的 Z_consistency=4.099397 生成脚本未存盘, "
                         "合成公式不可精确复现 (Stouffer-8ch=3.930, "
                         "Fisher-8ch=4.120); v9 起方法显式化并登记本快照, "
                         "旧值保留于冻结 v2 快照作历史记录"),
    },
    "_criteria": {
        "consistent": "|Z| < 6σ: 理论预测与数据统计一致 — 一致性检验的通过标准, 不构成 6σ 级发现",
        "revision": "v9 P0 (2026-08-30): V7 OC 基线并入, 沿用 v8 判据语义",
    },
    "V7_combined_v3": {
        "test": "combined_significance",
        "individual_Z": chans + [{
            "name": v2_suff["name"], "Z": v2_suff["Z"], "type": "充分性",
            "source": "cdd_ocean_dns_validation_v2_results.json#V7_combined.individual_Z",
        }],
        "k_consistency": k,
        "sum_Z": sum_z,
        "Z_consistency": z_new,
        "Z_consistency_centi": round(z_new * 100),
        "Z_sufficiency": v2["V7_combined"]["Z_sufficiency"],
        "consistent": True,
        "fisher_robustness": {
            "chi2_df": 2 * k,
            "chi2": chi2,
            "Z_fisher": z_fisher,
            "note": "Fisher 合成稳健性复核 (双侧 p), 与 Stouffer 主方法并列报告",
        },
        "supersedes": {
            "file": "cdd_ocean_dns_validation_v2_results.json",
            "sha256": h2,
            "V7_Z_consistency": old,
            "k_consistency": 8,
            "note": "不含 V6a OC 通道; 生成脚本未存盘, 公式不可精确复现",
        },
    },
}

with open(OUT, "w", encoding="utf-8") as f:
    json.dump(out, f, ensure_ascii=False, indent=2)
    f.write("\n")

ho = sha256(OUT)
print(f"[done] new snapshot: {OUT}")
print(f"[done] SHA256 = {ho}")
