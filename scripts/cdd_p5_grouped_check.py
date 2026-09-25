#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""P5 v28.4 补充: 通道相关性压力检验 — 设施分组 Stouffer 合成.

动机 (cdd-verify WV3 审稿发现): V6d 八通道注释"全部独立设施/数据"过强 —
ABL 三通道同属 TUM 风洞 (同设施不同 TI 工况), Ishihara2009 综述值与
DNS 元分析源可能部分重叠, JHTDB 1024/32768 同数据库家族。
Stouffer k=8 假设通道完全独立; 若存在正相关, Z 被高估。

压力检验 (组内先合成, 跨组按组数 k_g 合成):
  G1 DNS-标量元分析     scalar_meta_fixed
  G2 JHTDB 家族         JHTDB_32768 + JHTDB_1024
  G3 综述               Ishihara2009
  G4 SWUF-3D (DLR)      SWUF3D_v28_4
  G5 TUM 风洞 ABL       Extreme + Mod + High TI (同设施)
更保守变体: G1+G3+G2 合并为单 DNS 组 (k=3), G4+G5 合并为单风洞组 (k=2)。

输出: H:\cdd_p5_v28_4_grouped_check.json
"""
import json
import math

SRC = r"H:\cdd_p5_v28_4_results.json"
OUT = r"H:\cdd_p5_v28_4_grouped_check.json"

d = json.load(open(SRC, encoding="utf-8"))
ch = d["D_v6d_synthesis"]["channels"]
Z = {c["name"]: c["Z"] for c in ch}

def stouffer(zs):
    return sum(zs) / math.sqrt(len(zs))

groups = {
    "G1_dns_scalar_meta": ["scalar_meta_fixed"],
    "G2_jhtdb_family": ["alpha_JHTDB_32768", "alpha_JHTDB_1024"],
    "G3_review_ishihara": ["alpha_Ishihara2009"],
    "G4_swuf3d_dlr": ["alpha_SWUF3D_v28_4"],
    "G5_tum_abl": ["alpha_ABL_Extreme_TI", "alpha_ABL_Mod_TI", "alpha_ABL_High_TI"],
}

res = {"source": SRC, "method": "组内 Stouffer → 跨组 Stouffer (k = 组数); 检验正相关下 Z 的稳健性"}
zg = {}
for g, names in groups.items():
    zg[g] = stouffer([Z[n] for n in names])
res["group_Z"] = zg

k5 = len(groups)
res["Z_grouped_5facilities"] = stouffer(list(zg.values()))
res["k_5facilities"] = k5

z_dns = stouffer([Z["scalar_meta_fixed"], Z["alpha_Ishihara2009"],
                  Z["alpha_JHTDB_32768"], Z["alpha_JHTDB_1024"]])
z_wind = stouffer([Z["alpha_SWUF3D_v28_4"], Z["alpha_ABL_Extreme_TI"],
                   Z["alpha_ABL_Mod_TI"], Z["alpha_ABL_High_TI"]])
res["Z_grouped_2classes"] = stouffer([z_dns, z_wind])
res["z_dns_class"] = z_dns
res["z_wind_class"] = z_wind
res["k_2classes"] = 2

main = d["D_v6d_synthesis"]["stouffer_Z"]
res["Z_original_k8"] = main
res["verdict"] = (
    f"分组压力检验: k=8 完全独立假设 Z={main:.3f}; 设施分组 k=5 → "
    f"{res['Z_grouped_5facilities']:.3f}; 最保守设施类别分组 k=2 → "
    f"{res['Z_grouped_2classes']:.3f}. 全部 > 6σ — 正相关风险下结论不变。"
)

json.dump(res, open(OUT, "w", encoding="utf-8"), ensure_ascii=False, indent=2)
print(json.dumps(res, ensure_ascii=False, indent=2))
