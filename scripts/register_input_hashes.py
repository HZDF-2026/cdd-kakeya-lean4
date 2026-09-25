# register_input_hashes.py - A4.2 原始输入数据哈希锁定 (2026-08-30)
# 对象: P5/P2 管线的全部本地原始输入 (SWUF-3D / ABL / JHTDB ESS JSON) + 源压缩包
# 输出: H:\cdd_lean4\raw_input_data_hashes.json (版本化清单, DataProvenance.lean §6 登记对象)
# 注意: 本脚本只读不改, 不触碰已冻结的 cdd_p5_v28_4_results.json 等结果快照
import hashlib
import json
import os
import sys
from datetime import datetime

SWUF_DIR = r"H:\turbulence_obs_data\SWUF3D"
ABL_NC = {
    "Extreme-TI (35 探针)": r"H:\tmp\abl\DATA_test_4.nc",
    "Mod-TI (875 探针)": r"H:\tmp\abl\DATA_test_1.nc",
    "High-TI (480 探针)": r"H:\tmp\abl\DATA_test_2.nc",
}
JHTDB_JSON = r"H:\cdd_d3_jhtdb_results\cdd_jhtdb_verification_20260726_053419.json"
SOURCE_ARCHIVES = {
    "SWUF3D 分发包 (DLR)": os.path.join(SWUF_DIR, "dlr_swuf3d_windtunnel.zip"),
    "ABL 分发包 (TUM Inflow)": r"H:\turbulence_obs_data\ABL_WindTunnel\Inflow.zip",
}
OUT = r"H:\cdd_lean4\raw_input_data_hashes.json"

BLOCK = 1 << 20


def sha256_file(path):
    h = hashlib.sha256()
    n = 0
    with open(path, "rb") as f:
        while True:
            b = f.read(BLOCK)
            if not b:
                break
            h.update(b)
            n += len(b)
    return h.hexdigest().upper(), n


def entry(path, role):
    if not os.path.exists(path):
        return {"path": path, "role": role, "missing": True}
    digest, size = sha256_file(path)
    return {
        "file": os.path.basename(path),
        "path": path,
        "role": role,
        "bytes": size,
        "sha256": digest,
    }


def main():
    import glob as globmod
    manifest = {
        "_meta": {
            "date": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            "purpose": ("改良清单 A4.2 (P1): 原始输入数据哈希锁定。"
                        "登记对象 = cdd_p5_theory_advance_v28_4.py / cdd_p2_pipeline.py "
                        "的全部本地原始输入; DataProvenance.lean §6 为其 Lean 注册表。"),
            "method": "SHA256 (Python hashlib, 逐文件全量读取)",
            "pipeline_scripts": [
                "H:\\cdd_lean4\\scripts\\cdd_p5_theory_advance_v28_4.py",
                "H:\\cdd_lean4\\scripts\\cdd_p2_pipeline.py",
            ],
            "frozen_snapshots_untouched": [
                "H:\\cdd_p5_v28_4_results.json (SHA256 已登记于 DataProvenance §5, 不修改)",
                "H:\\cdd_p2_p3_pipeline_results.json (同上)",
            ],
            "location_caveat": ("ABL nc 提取件位于 H:\\tmp\\abl (临时目录), "
                                "持久层为 Inflow.zip (本清单已登记其哈希); "
                                "建议后续将 nc 提取件迁至 turbulence_obs_data。"),
        },
        "A_swuf3d_cta1000": {
            "dir": SWUF_DIR,
            "glob": "turbulence__*__f_cta_1000.txt",
            "pipeline_ref": "cdd_p5_theory_advance_v28_4.py L530-531 (SWUF_DIR glob)",
            "expected_count": 19,
            "window_diagnostic_passed": 9,
            "files": [],
        },
        "B_abl_windtunnel_nc": {
            "pipeline_ref": "cdd_p5_theory_advance_v28_4.py L47-51 (ABL_NC dict)",
            "files": [],
        },
        "C_jhtdb_1024coarse_ess_json": {
            "pipeline_ref": "cdd_p2_pipeline.py L39 (JHTDB_JSON)",
            "raw_data_status": ("JHTDB isotropic1024coarse 原始速度场不在本地 "
                                "(来源 http://turbulence.idies.jhu.edu); "
                                "本地输入为 12 子体积 ESS zq 谱统计 JSON。"),
            "files": [],
        },
        "D_source_archives": {"files": []},
        "E_not_local_literature_only": {
            "JHTDB_32768": ("文献快照 α_u = 0.380 ± 0.005 "
                            "(P5 JSON A 段: 'Phase 1 ESS + JHTDB 32768³ 文献快照, 原始数据不在本地'); "
                            "溯源链止于文献值, 无本地文件可哈希。"),
            "Ishihara2009": "综述值 α_u = 0.36 ± 0.04 (Annu. Rev. Fluid Mech. 41, 165), 文献参数。",
        },
    }

    swuf_files = sorted(globmod.glob(os.path.join(
        SWUF_DIR, "turbulence__*__f_cta_1000.txt")))
    print(f"[A] SWUF-3D CTA-1000: {len(swuf_files)} files ...")
    for p in swuf_files:
        manifest["A_swuf3d_cta1000"]["files"].append(entry(p, "SWUF-3D 工况记录 (CTA 1000 Hz)"))
        print(f"    {os.path.basename(p)} ok")

    print("[B] ABL nc ...")
    for name, p in ABL_NC.items():
        manifest["B_abl_windtunnel_nc"]["files"].append(entry(p, f"ABL {name}"))
        print(f"    {os.path.basename(p)} ok")

    print("[C] JHTDB ESS JSON ...")
    manifest["C_jhtdb_1024coarse_ess_json"]["files"].append(
        entry(JHTDB_JSON, "JHTDB 1024coarse 12 子体积 ESS 统计 (P2 输入)"))
    print("    ok")

    print("[D] source archives ...")
    for name, p in SOURCE_ARCHIVES.items():
        manifest["D_source_archives"]["files"].append(entry(p, name))
        print(f"    {os.path.basename(p)} ok")

    n = (len(manifest["A_swuf3d_cta1000"]["files"])
         + len(manifest["B_abl_windtunnel_nc"]["files"])
         + len(manifest["C_jhtdb_1024coarse_ess_json"]["files"])
         + len(manifest["D_source_archives"]["files"]))
    missing = sum(1 for sec in "ABCD"
                  for f in manifest[f"{'A_swuf3d_cta1000' if sec=='A' else 'B_abl_windtunnel_nc' if sec=='B' else 'C_jhtdb_1024coarse_ess_json' if sec=='C' else 'D_source_archives'}"]["files"]
                  if f.get("missing"))
    manifest["_meta"]["total_files"] = n
    manifest["_meta"]["missing_files"] = missing
    manifest["_meta"]["swuf_count_check"] = (
        len(swuf_files) == manifest["A_swuf3d_cta1000"]["expected_count"])

    with open(OUT, "w", encoding="utf-8") as f:
        json.dump(manifest, f, indent=1, ensure_ascii=False)

    with open(OUT, "rb") as f:
        manifest_sha = hashlib.sha256(f.read()).hexdigest().upper()
    print(f"\nmanifest: {OUT}")
    print(f"total files = {n}, missing = {missing}, "
          f"swuf count check = {manifest['_meta']['swuf_count_check']}")
    print(f"manifest sha256 (自登记用): {manifest_sha}")
    return 0 if missing == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
