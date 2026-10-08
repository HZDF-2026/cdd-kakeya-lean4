# A2 预注册：CDD Γ/m 判据在 PDG 2026 官方字段上的操作化冻结 + 独立重数（2026-10-04）

状态：**冻结**（本文档先于重数脚本 `cdd_pdg_official_recount.py` 的编写与执行落盘）
纪律：判据与规则先冻结，后单轮执行重数；重数结果不得反向修改规则；重跑须新预注册轮次。

## 0. 任务定位

执行 `improvement_suggestions_20261004.md` §IV.A-A2（B7 可执行支线）：把 CDD 判据在 PDG 字段上操作化为冻结判定规则，独立重数，产出官方 vs CDD diff 表。落定前 `PP≈67.5%` 维持「CDD 自有分类」强制标注。

## 1. 两侧定义

- **官方侧（数据）**：本地 PDG 官方 sqlite（`pdg.sqlite`，edition **2026**，data release 2026-05-30，CC BY 4.0，与 pdg.lbl.gov API 同源）——即 CDD 理论文档自称所分类的同一版本。
- **加工路线（冻结）**：已登记的 `H:\cdd-vs-science\pdg_extract.py` v2 提取协议（递归树展开；值类型优先级 AC>FIT>E>V；上限/下限/排除值剔除；区间宽度取中值；单位统一 GeV；ℏ/τ 换算；反粒子合并）→ `H:\cdd-vs-science\pdg_particles.json`（396 family）。重数脚本**消费该冻结提取物**（单一加工路线，不做并行二次提取），其 SHA256 入登记。
- **CDD 侧（声称）**：`cdd_theory_zh.html` §4.1/§4.5：289 粒子 → PP 195 / SC 83 / AC 11；PP↔SC 间隙因子 1.08x，SC↔AC 间隙因子 1.07x，「跨界粒子数 0」；PP 细分（稳定 ~20 / 极窄 <0.01 ~100 / 窄 0.01–0.05 ~75）。

## 2. 冻结的操作化规则

**判据（理论文档定义 4.1 原文数值，边界归属按 SC 区间闭）**：
- PP：Γ/m < 0.05
- SC：0.05 ≤ Γ/m ≤ 0.2
- AC：Γ/m > 0.2

**Scope**：`pdg_particles.json` 全部 `mass_GeV > 0` 的 family（前探 360 项；36 项无质量 family 不入 scope——含 3 中微子，质量仅有上限，Γ/m 不可定义；diff 表披露）。

**Γ 的确定优先级（机械规则，禁止人工逐例裁决）**：
- G1：`width_GeV` 有值（point / range-mid / 寿命 ℏ/τ 换算）→ Γ/m = width/mass
- G2：`width_GeV` 与 `lifetime_s` 均缺 → 按理论自身「稳定粒子：Γ = 0 ⟹ Γ/m = 0 < 0.05 → PP」读法，Γ/m := 0 → PP，旗标 `gamma_from: "absent_stable_rule"`（前探 56 项，DB 中连 G 行都不存在，无可替代数值来源）
- 无其他规则。J^PC（`pdgparticle.quantum_j/p/c`）仅作识别元数据，**不参与判定**。

## 3. 冻结的 diff 表维度

| # | 维度 | 内容 |
| -- | -- | -- |
| D1 | 计数 diff | 官方重数 PP/SC/AC vs CDD 195/83/11 |
| D2 | scope diff | 官方 mass>0 计数（+全提取 396）vs CDD 289；PP 按 gamma_from 分层 vs CDD「稳定 ~20」 |
| D3 | 间隙验证 | 官方排序表 (min SC Γ/m)/(max PP Γ/m>0) 与 (min AC)/(max SC) vs 声称 1.08x/1.07x |
| D4 | 边界敏感带 | Γ/m ∈ [0.04,0.06] ∪ [0.18,0.22] 全列 + 距阈值最小距离 |
| D5 | 每粒子分类表 | 全量落盘（name, pdgid, J^P^C, m, Γ, width_kind, gamma_from, Γ/m, cls） |
| D6 | 示例粒子核验 | 理论文档点名粒子的官方重数结果 vs 理论声称：Z0/W±/t（PP）、ρ(770)（SC）、K*(892)（SC）、a₁(1260)（AC 边界）、σ=f₀(500)（AC）、κ=K₀*(700)（AC） |

## 4. 已知局限（预披露）

1. **G2 读法的混合性**：56 项缺 Γ family 机械并入 PP，混合了「真稳定」（e⁻/p）、「窄而未测」（χ_b0(1P) 类）与「数据不良」（N(~3000) 类）三种物理状态——这是理论自身「Γ=0⟹PP」读法的机械应用；diff 表以 `gamma_from` 旗标分层披露，不做人工拆分。
2. **无逐粒子 diff**：CDD 195/83/11 无逐粒子归属存档（`cdd_pdg_classification_recount.py` 亲验：仅为整数唯一性登记，从未从原始表重数）→ diff 只在计数/scope/间隙/示例层面。
3. **版本差异**：理论文档示例值（如 K*(892) Γ/m=0.057）取自旧版 PDG 数值，官方 2026 提取值 0.0518；D6 核验以「分类是否一致」为准，数值差异披露不裁决。
4. **区间宽度中值**：提取协议对「250–600」类区间宽度取中值，属已登记的既有取舍，本重数不改动。

## 5. 执行与登记

- 脚本：`h:\cdd_lean4\scripts\cdd_pdg_official_recount.py`（单轮执行）
- 输出：`h:\cdd_pdg_official_vs_cdd_diff_20261004.json`
- 登记项：本文件 SHA256、脚本 SHA256、`pdg_particles.json` SHA256、sqlite edition 元组（2026）
- 收口动作：`cdd_pdg_classification_recount.json` 的 `_meta.B7` 登记更新为「重数已执行」并指向本 diff 表（计数字段 195/83/11 本身不动，其「CDD 自有快照」语义维持）
