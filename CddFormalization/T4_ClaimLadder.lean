import CddFormalization.T3_ECSChannels
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.NormNum

/-! # T4 Claim Ladder: 6σ 声明层预注册判据的形式化登记

    CDD-ECS 6σ 框架声明层 (claim layer, v2 预注册) 的 Lean 锚点
    登记, 实现声明层预注册 §snapshot_registration.lean_module 条款:
    - 声明阶梯 L1-L5 的冻结统计量、阈值与确认规则;
    - 双 σ 程序 (z_level 继承 + z_traj 新增)、通道贡献上限 c = 5、
      族级聚合 (族内 Stouffer → 跨族 Stouffer)、完全相关下界
      (族均值口径)、Bonferroni 冻结值;
    - T 系列过渡通道 T1-T8 判据冻结 (数据形态 ~2030+ 尚不存在,
      预注册纪律的本征位置) 与 L4 分区;
    - v5 基线快照 (snapshot 0) 声明层记录值的算术一致性核对。

    ## 事件顺序 (预注册纪律)

    ```
    v1.0 判据冻结 → v1 跑 → 可达性/格式探针 (无指标计算)
      → A1 登记 → v2 跑 → 运行后判决复查 (C1 符号缺陷; 无阈值
      查看/调整) → A2 登记 → v3 跑 → 运行后合成复查 (Z_gap 方向
      缺陷; 无阈值查看/调整) → A3 登记 → v4 跑 (Z_gap 和式权威)
      → 6σ 框架 v1.0-draft → 声明层 v2 预注册 (本模块判据来源;
      SHA256 登记, 声明层数据接触前冻结)
      → v5 跑 (通道层 = v4 逐字复跑 + 声明层首算 = 基线快照 0)
      → 本模块: 判据锚点 (Rat) + 基线快照记录值算术一致性核对
    ```

    ## 溯源链 (每一记录值)

    ```
    原始数据 (缓存 H:\cdd_ecs_data, 逐文件 SHA256 登记于快照)
      → Python 管线 cdd_lean4/scripts/cdd_ecs_channel_pipeline_v5.py
        (implementation guard: 12 条冻结公式字符串 + cap_c = 5.0
        + s 符号表字节级断言先行, 任何失配即中止)
      → JSON 快照 H:\cdd_ecs_channel_pipeline_results_v5.json
        (SHA256 89129A6D…2392, 管线 v5.0, 2026-08-30T10:43:31Z)
      → 本模块: 判据锚点 (Rat) + 记录值算术一致性核对 (Int 缩放)
    ```

    ## 形式化范围 (诚实声明)

    - **基线快照 0 语义**: v5 首次声明层读数不进入任何确认计数;
      全部确认须由冻结后年度快照 (自 2027-09-30) 达成 (交集语义,
      禁止选择性停止); L3 最早确认 2029-09-30, L4 ~2035;
    - `decide` 证明核对的是**记录值与预注册阈值的算术比较**及
      **合成层算术恒等式** (含登记舍入容差), 不构成从原始数据到
      结论的形式化推导 (同 T2_Validation/T3 口径); 物理有效性
      取决于数据管线;
    - **层分离** (v2 预注册 meta.layer_separation): 判决层 (红/
      黄/绿 + 状态机) 管 S2 何时触发; 声明层管理论命题被数据
      支持的置信度。声明层 6σ 不触发任何行动, 判决层红界不要求
      6σ;
    - **L3-traj 负值 (−3.2037σ) 是设计内结果**: 与判决层 CRITICAL
      及理论临界带定位 (R ≈ 1, 快窗主战场) 一致, 非理论反驳 —
      是对事实命题「当前全球系统尚未进入解锁领先轨迹」的支持
      (v2 预注册 honesty_boundaries);
    - **无理数规避**: √2/√3/√10 进入恒等式时取平方形式
      (k·Z² ≈ (Σz)² 型), 登记容差覆盖记录值 4 位小数舍入的传播
      界 (各定理注释给出推导; T3 §5 同法);
    - **管线合成口径**: 族内/跨族 Stouffer 输出按 4 位小数舍入后
      进入最终 /√2 步 (管线 family_stouffer 返回值即舍入值),
      故本模块以 4 位小数登记值可复算全部合成层记录值;
    - C7 z_level 是**估计不确定度传播程序** (δ 法, LR = 1 − 2^β),
      与序列残差程序 (C1/C4/C5/C8) 性质不同, 快照内显式注记;
    - τ 读数是**可解释性读数** (至阈值年数 ± 误差), 非检验统计量;
    - 本模块登记「预注册判据与 v5 基线快照统计结果的形式化记录」,
      非「从原始数据到结论的形式化推导」。

    CDD Framework v28.4 · CDD-ECS 6σ 声明层
    Date: 2026-08-30
    All proofs use ONLY core Lean4 tactics (decide) and Mathlib norm_num.
-/

namespace CDD.T4.ClaimLadder

open CDD.T3.ECSChannels

-- ============================================================
-- §1 声明阶梯、σ 程序与 T 系列枚举
-- ============================================================

/-- 声明阶梯层级 (v2 预注册 claim_ladder): L1 压力趋势实在性 /
    L2a 能源学习曲线实在性 / L2b 信息采用趋势实在性 /
    L3 R 方向 (level-v1 对照 / level-v2 主读数 / traj 轨迹) /
    L4 过渡速率 (T 系列) / L5 P1 条件闭合 (远期占位)。 -/
inductive ClaimLevel where
  | L1
  | L2a
  | L2b
  | L3
  | L4
  | L5
  deriving DecidableEq

/-- σ 程序 (v2 预注册 sigma_programs): z_level = 水位读数
    (残差 σ 口径或 C7 估计 σ 口径); z_traj = 轨迹读数
    (冻结窗口 OLS 趋势 t, 方向调整后一致折减 1/√10)。 -/
inductive SigmaProgram where
  | zLevel
  | zTraj
  deriving DecidableEq

/-- T 系列过渡通道 (v2 预注册 t_series, 数据形态 ~2030+ 尚不存在):
    政治上层结构承诺的可测化。上 = 解锁正方向, 下 = 压力方向。 -/
inductive TChannel where
  | T1_r_need
  | T2_concentration
  | T3_binding
  | T4_participation
  | T5_guard
  | T6_network
  | T7_language
  | T8_sc_embedding
  deriving DecidableEq

/-- T 系列方向: true = 上升为解锁正方向 (T1/T3/T4/T7/T8);
    false = 下降为正方向 (T2/T5/T6, 压力方向)。 -/
def tDirectionUp : TChannel → Bool
  | .T1_r_need => true
  | .T2_concentration => false
  | .T3_binding => true
  | .T4_participation => true
  | .T5_guard => false
  | .T6_network => false
  | .T7_language => true
  | .T8_sc_embedding => true

/-- L4 治理压力分区 (v2 预注册 L4 partition): T2/T5/T6。 -/
def governancePressureT : List TChannel :=
  [.T2_concentration, .T5_guard, .T6_network]

/-- L4 过渡解锁分区: T1/T3/T4/T7/T8。 -/
def transitionUnlockT : List TChannel :=
  [.T1_r_need, .T3_binding, .T4_participation, .T7_language, .T8_sc_embedding]

/-- L4 分区计数一致性: 3 治理压力 + 5 过渡解锁 = 8。 -/
theorem t_partition_count :
    governancePressureT.length + transitionUnlockT.length = 8 := by decide

/-- 治理压力分区全部为压力方向。 -/
theorem t_pressure_directions :
    (governancePressureT.all (fun t => !tDirectionUp t)) = true := by decide

/-- 过渡解锁分区全部为解锁正方向。 -/
theorem t_unlock_directions :
    (transitionUnlockT.all tDirectionUp) = true := by decide

/-- L4 分区互斥。 -/
theorem t_partition_disjoint :
    (governancePressureT.any (fun t =>
      transitionUnlockT.any (fun u => decide (t = u)))) = false := by
  decide

-- ============================================================
-- §2 冻结判据锚点 (声明层 v2, 数据接触前冻结)
-- ============================================================

/-! ### 6σ 定义与贡献上限

    6σ = 单侧 p < 9.9×10⁻¹⁰ ⇔ 标准正态 Z ≥ 6 (v2 预注册
    meta.six_sigma_definition)。贡献上限守卫 (guards.cap_c):
    进入合成的通道贡献 z_enter = sign(z)·min(|z|, 5), c = 5.0;
    理由: 族显著性不得由单通道承载 (A3-2 登记 C5 占 96.6%);
    5 = 物理侧协议惯例「通道单独 5σ 显著」。
    **c = 5 < 6 语义**: 任一单通道 (即使被截前 26.67σ) 都不能
    独自把族级声明抬到 6σ — 上限保证 6σ 族级声明本质上是
    多通道广度命题。-/

/-- 6σ 阈值锚点: Z ≥ 6。 -/
abbrev sigma6 : Rat := mkRat 6 1

/-- 通道贡献上限: c = 5.0 (合成入口截断)。 -/
abbrev cap_c : Rat := mkRat 5 1

/-- 上限-阈值序: c = 5 < 6 — 单通道贡献被截至阈值之下,
    6σ 族级声明不可由单通道独自达成 (守卫 (a) 的设计语义)。 -/
theorem cap_below_six_sigma : cap_c < sigma6 := by decide

/-- L2b 可判定性门槛: 序列 ≥ 8 个年度观测才可判决
    (短序列 t 无功效, 硬判会制造假阴性)。 -/
abbrev l2b_decidability_gate : Nat := 8

/-- Bonferroni 通道级冻结值 (族内 α = 9.9×10⁻¹⁰ 单侧):
    m = 1/2/3/4/8。 -/
abbrev bonferroni_m1 : Rat := mkRat 6 1
abbrev bonferroni_m2 : Rat := mkRat 611 100
abbrev bonferroni_m3 : Rat := mkRat 618 100
abbrev bonferroni_m4 : Rat := mkRat 622 100
abbrev bonferroni_m8 : Rat := mkRat 63 10

/-- Bonferroni 冻结值单调: 6.00 < 6.11 < 6.18 < 6.22 < 6.30。 -/
theorem bonferroni_monotone :
    bonferroni_m1 < bonferroni_m2 ∧ bonferroni_m2 < bonferroni_m3
    ∧ bonferroni_m3 < bonferroni_m4 ∧ bonferroni_m4 < bonferroni_m8 := by
  decide

/-- 声明层阈值函数: L1/L2a/L2b/L3/L4 均为 6σ; L5 远期占位
    (判据冻结规则: 数据形态可描述时冻结, 不晚于首个候选基地
    建成 — 过早冻结引入无效精度)。 -/
def levelThreshold : ClaimLevel → Option Rat
  | .L1 | .L2a | .L2b | .L3 | .L4 => some 6
  | .L5 => none

/-- L1-L4 阈值 = 6σ, L5 无冻结阈值。 -/
theorem level_thresholds :
    levelThreshold ClaimLevel.L1 = some 6 ∧ levelThreshold ClaimLevel.L2a = some 6
    ∧ levelThreshold ClaimLevel.L2b = some 6 ∧ levelThreshold ClaimLevel.L3 = some 6
    ∧ levelThreshold ClaimLevel.L4 = some 6 ∧ levelThreshold ClaimLevel.L5 = none := by
  decide

/-- 确认窗口 (guards.repeated_snapshot_control): L3 = 3 个连续
    年度快照; L4/L5 = 5; L1/L2a/L2b = 立即可判 + 年度复查
    (撤销制, 非固定计数)。交集语义, 禁止选择性停止。 -/
def confirmationWindow : ClaimLevel → Option Nat
  | .L3 => some 3
  | .L4 => some 5
  | .L5 => some 5
  | .L1 | .L2a | .L2b => none

/-- 确认时钟: 首个可计入确认的快照 = 2027-09-30 (v1.0 §9 年度
    复查日); L3 最早确认 = 2029-09-30 (窗口 3); L4 激活 ~2030+
    (首个基地统计系统上线), 最早确认 ~2035。 -/
abbrev firstEligibleSnapshotYear : Nat := 2027
abbrev l3EarliestConfirmationYear : Nat := 2029
abbrev l4ActivationYearApprox : Nat := 2030
abbrev l4EarliestConfirmationYearApprox : Nat := 2035

/-- 确认窗口登记: L3 = 3, L4 = 5, L5 = 5。 -/
theorem confirmation_windows :
    confirmationWindow ClaimLevel.L3 = some 3
    ∧ confirmationWindow ClaimLevel.L4 = some 5
    ∧ confirmationWindow ClaimLevel.L5 = some 5 := by decide

/-- 时钟序: 2027 (首可计入) < 2029 (L3 最早确认)。 -/
theorem clock_order : firstEligibleSnapshotYear < l3EarliestConfirmationYear := by decide

/-- 时钟序: L4 激活 (~2030) 早于其最早确认 (~2035)。 -/
theorem l4_clock_order : l4ActivationYearApprox < l4EarliestConfirmationYearApprox := by
  decide

/-! ### s 符号表 (z_traj 方向调整, v2 预注册 sigma_programs.z_traj)

    s_i = 方向符号: 指标上升 = 安全 → s = +1; 指标上升 = 危险
    → s = −1。z_traj_i = s_i·t_i/√10。C2/C6 不在冻结 s 表内
    (pending_data / 时长计数, 无 σ), 登记 s = 0 以显式标记排除。 -/

/-- z_traj 冻结方向符号表 (7 个可算通道; C3 双流域同 s = +1)。 -/
def sTable : ECSChannel → Int
  | .C1_temperature => -1        -- 升温 = 危险 (M1 裕度收缩)
  | .C2_amoc => 0                -- 不在冻结 s 表 (pending_data)
  | .C3_icesheets => 1           -- 质量 (负累积) 下降 = 危险
  | .C4_biosphere => -1          -- OHC 上升 = 危险
  | .C5_biogeochemical => -1     -- CO2 上升 = 危险
  | .C6_social => 0              -- 不在冻结 s 表 (时长计数)
  | .C7_energy => -1             -- β ≥ 0 (无学习) = 危险
  | .C8_information => 1         -- 采用率下降 = 危险

/-- z_traj 花名册: 6 通道 (C3 折合自双流域)。 -/
def zTrajRoster : List ECSChannel :=
  [.C1_temperature, .C3_icesheets, .C4_biosphere, .C5_biogeochemical, .C7_energy, .C8_information]

/-- z_traj 花名册计数 = 6。 -/
theorem ztraj_roster_count : zTrajRoster.length = 6 := by decide

/-- 花名册内通道方向符号均非零 (|s| = 1)。 -/
theorem ztraj_roster_saturated :
    (zTrajRoster.all (fun c => decide (sTable c = 1 ∨ sTable c = -1))) = true := by
  decide

/-- 排除通道 (C2/C6) 方向符号 = 0 (显式排除标记)。 -/
theorem ztraj_excluded_zero :
    sTable ECSChannel.C2_amoc = 0 ∧ sTable ECSChannel.C6_social = 0 := by decide

/-! ### C7 z_level 程序锚点 (估计不确定度传播)

    sigma_LR_pp = 100·ln(2)·(1 − LR)·SE(β) (δ 法, LR = 1 − 2^β);
    z_level_C7 = (LR_pct − 12)/sigma_LR_pp; 红锚 12% (C7 红界
    LR < 12, v1.0 §2 冻结)。 -/
abbrev c7_red_LR_pct : Rat := mkRat 12 1

-- ============================================================
-- §3 T 系列冻结阈值 (数据形态尚不存在, 预注册本征位置)
-- ============================================================

/-! T 系列判据 (v2 预注册 t_series.channels): 相对阈值锚
    (r0/c0/f0/x0) = 建基年实测值 (任何干预部署前哈希登记);
    锚是测量不是选择。绝对阈值如下冻结。 -/

/-- T3 约束力比率: red < 1/10, green ≥ 1/3 (且斜率 ≥ +3 pp/yr)。 -/
abbrev t3_binding_red : Rat := mkRat 1 10
abbrev t3_binding_green : Rat := mkRat 1 3

/-- T4 参与率: red < 25%, green ≥ 50% (且斜率 ≥ +2 pp/yr)。 -/
abbrev t4_participation_red : Rat := mkRat 25 1
abbrev t4_participation_green : Rat := mkRat 50 1

/-- T5 维护性武装频率 (相对 f0): red > 0.8·f0, green ≤ 0.2·f0
    (且斜率 ≤ −10 %/yr) — 「守卫系统随道德自足性成熟而日落」
    的可裁决形式。 -/
abbrev t5_guard_hi : Rat := mkRat 8 10
abbrev t5_guard_lo : Rat := mkRat 2 10

/-- T6 协商网络集中度 (相对 x0): red > 1.2·x0, green ≤ 0.8·x0 —
    PP 再核化警报 (与 T3 交叉验证)。 -/
abbrev t6_network_hi : Rat := mkRat 12 10
abbrev t6_network_lo : Rat := mkRat 8 10

/-- T7 语言覆盖: red < 70%, green ≥ 90% (语义等价 ≥ 95%)。 -/
abbrev t7_language_red : Rat := mkRat 70 1
abbrev t7_language_green : Rat := mkRat 90 1

/-- T8 SC 嵌入: red < 50%, green ≥ 80% (数字化覆盖率斜率 > 0)。 -/
abbrev t8_sc_red : Rat := mkRat 50 1
abbrev t8_sc_green : Rat := mkRat 80 1

/-- T1 绿界相对偏移: r0 + 10 pp (斜率 ≥ +1 pp/yr)。 -/
abbrev t1_green_offset_pp : Rat := mkRat 10 1

/-- T2 绿界相对偏移: c0 − 5 pp (斜率 ≤ −0.5 pp/yr)。 -/
abbrev t2_green_offset_pp : Rat := mkRat 5 1

theorem t3_band_order : t3_binding_red < t3_binding_green := by decide
theorem t4_band_order : t4_participation_red < t4_participation_green := by decide
theorem t5_band_order : t5_guard_lo < t5_guard_hi := by decide
theorem t6_band_order : t6_network_lo < t6_network_hi := by decide
theorem t7_band_order : t7_language_red < t7_language_green := by decide
theorem t8_band_order : t8_sc_red < t8_sc_green := by decide

/-- T 系列带序合取: 六个绝对阈值通道红界均严格低于绿界
    (黄带非空)。 -/
theorem t_series_band_orders :
    t3_binding_red < t3_binding_green
    ∧ t4_participation_red < t4_participation_green
    ∧ t5_guard_lo < t5_guard_hi
    ∧ t6_network_lo < t6_network_hi
    ∧ t7_language_red < t7_language_green
    ∧ t8_sc_red < t8_sc_green := by decide

-- ============================================================
-- §4 基线快照 0 记录值: σ 程序分量 (Int 缩放登记)
-- ============================================================

/-! 记录值来源: v5 快照 claim_layer.components / .L1 / .L2a /
    .L2b / .L3_R_direction / .tau_readings / .bonferroni_channel_level。
    缩放: z 值 ×10⁴; t 值 ×10²; τ 相关值各自注明。管线以未舍入
    中间值计算, 本模块按记录值登记, 不重算; 合成层算术按
    §0 登记容差核对 (管线族内/跨族输出按 4 位小数舍入后进入
    最终 /√2, 故 4 位小数登记值可复算合成层)。 -/

/-- L1 花名册趋势 t 值 (×10², v5 快照 L1.t_values):
    C1 = 11.77 (GISTEMP 近 30 年), C3-GIS = −76.6,
    C3-AIS = −88.13 (IMBIE 近 10 年指标窗), C4 = 14.16
    (OHC 近 10 年), C5 = 81.83 (CO2 近 30 年)。 -/
abbrev tC1_x100 : Int := 1177
abbrev tC3GIS_x100 : Int := -7660
abbrev tC3AIS_x100 : Int := -8813
abbrev tC4_x100 : Int := 1416
abbrev tC5_x100 : Int := 8183

/-- z_traj 未截断记录值 (×10⁴, v5 快照 components.z_traj):
    C1 = −3.7229, C3-GIS = −24.2224, C3-AIS = −27.8705,
    C3 (折合) = −27.8705, C4 = −4.4775, C5 = −25.8784,
    C7 = 9.7766, C8 = 1.4623。 -/
abbrev ztrajC1_x1e4 : Int := -37229
abbrev ztrajC3GIS_x1e4 : Int := -242224
abbrev ztrajC3AIS_x1e4 : Int := -278705
abbrev ztrajC3_x1e4 : Int := -278705
abbrev ztrajC4_x1e4 : Int := -44775
abbrev ztrajC5_x1e4 : Int := -258784
abbrev ztrajC7_x1e4 : Int := 97766
abbrev ztrajC8_x1e4 : Int := 14623

/-- z_traj 截断后进入合成值 (×10⁴, components.z_traj_capped):
    C3/C5/C7 触上限 ±5.0, C1/C4/C8 未触。 -/
abbrev ztrajC3_capped_x1e4 : Int := -50000
abbrev ztrajC5_capped_x1e4 : Int := -50000
abbrev ztrajC7_capped_x1e4 : Int := 50000

/-- z_level 记录值 (×10⁴): C1 = 0.3288, C4 = −0.0669,
    C5 = 7.436 (未截), C7 = 26.6713 (新程序, 未截),
    C8 = 2.1565。 -/
abbrev zlvlC1_x1e4 : Int := 3288
abbrev zlvlC4_x1e4 : Int := -669
abbrev zlvlC5_x1e4 : Int := 74360
abbrev zlvlC7_x1e4 : Int := 266713
abbrev zlvlC8_x1e4 : Int := 21565

/-- z_level 截断后进入合成值 (×10⁴): C5 → 5.0, C7 → 5.0。 -/
abbrev zlvlC5_capped_x1e4 : Int := 50000
abbrev zlvlC7_capped_x1e4 : Int := 50000

-- ------------------------------------------------------------
-- §4.2 贡献上限守卫 (精确截断核对)
-- ------------------------------------------------------------

/-- C5 z_level 截断: 7.436 > 5 → 5.0 (贡献上限守卫 (a))。 -/
theorem cap_C5_level : zlvlC5_x1e4 > 50000 ∧ zlvlC5_capped_x1e4 = 50000 := by decide

/-- C7 z_level 截断: 26.6713 > 5 → 5.0。 -/
theorem cap_C7_level : zlvlC7_x1e4 > 50000 ∧ zlvlC7_capped_x1e4 = 50000 := by decide

/-- C3-GIS z_traj 截断: |−24.2224| > 5 → −5.0。 -/
theorem cap_C3GIS_traj : ztrajC3GIS_x1e4 < -50000 ∧ -50000 < 0 := by decide

/-- C3-AIS z_traj 截断: |−27.8705| > 5 → −5.0。 -/
theorem cap_C3AIS_traj : ztrajC3AIS_x1e4 < -50000 := by decide

/-- C5 z_traj 截断: |−25.8784| > 5 → −5.0。 -/
theorem cap_C5_traj : ztrajC5_x1e4 < -50000 := by decide

/-- C7 z_traj 截断: 9.7766 > 5 → +5.0。 -/
theorem cap_C7_traj : ztrajC7_x1e4 > 50000 ∧ ztrajC7_capped_x1e4 = 50000 := by decide

/-- 未触上限通道 (z_traj): C1 (3.72), C4 (4.48), C8 (1.46) 均
    |z| < 5, 原值进入合成。 -/
theorem nocap_traj :
    ztrajC1_x1e4 > -50000 ∧ ztrajC1_x1e4 < 50000
    ∧ ztrajC4_x1e4 > -50000 ∧ ztrajC4_x1e4 < 50000
    ∧ ztrajC8_x1e4 < 50000 := by decide

/-- 未触上限通道 (z_level): C1/C4/C8 均 |z| < 5。 -/
theorem nocap_level :
    zlvlC1_x1e4 < 50000 ∧ zlvlC4_x1e4 > -50000 ∧ zlvlC8_x1e4 < 50000 := by decide

/-! **守卫 (a) 的已登记代价 (广度语义)**: C7 单通道 z_level
    = 26.67σ 被截至 5 — C7 的进一步改善对 Z_R 无边际贡献,
    复合统计趋向「决定性越过阈值的通道数」广度度量
    (v2 预注册 L3-traj breadth_honesty_note)。 -/

/-- C7 上限约束登记: 未截 26.6713 > 5 — 单通道优势被封顶,
    6σ 声明必须由多通道广度达成 (§2 cap_below_six_sigma)。 -/
theorem c7_cap_binds_breadth_cost : zlvlC7_x1e4 > 50000 := by decide

-- ------------------------------------------------------------
-- §4.3 C3 折合 (最劣流域, 保守)
-- ------------------------------------------------------------

/-- C3 折合规则 z_C3 = min(z_GIS, z_AIS): AIS (−27.8705) 劣于
    GIS (−24.2224), 折合 = AIS 值 (精确)。 -/
theorem c3_fold_rule :
    ztrajC3AIS_x1e4 ≤ ztrajC3GIS_x1e4 ∧ ztrajC3_x1e4 = ztrajC3AIS_x1e4 := by decide

-- ============================================================
-- §5 L1 / L2a / L2b: 判决与算术
-- ============================================================

/-- L1 记录值: Z_L1 = 45.4653σ (×10⁴) 与 χ² 读数 = 2067.09
    (×10², df = 5)。 -/
abbrev ZL1_x1e4 : Int := 454653
abbrev chi2_x100 : Int := 206709
abbrev chi2_df : Nat := 5

/-- L1 平方恒等式 (规避 √10): Z_L1 = √(Σt²)/√10 ⇒
    Z_L1² = χ² 读数。Z² 与 χ² 均由未舍入 t 值计算后各自 4/2 位
    小数舍入; 传播界 ≈ 2|Z|·5×10⁻⁵ + 5×10⁻³ ≈ 10⁻², 注册容差
    10⁻² (×10⁻⁸ 单位 10⁶); 实际偏差 3.5×10⁻³。 -/
theorem L1_squared_chi2 :
    (ZL1_x1e4 * ZL1_x1e4 - chi2_x100 * 1000000).natAbs ≤ 1000000 := by decide

/-- L1 与花名册 t 值的一致性 (平方形式): 10·Z_L1² ≈ Σt_i²。
    t 记录至 2 位小数 (各 ±5×10⁻³) ⇒ Σt² 传播界
    2·5×10⁻³·Σ|t| = 0.01×272.49 ≈ 2.72 ⇒ 10Z² 容差 3 (×10⁻⁸
    单位 3×10⁸); 实际偏差 1.29。 -/
theorem L1_squared_sum_t :
    (10 * ZL1_x1e4 * ZL1_x1e4
      - 10000 * (tC1_x100 * tC1_x100 + tC3GIS_x100 * tC3GIS_x100
        + tC3AIS_x100 * tC3AIS_x100 + tC4_x100 * tC4_x100
        + tC5_x100 * tC5_x100)).natAbs ≤ 300000000 := by decide

/-- L1 χ² 自由度 = 花名册大小 = 5 (C2/C6 pending 排除并报告)。 -/
theorem L1_df_roster : chi2_df = 5 ∧ chi2_df = 1 + 1 + 1 + 1 + 1 := by decide

/-- **L1 判决: 45.4653 ≥ 6 — 压力通道组物理趋势实在性在基线
    快照即超 6σ** (判决可由当前数据作出; 年度快照复查,
    撤销制; 基线不计数)。 -/
theorem L1_threshold_met : 60000 ≤ ZL1_x1e4 := by decide

/-- L1 超阈值量: 45.4653 − 6 = 39.4653σ。 -/
theorem L1_margin : ZL1_x1e4 - 60000 = 394653 := by decide

/-- L2a 记录值: t_β = −30.92 (×10²), SE(β) = 0.021714 (×10⁶),
    z_L2a = 9.7766σ (×10⁴; 未截断 — 单通道命题豁免上限)。 -/
abbrev tBeta_x100 : Int := -3092
abbrev SEbeta_x1e6 : Int := 21714
abbrev zL2a_x1e4 : Int := 97766

/-- L2a 平方恒等式: z = −t/√10 ⇒ 10·z² ≈ t²。t 记录至 2 位小数
    (±5×10⁻³ ⇒ t² 传播界 2×30.92×0.005 ≈ 0.31), z 至 4 位
    (10z² 传播界 ≈ 0.01), 注册容差 0.4 (×10⁻⁸ 单位 4×10⁷);
    实际偏差 0.227。 -/
theorem L2a_squared :
    (10 * zL2a_x1e4 * zL2a_x1e4 - 10000 * (3092 * 3092)).natAbs ≤ 40000000 := by decide

/-- **L2a 判决: 9.7766 ≥ 6 — PV LCOE 学习曲线实在性 (β < 0)
    在基线快照即超 6σ** (未截断值; 年度复查, 学习停滞 → 撤销)。 -/
theorem L2a_threshold_met : 60000 ≤ zL2a_x1e4 := by decide

/-- L2b 记录状态: series_short — OECD 采用率序列 n = 6 < 8
    (可判定性门槛未过), 不可判而非失败 (短序列 t 无功效,
    硬判制造假阴性; 序列达 8 个年度观测后按阈值判决)。 -/
abbrev l2b_n_obs : Nat := 6

theorem L2b_series_short : l2b_n_obs < l2b_decidability_gate := by decide

-- ============================================================
-- §6 L3 三变体: 合成层算术与判决
-- ============================================================

/-! L3 合成 (管线 v5 family_stouffer 口径): 族内 Stouffer
    (sum z/√k) → 跨族 Stouffer (sum 族值/√族数) →
    Z_R = (Z_unlock + Z_pressure)/√2; 完全相关下界 =
    (unlock 族均值 Stouffer + pressure 族均值 Stouffer)/√2。
    族内/跨族输出按 4 位小数舍入后进入最终 /√2。压力侧全部
    z 通道属单一 climate_carbon 族 — 压力侧信息本质是**一个**
    气候系统承诺, 非多份独立确认 (v2 guards.family_aggregation
    structural_note, 读数语义的一部分)。 -/

/-- L3-level(v1 对照花名册) 合成层记录值 (×10⁴):
    Z_pressure = 3.038, Z_unlock = 2.1565 (k = 1, = z_C8),
    Z_R = 3.6731, 完全相关下界 = 2.7651。 -/
abbrev Zp_v1_x1e4 : Int := 30380
abbrev Zu_v1_x1e4 : Int := 21565
abbrev ZR_v1_x1e4 : Int := 36731
abbrev pcb_v1_x1e4 : Int := 27651

/-- L3-level(v2 主读数花名册) 合成层记录值 (×10⁴):
    Z_pressure = 3.038, Z_unlock = 5.0604, Z_R = 5.7264,
    完全相关下界 = 4.8185。 -/
abbrev Zp_v2_x1e4 : Int := 30380
abbrev Zu_v2_x1e4 : Int := 50604
abbrev ZR_v2_x1e4 : Int := 57264
abbrev pcb_v2_x1e4 : Int := 48185

/-- L3-traj 合成层记录值 (×10⁴): Z_pressure_traj = −9.1002,
    Z_unlock_traj = 4.5695, Z_R_traj = −3.2037,
    完全相关下界 = 0.0137。 -/
abbrev Zptraj_x1e4 : Int := -91002
abbrev Zutraj_x1e4 : Int := 45695
abbrev ZRtraj_x1e4 : Int := -32037
abbrev pcb_traj_x1e4 : Int := 137

/-- 压力侧 z 和 (v1/v2 花名册, 截断后; ×10⁴):
    0.3288 − 0.0669 + 5.0 = 5.2619 (climate_carbon 单族, k = 3)。 -/
abbrev pressureLevelSum_x1e4 : Int := 52619

/-- 压力侧族均值 (完全相关下界分量; ×10⁴): 5.2619/3 → 1.754。 -/
abbrev pressureFamilyMean_x1e4 : Int := 17540

/-- 解锁侧 z 和 (v2 花名册, 截断后; ×10⁴): 5.0 + 2.1565
    = 7.1565 (energy + information 两族, 各 k = 1)。 -/
abbrev unlockLevelSum_v2_x1e4 : Int := 71565

/-- 解锁侧 z 和 (v1 对照, ×10⁴): 2.1565 (information 单族)。 -/
abbrev unlockLevelSum_v1_x1e4 : Int := 21565

/-- 压力和 (v1 = v2, 同花名册同截断): 记录值恒等式
    0.3288 − 0.0669 + 5.0 = 5.2619 (精确)。 -/
theorem L3_pressure_sum_identity :
    zlvlC1_x1e4 + zlvlC4_x1e4 + zlvlC5_capped_x1e4 = pressureLevelSum_x1e4 := by decide

/-- 解锁和 (v2): 5.0 + 2.1565 = 7.1565 (精确)。 -/
theorem L3_unlock_sum_v2 :
    zlvlC7_capped_x1e4 + zlvlC8_x1e4 = unlockLevelSum_v2_x1e4 := by decide

/-- 解锁和 (v1): Z_unlock = z_C8 (k = 1, √1 = 1, 精确恒等式)。 -/
theorem L3_unlock_v1_identity : unlockLevelSum_v1_x1e4 = zlvlC8_x1e4 := by decide

/-- 压力族均值舍入一致性: |3×1.7540 − 5.2619| = 1 (×10⁻⁴)
    — 4 位小数舍入 (未舍入 1.75397 → 1.754)。 -/
theorem L3_pressure_mean_rounding :
    (3 * pressureFamilyMean_x1e4 - pressureLevelSum_x1e4).natAbs ≤ 100 := by decide

/-- 压力侧 Stouffer 平方恒等式 (k = 3): 3·Z_pressure² ≈ (Σz)²。
    Z 记录至 4 位小数 ⇒ 传播界 2k·|Z|·5×10⁻⁵ ≈ 9.1×10⁻⁴, 注册
    容差 10⁻² (×10⁻⁸ 单位 10⁶); 实际偏差 7.4×10⁻⁴。 -/
theorem L3_pressure_stouffer_squared :
    (3 * Zp_v2_x1e4 * Zp_v2_x1e4 - pressureLevelSum_x1e4 * pressureLevelSum_x1e4).natAbs
      ≤ 1000000 := by decide

/-- 解锁侧 Stouffer 平方恒等式 (v2, 两族): 2·Z_unlock² ≈ (Σz)²。
    实际偏差 1.96×10⁻³ ≤ 注册容差 10⁻²。 -/
theorem L3_unlock_stouffer_squared_v2 :
    (2 * Zu_v2_x1e4 * Zu_v2_x1e4 - unlockLevelSum_v2_x1e4 * unlockLevelSum_v2_x1e4).natAbs
      ≤ 1000000 := by decide

/-- Z_R 平方恒等式 (v2 主读数): 2·Z_R² ≈ (Z_u + Z_p)²,
    其中 Z_u + Z_p = 5.0604 + 3.038 = 8.0984。实际偏差
    7.7×10⁻⁴ ≤ 注册容差 10⁻²。 -/
theorem L3_ZR_squared_v2 :
    (2 * ZR_v2_x1e4 * ZR_v2_x1e4 - 80984 * 80984).natAbs ≤ 1000000 := by decide

/-- Z_R 平方恒等式 (v1 对照): 2·Z_R² ≈ (2.1565 + 3.038)²
    = 5.1945²。实际偏差 5.0×10⁻⁴。 -/
theorem L3_ZR_squared_v1 :
    (2 * ZR_v1_x1e4 * ZR_v1_x1e4 - 51945 * 51945).natAbs ≤ 1000000 := by decide

/-- 完全相关下界平方恒等式 (v2): 2·pcb² ≈ (5.0604 + 1.754)²
    = 6.8144²。实际偏差 1.6×10⁻⁴。 -/
theorem L3_pcb_squared_v2 :
    (2 * pcb_v2_x1e4 * pcb_v2_x1e4 - 68144 * 68144).natAbs ≤ 1000000 := by decide

/-- 完全相关下界平方恒等式 (v1): 2·pcb² ≈ (2.1565 + 1.754)²
    = 3.9105²。实际偏差 4.5×10⁻⁴。 -/
theorem L3_pcb_squared_v1 :
    (2 * pcb_v1_x1e4 * pcb_v1_x1e4 - 39105 * 39105).natAbs ≤ 1000000 := by decide

/-- **L3-level(v2) 判决: 5.7264 < 6 — 未达 6σ** (诚实登记;
    确认须 ≥ 3 个冻结后连续年度快照全 ≥ 6, 最早 2029-09-30)。 -/
theorem L3_v2_not_met : ZR_v2_x1e4 < 60000 := by decide

/-- L3-v2 差距量化: 6 − 5.7264 = 0.2736σ (×10⁻⁴ = 2736)。 -/
theorem L3_v2_gap : 60000 - ZR_v2_x1e4 = 2736 := by decide

/-- L3-v1 对照判决: 3.6731 < 6 (未达)。 -/
theorem L3_v1_not_met : ZR_v1_x1e4 < 60000 := by decide

/-- 解锁侧覆盖完成效应: v2 花名册 (C7 加入) 使 Z_R 自 3.6731
    升至 5.7264 — v2 预注册设计的解锁侧补全路径被执行验证
    (v1 → v2: +2.0533σ, 全部来自 C7 截断贡献)。 -/
theorem L3_v2_improves_v1 : ZR_v1_x1e4 < ZR_v2_x1e4 ∧ ZR_v2_x1e4 - ZR_v1_x1e4 = 20533 := by
  decide

/-- 完全相关下界亦未达 (v2): 4.8185 < 6 — 即使按族均值保守口径
    同样未达; 结论对相关性假设稳健 (两口径同向)。 -/
theorem L3_v2_pcb_not_met : pcb_v2_x1e4 < 60000 := by decide

/-! L3-traj 合成 (截断后进入值; ×10⁴): 压力侧 C1 = −3.7229,
    C3 = −5.0, C4 = −4.4775, C5 = −5.0 (climate_carbon 单族
    k = 4, √4 = 2 — **精确**半和); 解锁侧 C7 = 5.0 (energy),
    C8 = 1.4623 (information), 跨族 /√2。 -/

/-- L3-traj 压力侧和 (×10⁴): −3.7229 − 5.0 − 4.4775 − 5.0
    = −18.2004 (精确)。 -/
abbrev pressureTrajSum_x1e4 : Int := -182004

/-- L3-traj 压力侧和恒等式 (精确): 四截断值之和。 -/
theorem L3traj_pressure_sum :
    ztrajC1_x1e4 + ztrajC3_capped_x1e4 + ztrajC4_x1e4 + ztrajC5_capped_x1e4
      = pressureTrajSum_x1e4 := by decide

/-- **L3-traj 压力侧 Stouffer 精确恒等式 (k = 4, √4 = 2, 无
    无理数)**: Z_pressure_traj = −18.2004/2 = −9.1002 (精确)。 -/
theorem L3traj_pressure_half :
    2 * Zptraj_x1e4 = pressureTrajSum_x1e4 := by decide

/-- L3-traj 压力族均值 (完全相关下界分量, 精确):
    −18.2004/4 = −4.5501。 -/
abbrev pressureTrajMean_x1e4 : Int := -45501

theorem L3traj_pressure_mean : 4 * pressureTrajMean_x1e4 = pressureTrajSum_x1e4 := by decide

/-- L3-traj 解锁侧跨族 Stouffer 平方恒等式: 2·Z_u² ≈ (5.0 +
    1.4623)² = 6.4623²。实际偏差 6.6×10⁻⁴。 -/
theorem L3traj_unlock_squared :
    (2 * Zutraj_x1e4 * Zutraj_x1e4 - 64623 * 64623).natAbs ≤ 1000000 := by decide

/-- L3-traj Z_R 平方恒等式: 2·Z_R_traj² ≈ (4.5695 − 9.1002)²
    = 4.5307²。实际偏差 1.4×10⁻⁴。 -/
theorem L3traj_ZR_squared :
    (2 * ZRtraj_x1e4 * ZRtraj_x1e4 - 45307 * 45307).natAbs ≤ 1000000 := by decide

/-- L3-traj 完全相关下界平方恒等式: 2·pcb² ≈ (4.5695 −
    4.5501)² = 0.0194²。实际偏差 9.8×10⁻⁵。 -/
theorem L3traj_pcb_squared :
    (2 * pcb_traj_x1e4 * pcb_traj_x1e4 - 194 * 194).natAbs ≤ 1000000 := by decide

/-- **L3-traj 判决: Z_R_traj = −3.2037 < 0 — 命题不被支持**
    (压力侧恶化确定性超过解锁侧改善确定性)。设计内结果:
    与判决层 CRITICAL 及理论临界带 (R ≈ 1) 定位一致, 非理论
    反驳; 是对「当前全球系统尚未进入解锁领先轨迹」的支持。 -/
theorem L3traj_negative : ZRtraj_x1e4 < 0 := by decide

/-- L3-traj 亦远低于 6σ 阈值 (单侧命题, 负值即不支持)。 -/
theorem L3traj_not_met : ZRtraj_x1e4 < 60000 := by decide

/-- L3-traj 完全相关下界 = 0.0137 ≈ 0 — 两口径 (独立/完全相关)
    同为零邻域: 解锁轨迹领先量在两口径下均不成立。 -/
theorem L3traj_pcb_near_zero : -1000 ≤ pcb_traj_x1e4 ∧ pcb_traj_x1e4 ≤ 1000 := by decide

-- ============================================================
-- §7 C7 z_level 程序 (δ 法) 记录值算术
-- ============================================================

/-- C7 z_level 程序记录值: LR_pct = 37.21 (×10²),
    σ_LR_pp = 0.9451 (×10⁴), z_level_C7 = 26.6713 (×10⁴)。 -/
abbrev c7_LR_pct_x100 : Int := 3721
abbrev c7_sigma_LR_pp_x1e4 : Int := 9451
abbrev c7_z_level_x1e4 : Int := 266713

/-- C7 程序交叉乘积恒等式: z·σ ≈ LR_pct − 12 = 25.21。
    z 记录 4 位 (±5×10⁻⁵), σ 4 位, LR_pct 2 位 (±0.005) ⇒
    传播界 ≈ 26.67×5×10⁻⁵ + 0.945×5×10⁻⁵ + 0.005 ≈ 6.4×10⁻³,
    注册容差 10⁻² (×10⁻⁸ 单位 10⁶); 实际偏差 3.0×10⁻³。 -/
theorem C7_zlevel_crossproduct :
    (c7_z_level_x1e4 * c7_sigma_LR_pp_x1e4 - 2521000000).natAbs ≤ 1000000 := by decide

/-- C7 程序量纲核对: LR_pct − 12 = 25.21 > 0 — 学习率远在红锚
    (12%) 上方 (v1.0 §2 C7 红界 LR < 12)。 -/
theorem C7_margin_positive : 1200 < c7_LR_pct_x100 := by decide

/-- C7 t_β 与 z_traj 分量一致: L2a 统计量 = C7 的 z_traj 分量
    (同一 log-log 斜率 t; 冻结双报告: L2a 用 z_traj 斜率读数,
    L3-level-v2 用 z_level 学习率裕度读数)。 -/
theorem C7_dual_reporting : zL2a_x1e4 = ztrajC7_x1e4 := by decide

-- ============================================================
-- §8 τ 读数 (可解释性, 非检验统计量)
-- ============================================================

/-! τ_i = (θ_i − M_i)/b_i; σ_τ = (1/|b|)·√(σ_M² + τ²·SE(b)²)
    (δ 法)。水平型通道 C1/C5/C8; 速率型通道 (C3/C4) τ 需二阶
    趋势, 未注册 — 通道判决 (红) 即读数。C8 锚 θ = 30 是绿线
    (解锁侧读「至绿线年数」)。τ 差检验为 v3 候选, v2 未注册。 -/

/-- C1 τ 记录值: θ = 0 (M1 红线), M = 0.0334 (×10⁴),
    b = −0.025257 (×10⁶), τ = 1.32 yr (×10²),
    σ_τ = 1.17 (×10²), σ_M = 0.0294 (×10⁴)。 -/
abbrev tauC1_theta : Int := 0
abbrev tauC1_M_x1e4 : Int := 334
abbrev tauC1_b_x1e6 : Int := -25257
abbrev tauC1_tau_x100 : Int := 132
abbrev tauC1_sigma_tau_x100 : Int := 117
abbrev tauC1_sigma_M_x1e4 : Int := 294

/-- C5 τ 记录值: θ = 85 (M5b 红界), M = 75.62 (×10²),
    b = +2.1775 (×10⁴), τ = 4.31, σ_τ = 0.58, σ_M = 1.261。 -/
abbrev tauC5_theta_x100 : Int := 8500
abbrev tauC5_M_x100 : Int := 7562
abbrev tauC5_b_x1e4 : Int := 21775
abbrev tauC5_tau_x100 : Int := 431
abbrev tauC5_sigma_tau_x100 : Int := 58
abbrev tauC5_sigma_M_x1e3 : Int := 1261

/-- C8 τ 记录值: θ = 30 (M8a 绿线, 解锁侧), M = 20.301 (×10³),
    b = +2.7171 (×10⁴), τ = 3.57, σ_τ = 1.19, σ_M = 2.458。 -/
abbrev tauC8_theta_x100 : Int := 3000
abbrev tauC8_M_x1e3 : Int := 20301
abbrev tauC8_b_x1e4 : Int := 27171
abbrev tauC8_tau_x100 : Int := 357
abbrev tauC8_sigma_tau_x100 : Int := 119
abbrev tauC8_sigma_M_x1e3 : Int := 2458

/-- C1 τ 交叉乘积: τ·|b| ≈ M − θ = 0.0334 (τ 记录 2 位 ⇒
    传播界 0.005×0.02526 ≈ 1.3×10⁻⁴; 实际偏差 6.1×10⁻⁵,
    容差 10⁻³ 于 ×10⁻⁸ 单位 = 10⁵)。 -/
theorem tauC1_cross :
    (132 * 25257 - 3340000 : Int).natAbs ≤ 100000 := by decide

/-- C1 σ_M 口径恒等式: 12·σ_M² ≈ σ_annual² (0.1017²;
    12 月滑动均值的测量 σ = 年均残差/√12)。实际偏差
    2.9×10⁻⁵ (×10⁻⁸ 单位 2,943 ≤ 10⁴)。 -/
theorem tauC1_sigmaM_squared :
    (12 * 294 * 294 - 1017 * 1017 : Int).natAbs ≤ 10000 := by decide

/-- C1 τ 方向登记: b < 0 (M1 裕度收缩) 且 τ > 0 — 距红线
    ≈ 1.32 yr, σ_τ = 1.17 (误差与点估计同量级, 读数弱)。 -/
theorem tauC1_direction : tauC1_b_x1e6 < 0 ∧ 0 < tauC1_tau_x100 := by decide

/-- C5 τ 交叉乘积: τ·b ≈ θ − M = 9.38 (实际偏差 5.0×10⁻³,
    传播界 0.005×2.1775 ≈ 1.1×10⁻², 容差 1.5×10⁻² 于 ×10⁻⁶
    单位 = 15000)。 -/
theorem tauC5_cross :
    (431 * 21775 - 9380000 : Int).natAbs ≤ 15000 := by decide

/-- C5 τ 读数: 4.31 yr 至红界 (σ_τ = 0.58) — 水平型读数中
    最紧的一个 (CO₂ 裕度按当前速率约 4.3 年入红带)。 -/
theorem tauC5_reading : 0 < tauC5_tau_x100 ∧ tauC5_sigma_tau_x100 < tauC5_tau_x100 := by
  decide

/-- C8 τ 交叉乘积: τ·b ≈ θ − M = 9.699 (实际偏差 1.0×10⁻³
    ≤ 容差 10⁻² 于 ×10⁻⁶ 单位 = 10⁴)。 -/
theorem tauC8_cross :
    (357 * 27171 - 9699000 : Int).natAbs ≤ 10000 := by decide

/-- C8 τ 读数: 3.57 yr 至绿线 (30%, 解锁侧正向读数,
    σ_τ = 1.19)。 -/
theorem tauC8_reading : 0 < tauC8_tau_x100 := by decide

-- ============================================================
-- §9 Bonferroni 通道级判决 (族内 m, α = 9.9×10⁻¹⁰ 单侧)
-- ============================================================

/-! 复合统计不校正 (花名册冻结 ⇒ 无选择 ⇒ 无校正); 阶梯全称
    语义合取保守; 禁析取声明 (v2 §guards.multiple_comparison)。
    climate_carbon 族 m = 4 (C1/C3/C4/C5), energy/information
    族 m = 1 (C7/C8)。 -/

/-- **C5 z_level 通道级显著**: 7.436 ≥ 6.22 (m = 4 Bonferroni)。 -/
theorem bonf_C5_significant : 62200 ≤ zlvlC5_x1e4 := by decide

/-- **C7 z_level 通道级显著**: 26.6713 ≥ 6.00 (m = 1)。 -/
theorem bonf_C7_significant : 60000 ≤ c7_z_level_x1e4 := by decide

/-- **C7 z_traj 通道级显著**: 9.7766 ≥ 6.00 (m = 1)。 -/
theorem bonf_C7_traj_significant : 60000 ≤ ztrajC7_x1e4 := by decide

/-- C1 z_level 不显著: 0.3288 < 6.22 (m = 4)。 -/
theorem bonf_C1_not : zlvlC1_x1e4 < 62200 := by decide

/-- C4 z_level 不显著: −0.0669 < 6.22。 -/
theorem bonf_C4_not : zlvlC4_x1e4 < 62200 := by decide

/-- C8 z_level 不显著: 2.1565 < 6.00 (m = 1)。 -/
theorem bonf_C8_not : zlvlC8_x1e4 < 60000 := by decide

/-- C1 z_traj 不显著 (m = 4): −3.7229 < 6.22。 -/
theorem bonf_C1_traj_not : ztrajC1_x1e4 < 62200 := by decide

/-- C3 z_traj 不显著 (m = 4, 折合未截值): −27.8705 < 6.22 —
    负向大 |z| 是压力侧恶化确定性, 非安全方向显著。 -/
theorem bonf_C3_traj_not : ztrajC3_x1e4 < 62200 := by decide

/-- C4 z_traj 不显著 (m = 4): −4.4775 < 6.22。 -/
theorem bonf_C4_traj_not : ztrajC4_x1e4 < 62200 := by decide

/-- C5 z_traj 不显著 (m = 4): −25.8784 < 6.22。 -/
theorem bonf_C5_traj_not : ztrajC5_x1e4 < 62200 := by decide

/-- C8 z_traj 不显著 (m = 1): 1.4623 < 6.00。 -/
theorem bonf_C8_traj_not : ztrajC8_x1e4 < 60000 := by decide

/-- 通道级显著集合登记 (基线快照): 恰为 C5 (z_level) 与 C7
    (z_level, z_traj) — 全部 12 个通道级语句中 3 个显著,
    9 个不显著 (如实登记, 无析取声明)。 -/
theorem bonf_summary :
    (62200 ≤ zlvlC5_x1e4) ∧ (60000 ≤ c7_z_level_x1e4) ∧ (60000 ≤ ztrajC7_x1e4)
    ∧ (zlvlC1_x1e4 < 62200) ∧ (zlvlC4_x1e4 < 62200) ∧ (zlvlC8_x1e4 < 60000) := by
  decide

-- ============================================================
-- §10 实现守卫公式字符串 (12 条, 管线 v5 字节级断言)
-- ============================================================

/-- 主公式字符串 (6 条, v2 预注册 implementation_guards.formula_strings):
    管线 v5 于声明层计算前逐条字节级断言, 失配即中止。 -/
def guardFormulas : List String :=
  [ "z_traj_i = s_i * t_i / sqrt(10)"
  , "cap_c = 5.0"
  , "Z_R = (Z_unlock + Z_pressure) / sqrt(2)"
  , "Z_L1 = sqrt(sum(t_i^2)) / sqrt(10)"
  , "sigma_LR_pp = 100 * ln(2) * (1 - LR) * SE(beta)"
  , "tau_i = (theta_i - M_i) / b_i" ]

/-- 次公式字符串 (6 条, secondary_formula_strings)。 -/
def guardFormulasSecondary : List String :=
  [ "z_level_C7 = (LR_pct - 12) / sigma_LR_pp"
  , "Z_R_traj = (Z_unlock_traj + Z_pressure_traj) / sqrt(2)"
  , "Z_T = (Z_Tunlock + Z_Tpressure) / sqrt(2)"
  , "z_entering_synthesis = sign(z) * min(|z|, c)"
  , "sigma_tau = (1/|b|) * sqrt(sigma_M^2 + tau^2 * SE(b)^2)"
  , "z_C3 = min(z_GIS, z_AIS)" ]

/-- 守卫公式计数: 主 6 + 次 6 = 12。 -/
theorem guard_formula_count :
    guardFormulas.length = 6 ∧ guardFormulasSecondary.length = 6 := by decide

/-- 首条守卫公式字节级登记: z_traj 冻结公式。 -/
theorem guard_formula_0 :
    guardFormulas.head? = some "z_traj_i = s_i * t_i / sqrt(10)" := by decide

/-- 第二条: 贡献上限冻结值 c = 5.0。 -/
theorem guard_formula_1 :
    (guardFormulas.getD 1 "") = "cap_c = 5.0" := by decide

/-- 第三条: Z_R 和式 (A3-1 语义延续到声明层)。 -/
theorem guard_formula_2 :
    (guardFormulas.getD 2 "") = "Z_R = (Z_unlock + Z_pressure) / sqrt(2)" := by decide

/-- C3 折合守卫 (次表末条): 最劣流域规则。 -/
theorem guard_formula_secondary_5 :
    (guardFormulasSecondary.getD 5 "") = "z_C3 = min(z_GIS, z_AIS)" := by decide

-- ============================================================
-- §11 溯源注册表 (SHA256 与再生命令)
-- ============================================================

/-! 声明层预注册与快照链的 SHA256 注册表 (v5 快照
    pipeline.preregistration + 声明层节登记 + 快照文件自身
    哈希 2026-08-30 冻结后计算)。Lean 仅登记字符串; 哈希一致
    性核对在管线/审计层完成 (同 T3 §7 / DataProvenance §5)。 -/

def claimPreregV2MdSha256 : String :=
  "9E77BF987B563C072C8125D9B87BFAAA3CA34FC363781587F2CF884164379620"

def claimPreregV2JsonSha256 : String :=
  "9F9E3A67CFB18A7C5CB94397E4BAA1C69E2815C0C800B6096CA4F63EB5C623F5"

def snapshotV5Sha256 : String :=
  "89129A6DAF0FCC9413F87C2E796DDE0E4700FD05CDC95F65421969317B652392"

def snapshotV4Sha256 : String :=
  "0B655C69B2ACFA5EBF1D77BF89D5A5355186293047CF1E7A38C8741DFFC8D1AE"

def amendmentA3MdSha256 : String :=
  "5F1C05C7115967A4CF054C31AE700A4CC6652DCB85DB26EF4EA5AA58BDFE9325"

def amendmentA3JsonSha256 : String :=
  "C02C4310967FBE87E4E6A83FD98775C5006DCF6297B5568CBD215C4677F2BE5A"

def frameworkV1DraftSha256 : String :=
  "CA285261B843D84241411466729208729E60BF93CF45475AF166795ACDE1E9BA"

def pipelineV5ScriptPath : String := "H:\\cdd_lean4\\scripts\\cdd_ecs_channel_pipeline_v5.py"

def snapshotV5Path : String := "H:\\cdd_ecs_channel_pipeline_results_v5.json"

def regenerationCommandV5 : String := "python H:\\cdd_lean4\\scripts\\cdd_ecs_channel_pipeline_v5.py"

/-- 哈希格式核对: 七个注册 SHA256 均为 64 个十六进制字符长度。 -/
theorem sha256_format :
    claimPreregV2MdSha256.length = 64 ∧ claimPreregV2JsonSha256.length = 64
    ∧ snapshotV5Sha256.length = 64 ∧ snapshotV4Sha256.length = 64
    ∧ amendmentA3MdSha256.length = 64 ∧ amendmentA3JsonSha256.length = 64
    ∧ frameworkV1DraftSha256.length = 64 := by decide

-- ============================================================
-- §12 T4 验证汇总 (项目惯例: 同 T3 summary)
-- ============================================================

/-- T4 verification summary: 声明层冻结判据锚点与 v5 基线快照
    核心结论合取。

    G1-G4 声明阶梯/T 系列结构与阈值; G5-G8 守卫与 Bonferroni;
    G9-G10 L1 判决与算术; G11 L2a 判决; G12 L2b 不可判;
    G13-G15 L3-v2 判决与对照; G16-G20 L3-level 合成算术;
    G21-G24 L3-traj 合成算术与判决; G25 C3 折合; G26-G29 C7
    程序; G30-G33 τ 读数; G34-G37 Bonferroni 通道级;
    G38-G39 守卫公式字符串; G40 溯源格式 (7 注册哈希)。 -/
theorem T4_verification_summary :
    governancePressureT.length + transitionUnlockT.length = 8 ∧      -- G1: L4 分区 3+5=8
    zTrajRoster.length = 6 ∧                                          -- G2: z_traj 花名册 6 通道
    (levelThreshold ClaimLevel.L1 = some 6 ∧ levelThreshold ClaimLevel.L2a = some 6
      ∧ levelThreshold ClaimLevel.L2b = some 6 ∧ levelThreshold ClaimLevel.L3 = some 6
      ∧ levelThreshold ClaimLevel.L4 = some 6 ∧ levelThreshold ClaimLevel.L5 = none) ∧  -- G3: 阈值表
    (confirmationWindow ClaimLevel.L3 = some 3
      ∧ confirmationWindow ClaimLevel.L4 = some 5
      ∧ confirmationWindow ClaimLevel.L5 = some 5) ∧                 -- G4: 确认窗口表
    cap_c < sigma6 ∧                                                  -- G5: 单通道上限 < 6σ
    (bonferroni_m1 < bonferroni_m2 ∧ bonferroni_m2 < bonferroni_m3
      ∧ bonferroni_m3 < bonferroni_m4 ∧ bonferroni_m4 < bonferroni_m8) ∧  -- G6: Bonferroni 单调
    firstEligibleSnapshotYear < l3EarliestConfirmationYear ∧          -- G7: 2027 < 2029
    l4ActivationYearApprox < l4EarliestConfirmationYearApprox ∧       -- G8: L4 时钟
    60000 ≤ ZL1_x1e4 ∧                                                -- G9: L1 判决 ≥ 6σ
    (ZL1_x1e4 * ZL1_x1e4 - chi2_x100 * 1000000).natAbs ≤ 1000000 ∧    -- G10: Z_L1² ≈ χ²
    60000 ≤ zL2a_x1e4 ∧                                               -- G11: L2a 判决 ≥ 6σ
    l2b_n_obs < l2b_decidability_gate ∧                               -- G12: L2b series_short
    ZR_v2_x1e4 < 60000 ∧                                              -- G13: L3-v2 未达
    60000 - ZR_v2_x1e4 = 2736 ∧                                       -- G14: 差距 0.2736σ
    (ZR_v1_x1e4 < ZR_v2_x1e4 ∧ ZR_v2_x1e4 - ZR_v1_x1e4 = 20533) ∧   -- G15: v2 > v1 (C7 补全)
    zlvlC1_x1e4 + zlvlC4_x1e4 + zlvlC5_capped_x1e4 = 52619 ∧          -- G16: 压力和恒等式
    (3 * Zp_v2_x1e4 * Zp_v2_x1e4 - 52619 * 52619).natAbs ≤ 1000000 ∧  -- G17: 压力 Stouffer
    (2 * Zu_v2_x1e4 * Zu_v2_x1e4 - 71565 * 71565).natAbs ≤ 1000000 ∧  -- G18: 解锁 Stouffer
    (2 * ZR_v2_x1e4 * ZR_v2_x1e4 - 80984 * 80984).natAbs ≤ 1000000 ∧  -- G19: Z_R(v2) 平方
    (2 * pcb_v2_x1e4 * pcb_v2_x1e4 - 68144 * 68144).natAbs ≤ 1000000 ∧ -- G20: pcb(v2) 平方
    2 * Zptraj_x1e4 = -182004 ∧                                       -- G21: traj 压力精确半和
    4 * pressureTrajMean_x1e4 = -182004 ∧                             -- G22: traj 族均值精确
    (2 * ZRtraj_x1e4 * ZRtraj_x1e4 - 45307 * 45307).natAbs ≤ 1000000 ∧ -- G23: Z_R_traj 平方
    ZRtraj_x1e4 < 0 ∧                                                  -- G24: traj 负值语义
    (ztrajC3AIS_x1e4 ≤ ztrajC3GIS_x1e4
      ∧ ztrajC3_x1e4 = ztrajC3AIS_x1e4) ∧                             -- G25: C3 折合 min
    zlvlC7_x1e4 > 50000 ∧                                              -- G26: C7 截断 (广度代价)
    (c7_z_level_x1e4 * c7_sigma_LR_pp_x1e4 - 2521000000).natAbs ≤ 1000000 ∧ -- G27: C7 交叉积
    zL2a_x1e4 = ztrajC7_x1e4 ∧                                        -- G28: C7 双报告一致
    1200 < c7_LR_pct_x100 ∧                                           -- G29: LR 裕度 > 红锚
    (132 * 25257 - 3340000 : Int).natAbs ≤ 100000 ∧                   -- G30: τ_C1 交叉积
    (431 * 21775 - 9380000 : Int).natAbs ≤ 15000 ∧                    -- G31: τ_C5 交叉积
    (357 * 27171 - 9699000 : Int).natAbs ≤ 10000 ∧                    -- G32: τ_C8 交叉积
    (12 * 294 * 294 - 1017 * 1017 : Int).natAbs ≤ 10000 ∧             -- G33: σ_M 口径恒等式
    62200 ≤ zlvlC5_x1e4 ∧                                             -- G34: C5 通道级显著
    60000 ≤ c7_z_level_x1e4 ∧                                         -- G35: C7 level 显著
    60000 ≤ ztrajC7_x1e4 ∧                                            -- G36: C7 traj 显著
    zlvlC8_x1e4 < 60000 ∧                                             -- G37: C8 不显著
    (guardFormulas.length = 6 ∧ guardFormulasSecondary.length = 6) ∧  -- G38: 守卫公式 12 条
    guardFormulas.head? = some "z_traj_i = s_i * t_i / sqrt(10)" ∧    -- G39: 首条字节级
    (claimPreregV2MdSha256.length = 64 ∧ claimPreregV2JsonSha256.length = 64
      ∧ snapshotV5Sha256.length = 64 ∧ snapshotV4Sha256.length = 64
      ∧ amendmentA3MdSha256.length = 64 ∧ amendmentA3JsonSha256.length = 64
      ∧ frameworkV1DraftSha256.length = 64) :=                        -- G40: 哈希格式 (7 注册)
  ⟨t_partition_count, ztraj_roster_count,
    level_thresholds, confirmation_windows,
    cap_below_six_sigma, bonferroni_monotone, clock_order, l4_clock_order,
    L1_threshold_met, L1_squared_chi2, L2a_threshold_met, L2b_series_short,
    L3_v2_not_met, L3_v2_gap, L3_v2_improves_v1, L3_pressure_sum_identity,
    L3_pressure_stouffer_squared, L3_unlock_stouffer_squared_v2,
    L3_ZR_squared_v2, L3_pcb_squared_v2, L3traj_pressure_half,
    L3traj_pressure_mean, L3traj_ZR_squared, L3traj_negative, c3_fold_rule,
    c7_cap_binds_breadth_cost, C7_zlevel_crossproduct, C7_dual_reporting,
    C7_margin_positive, tauC1_cross, tauC5_cross, tauC8_cross,
    tauC1_sigmaM_squared, bonf_C5_significant, bonf_C7_significant,
    bonf_C7_traj_significant, bonf_C8_not, guard_formula_count,
    guard_formula_0, sha256_format⟩

end CDD.T4.ClaimLadder
