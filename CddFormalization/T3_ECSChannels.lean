import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.NormNum

/-! # T3 ECS Channels: CDD-ECS 6+2 预注册通道判据的形式化登记

    CDD-ECS (地球环境-文明交互理论) C 系列通道预注册判据的 Lean 锚点
    登记, 实现预注册文档 §8 的 T3-g 接口条款:
    - §2 预注册阈值的**精确有理数锚点** (冻结于 v1.0; 修订案 A1/A2
      阈值变更数均为 0, 仅提供路由/常数与 C1 指标符号澄清);
    - §1 通道计数一致性定理: 6 压力通道 + 2 解锁通道 = 8;
    - §5 Stouffer 合成分离语义定理: 压力/解锁通道不混同;
    - §3/§4/§6 v3 快照按「记录的统计结果」口径登记 (同
      T2_Validation v8 P0 澄清): `decide` 证明核对的是**记录值与
      预注册阈值的算术比较**, 不构成从原始数据到结论的形式化推导;
      物理有效性取决于数据管线。

    ## 事件顺序 (预注册纪律)

    ```
    v1.0 判据冻结 (SHA256 登记)
      → v1 管线首跑 (快照 v1, 冻结不覆盖)
      → 数据源可达性/格式探针 (无指标计算)
      → 修订案 A1 登记 (阈值变更 = 0)
      → v2 管线重跑 (快照 v2, 冻结不覆盖)
      → 运行后判决复查 (发现 C1 符号缺陷; 无阈值查看/调整)
      → 修订案 A2 登记 (阈值变更 = 0; C1 裕度形式 M1 = 1.5 − T_12m)
      → v3 管线重跑 (快照 v3)
      → 运行后合成复查 (发现 Z_gap 方向缺陷; 无阈值查看/调整)
      → 修订案 A3 登记 (阈值/判决/状态机变更 = 0;
        Z_gap 和式形式 Z_unlock + Z_pressure)
      → v4 管线重跑 (快照 v4, 本模块 §5.5 登记其合成层)
    ```

    ## 溯源链 (每一记录值)

    ```
    原始数据 (缓存 H:\cdd_ecs_data, 逐文件 SHA256 登记于快照)
      → Python 管线 cdd_lean4/scripts/cdd_ecs_channel_pipeline_v3.py
        (A2 §4 implementation guard: 冻结公式字符串断言先行)
      → JSON 快照 H:\cdd_ecs_channel_pipeline_results_v3.json
        (SHA256 5409F01F…29026)
      → 本模块: 判据锚点 (Rat) + 记录值算术一致性核对 (Int 缩放)
    ```

    ## 形式化范围 (诚实声明)

    - z 值按快照**记录值**登记 (管线以未舍入中间值计算 z = margin/σ),
      本模块不重算通道 z, 仅核对合成层算术 (§5);
    - 全局状态机 `stateOf` 为管线 `synthesize()` 的逐字镜像 (§3);
    - Z_gap 是 R 的**方向代理**, 不等于 R (预注册 §2.3 原文);
    - pending_data 通道 (C2/C6) 排除于合成, 路由阻断如实登记 (A1-8);
    - A2-1 不变量: |M1_v2| = |M1_v3| (同一 T_12m 的纯符号翻转),
      v2 快照的 C1 判决及下游 (TRIGGER_PREP) 被 v3 取代 (A2 §0.5),
      符号翻转恒等式于 §6 显式登记;
    - 口径: 本模块是 "预注册判据与 v3 快照统计结果的**形式化记录**",
      非 "从原始数据到结论的形式化推导"。

    CDD Framework v28.4 · CDD-ECS C 系列
    Date: 2026-08-30
    All proofs use ONLY core Lean4 tactics (decide) and Mathlib norm_num.
-/

namespace CDD.T3.ECSChannels

-- ============================================================
-- §1 通道枚举、方向分区与计数一致性
-- ============================================================

/-- C 系列 8 通道 (预注册 v1.0 §1): C1-C6 压力通道 + C7-C8 解锁通道。 -/
inductive ECSChannel where
  | C1_temperature
  | C2_amoc
  | C3_icesheets
  | C4_biosphere
  | C5_biogeochemical
  | C6_social
  | C7_energy
  | C8_information
  deriving DecidableEq

/-- 通道四态编码 (预注册 §2.1): green = 裕度充足 / yellow = 警戒带 /
    red = 预注册红界触发 / pending_data = 质量门槛未过 (不参与合成)。 -/
inductive ECSStatus where
  | green
  | yellow
  | red
  | pending_data
  deriving DecidableEq

/-- 全局窗口状态 (预注册 §2.2 状态机 + 中止规则状态)。 -/
inductive ECSGlobalState where
  | STABLE              -- 轨道 A 倾向 (R > 1 区, 相变腿健康)
  | CRITICAL            -- 临界带 R ≈ 1
  | TRIGGER_PREP        -- S2 预备 (压力红 = 3)
  | TRIGGER             -- S2 对冲触发
  | CHANNEL_REPORT_ONLY -- 中止规则: pending ≥ 3, 仅通道级报告
  deriving DecidableEq

/-- 方向分区: 压力通道 (恶化方向) = true; 解锁通道 (扩张方向) = false。
    预注册 §1: 压力 = C1-C6, 解锁 = C7-C8。 -/
def isPressure : ECSChannel → Bool
  | .C1_temperature => true
  | .C2_amoc => true
  | .C3_icesheets => true
  | .C4_biosphere => true
  | .C5_biogeochemical => true
  | .C6_social => true
  | .C7_energy => false
  | .C8_information => false

/-- 压力通道列表 (管线 pressure_ids 逐字镜像)。 -/
def pressureChannels : List ECSChannel :=
  [.C1_temperature, .C2_amoc, .C3_icesheets, .C4_biosphere, .C5_biogeochemical, .C6_social]

/-- 解锁通道列表 (管线 unlock_ids 逐字镜像)。 -/
def unlockChannels : List ECSChannel :=
  [.C7_energy, .C8_information]

/-- 通道计数一致性 (T3-g 条款 1): 6 压力 + 2 解锁 = 8。 -/
theorem six_pressure_channels : pressureChannels.length = 6 := by decide

theorem two_unlock_channels : unlockChannels.length = 2 := by decide

theorem channel_count_consistency :
    pressureChannels.length + unlockChannels.length = 8 := by decide

/-- 压力列表成员全部为压力方向 (与 isPressure 分区一致)。 -/
theorem pressure_list_consistent : (pressureChannels.all isPressure) = true := by decide

/-- 解锁列表成员全部为解锁方向。 -/
theorem unlock_list_consistent : (unlockChannels.all (fun c => !isPressure c)) = true := by decide

/-- 压力/解锁列表互斥 (同一构造符不出现在两个列表)。 -/
theorem pressure_unlock_disjoint :
    (pressureChannels.any (fun c => unlockChannels.any (fun u => decide (c = u)))) = false := by
  decide

-- ============================================================
-- §2 预注册阈值有理数锚点 (v1.0 冻结, A1/A2 阈值变更 = 0)
-- ============================================================

/-! ### C1 温度路径 (压力)

    指标 M1 = 1.5°C − T_12m (1850-1900 基线, °C; **A2-1 裕度形式**:
    修订案 A2 [F] 澄清 v1.0 字面 M1 = T_12m − 1.5 的符号反转,
    阈值带数值逐字不变; M1 越大 = 距 1.5°C 红线越安全)。
    判据 [T/L]: green M1 > 0.30; yellow 0 < M1 ≤ 0.30; red M1 ≤ 0。
    交叉源分歧门槛 [O]: |GISTEMP − HadCRUT5| > 0.10°C → 降级 yellow。
    1.5°C 来源: Armstrong McKay 2022 十六要素中位临界阈值。
    z 程序 θ_red = 0 (红界在 M 下方, z = (M−θ)/σ, 越大越安全)。 -/

/-- C1 1.5°C 目标锚点 (T_12m 的红界目标; M1 的被减数, A2-1 形式)。 -/
abbrev c1_target_C : Rat := mkRat 3 2

/-- C1 green 下界: M1 > 0.30 (°C)。 -/
abbrev c1_green_M1 : Rat := mkRat 3 10

/-- C1 red 上界: M1 ≤ 0 (°C); 兼 Stouffer z 程序的 θ_red。 -/
abbrev c1_red_M1 : Rat := mkRat 0 1

/-- C1 交叉源分歧门槛: 0.10 (°C)。 -/
abbrev c1_crossgate_C : Rat := mkRat 1 10

/-- C1 带序: 红界 (0) 严格低于 green 界 (0.30) — 黄带非空。 -/
theorem c1_band_order : c1_red_M1 < c1_green_M1 := by decide

/-! ### C2 AMOC (压力)

    指标 M2a = RAPID 26.5°N 年均值 OLS 趋势 (Sv/decade) + t;
    M2b = 最近 5 年均值 − 10 Sv (崩溃阈值裕度)。
    判据 [T/L]: green |t| < 2 ∧ M2b > 5; yellow t < −2 ∨ M2b ≤ 5;
    red t < −2 ∧ 外推 2060 前跌破 10 Sv。
    10 Sv = collapse 判据 [L]; 15 Sv 警戒界 [O] = 裕度 5 + 10。
    z 程序 θ_red = 5 (红锚, 裕度口径)。 -/

/-- C2 崩溃阈值: 10 (Sv)。 -/
abbrev c2_collapse_Sv : Rat := mkRat 10 1

/-- C2 警戒裕度: 5 (Sv, M2b ≤ 5 → yellow); 兼 z 程序 θ_red。 -/
abbrev c2_warning_margin_Sv : Rat := mkRat 5 1

/-- C2 警戒水位: 15 (Sv, 5 年均值口径, 预注册 [L] 注记)。 -/
abbrev c2_warning_level_Sv : Rat := mkRat 15 1

/-- C2 趋势显著性门槛: |t| = 2。 -/
abbrev c2_t_threshold : Rat := mkRat 2 1

/-- C2 裕度-水位换算: 裕度 5 + 崩溃 10 = 警戒水位 15。 -/
theorem c2_margin_level_identity :
    c2_warning_margin_Sv + c2_collapse_Sv = c2_warning_level_Sv := by
  norm_num [c2_warning_margin_Sv, c2_collapse_Sv, c2_warning_level_Sv]

/-- C2 带序: 裕度 5 < 崩溃 0 裕度 (=10 Sv 水位)。 -/
theorem c2_band_order : c2_warning_margin_Sv < c2_collapse_Sv := by decide

/-! ### C3 冰盖流域 (压力)

    指标 M3a = GIS 近 10 年质量通量 (Gt/yr, 正 = 损失);
    M3b = AIS 同法。
    判据 [O]: green GIS < 150 ∧ AIS < 100; yellow GIS 150-270 ∨
    AIS 100-180; red GIS > 270 ∨ AIS > 180 ∨ 外推 2100 合计 SLR > 1 m。
    A1-6 常数: 360 Gt/mm 换算; 270 Gt/yr ≈ 0.75 mm/yr SLR 量级 [L]。 -/

abbrev c3_gis_yellow : Rat := mkRat 150 1
abbrev c3_gis_red : Rat := mkRat 270 1
abbrev c3_ais_yellow : Rat := mkRat 100 1
abbrev c3_ais_red : Rat := mkRat 180 1

/-- C3 外推 SLR 红界: 1000 (mm = 1 m)。 -/
abbrev c3_slr_red_mm : Rat := mkRat 1000 1

/-- C3 A1-6 冰-水换算常数: 360 (Gt/mm)。 -/
abbrev c3_gt_per_mm : Rat := mkRat 360 1

theorem c3_gis_band_order : c3_gis_yellow < c3_gis_red := by decide
theorem c3_ais_band_order : c3_ais_yellow < c3_ais_red := by decide

/-- C3 GIS 红界速率的 SLR 换算: 270 Gt/yr = 360 × (3/4) Gt/yr
    = 0.75 mm/yr (来源层 [L] 量级注记的精确化)。 -/
theorem c3_gis_red_slr_rate : c3_gt_per_mm * mkRat 3 4 = c3_gis_red := by
  norm_num [c3_gt_per_mm, c3_gis_red]

/-! ### C4 生物圈 (压力)

    指标 M4a = OHC 0-2000m 近 10 年趋势 (ZJ/yr);
    M4b = 亚马逊旱季降水 10 年均值偏差 (σ)。
    判据 [O]: green M4a < 5 ∧ M4b > −1; yellow M4a ∈ [5,10] ∨
    M4b ∈ [−2,−1]; red M4a > 10 ∨ 连续 3 年 M4b < −2。
    A1-5 部分可判定: 仅 M4a 时, > 10 → red (可判定),
    [5,10] → yellow (可判定), < 5 → pending (依赖 M4b)。 -/

abbrev c4_ohc_yellow : Rat := mkRat 5 1
abbrev c4_ohc_red : Rat := mkRat 10 1
abbrev c4_precip_yellow : Rat := mkRat (-1) 1
abbrev c4_precip_red : Rat := mkRat (-2) 1

theorem c4_ohc_band_order : c4_ohc_yellow < c4_ohc_red := by decide
theorem c4_precip_band_order : c4_precip_red < c4_precip_yellow := by decide

/-! ### C5 生物地球化学 (压力)

    指标 M5a = PB2023 越界数 (文献快照, F* 层);
    M5b = 全球年均 CO2 − 350 ppm。
    判据 [T/L]: green M5a ≤ 4 ∧ M5b < 70; yellow M5a = 5 ∨
    M5b ∈ [70,85]; red M5a ≥ 6 ∧ M5b ≥ 85。
    350 ppm = PB 气候边界 [T/L]。 -/

abbrev c5_pb_green : Rat := mkRat 4 1
abbrev c5_pb_yellow : Rat := mkRat 5 1
abbrev c5_pb_red : Rat := mkRat 6 1
abbrev c5_pb_boundary_ppm : Rat := mkRat 350 1
abbrev c5_co2_yellow : Rat := mkRat 70 1
abbrev c5_co2_red : Rat := mkRat 85 1

theorem c5_pb_band_order : c5_pb_green < c5_pb_yellow ∧ c5_pb_yellow < c5_pb_red := by decide
theorem c5_co2_band_order : c5_co2_yellow < c5_co2_red := by decide

/-- C5 黄带浓度水位: 350 + 70 = 420 ppm。 -/
theorem c5_yellow_co2_ppm : c5_pb_boundary_ppm + c5_co2_yellow = mkRat 420 1 := by
  norm_num [c5_pb_boundary_ppm, c5_co2_yellow]

/-- C5 红界浓度水位: 350 + 85 = 435 ppm; 兼 z 程序的 θ_red (裕度口径 85)。 -/
theorem c5_red_co2_ppm : c5_pb_boundary_ppm + c5_co2_red = mkRat 435 1 := by
  norm_num [c5_pb_boundary_ppm, c5_co2_red]

/-! ### C6 社会结构 (压力)

    指标 M6a = 美国实际家庭收入中位数距峰值年数 (yr)。
    判据 [O/L]: green M6a < 5; yellow M6a ∈ [5,15]; red M6a > 15。
    15 yr ≈ 1970s-1980s 结构性危机停滞时长 (Turchin SDT [L])。
    z 程序: 时长计数指标, 无可观测 σ → 数值合成排除 (§5)。 -/

abbrev c6_yellow : Rat := mkRat 5 1
abbrev c6_red : Rat := mkRat 15 1

theorem c6_band_order : c6_yellow < c6_red := by decide

/-! ### C7 能源解锁 (解锁, 正向)

    指标 M7a = PV LCOE 对数学习率 LR = 1 − 2^β (%);
    M7b = LCOE 5 年 CAGR 降幅 (%/yr)。
    判据 [L/O]: green LR ≥ 20 ∧ M7b ≥ 8; yellow LR ∈ [12,20) ∨
    M7b ∈ [3,8); red LR < 12 ∨ M7b < 3。
    20-24% 来源 BNEF/IRENA [L]; 12%/3% 为 [O]。
    解锁方向: red 界在 green 界**下方** (扩张力弱 = red)。
    A1-3: LCOE 单位 USD/kWh (判决不变, 比率/速率指标)。 -/

abbrev c7_lr_green : Rat := mkRat 20 1
abbrev c7_lr_red : Rat := mkRat 12 1
abbrev c7_cagr_green : Rat := mkRat 8 1
abbrev c7_cagr_red : Rat := mkRat 3 1

theorem c7_lr_band_order : c7_lr_red < c7_lr_green := by decide
theorem c7_cagr_band_order : c7_cagr_red < c7_cagr_green := by decide

/-! ### C8 信息-自动化 (解锁, 正向)

    指标 M8a = OECD 企业 AI 采用率最新值 (%);
    M8b = 采用率年变化 (pp/yr)。
    判据 [O/L]: green M8a ≥ 30 ∧ M8b ≥ 3; yellow M8a ∈ [15,30) ∨
    M8b ∈ [1,3); red M8a < 15 ∨ M8b < 1。
    2025 基线 20.2% [L] (OECD); 30% = 组织级传播假设 [O/L]。
    NBER 任务级生产率效应 (+14%~+40%) 为文献参数背景, 非机械判据。 -/

abbrev c8_adoption_green : Rat := mkRat 30 1
abbrev c8_adoption_red : Rat := mkRat 15 1
abbrev c8_growth_green : Rat := mkRat 3 1
abbrev c8_growth_red : Rat := mkRat 1 1

theorem c8_adoption_band_order : c8_adoption_red < c8_adoption_green := by decide
theorem c8_growth_band_order : c8_growth_red < c8_growth_green := by decide

-- ============================================================
-- §3 全局状态机 (预注册 §2.2, 管线 synthesize() 逐字镜像)
-- ============================================================

/-- S2 双红检查 (预注册 C2/C6 条款): C2 ∈ {red, yellow} 且 C6 = red。 -/
def s2DualRed (c2 c6 : ECSStatus) : Bool :=
  match c2, c6 with
  | .red, .red => true
  | .yellow, .red => true
  | _, _ => false

/-- 预注册 §2.2 窗口状态机。

    参数: `pendingTotal` = pending 通道总数; `s2` = S2 双红;
    `pRed`/`uRed`/`uYellow` = 压力红 / 解锁红 / 解锁黄计数。
    优先级: 中止规则 > TRIGGER (S2 双红 ∨ 压力红 ≥ 4) >
    TRIGGER_PREP (压力红 = 3) > CRITICAL (压力红 = 2 ∨ 解锁红 = 1 ∨
    解锁黄 = 2) > STABLE (压力红 ≤ 1 ∧ 解锁红 = 0) > 兜底 CRITICAL。
    TRIGGER_PERSISTENT (连续 5 年 CRITICAL 或更差) 为时序规则,
    单快照不可判定, 仅文档登记。 -/
def stateOf (pendingTotal : Nat) (s2 : Bool) (pRed uRed uYellow : Nat) : ECSGlobalState :=
  if 3 ≤ pendingTotal then .CHANNEL_REPORT_ONLY
  else if s2 = true ∨ 4 ≤ pRed then .TRIGGER
  else if pRed = 3 then .TRIGGER_PREP
  else if pRed = 2 ∨ uRed = 1 ∨ uYellow = 2 then .CRITICAL
  else if pRed ≤ 1 ∧ uRed = 0 then .STABLE
  else .CRITICAL

-- ============================================================
-- §4 v3 快照记录: 通道状态、计数与判决一致性
-- ============================================================

/-- v3 快照通道状态 (记录值)。

    来源: H:\cdd_ecs_channel_pipeline_results_v3.json #channels.*.status
    (SHA256 5409F01F…29026, 管线 v3.0, 2026-08-30T06:16:29Z)。
    C1 = yellow (A2-1 裕度形式 M1 = 0.0334 ∈ (0, 0.30];
    v2 快照 C1 = red 系旧公式符号反转所致, 被 A2 §0.5 取代)。
    C2/C6 = pending_data (A1-8 路由阻断, 无同机构替代路由,
    语义替代被预注册 §0.5 禁止)。 -/
def v3Status : ECSChannel → ECSStatus
  | .C1_temperature => .yellow
  | .C2_amoc => .pending_data
  | .C3_icesheets => .red
  | .C4_biosphere => .red
  | .C5_biogeochemical => .yellow
  | .C6_social => .pending_data
  | .C7_energy => .green
  | .C8_information => .yellow

/-- 按状态计数 (v3Status 的列表统计, 可计算)。 -/
def countStatus (chs : List ECSChannel) (s : ECSStatus) : Nat :=
  (chs.filter (fun c => decide (v3Status c = s))).length

/-- v3 压力红计数 = 2 (C3, C4; C1 降出红带)。 -/
theorem v3_pressure_red : countStatus pressureChannels ECSStatus.red = 2 := by decide

/-- v3 压力黄计数 = 2 (C1, C5)。 -/
theorem v3_pressure_yellow : countStatus pressureChannels ECSStatus.yellow = 2 := by decide

/-- v3 压力绿计数 = 0。 -/
theorem v3_pressure_green : countStatus pressureChannels ECSStatus.green = 0 := by decide

/-- v3 压力 pending 计数 = 2 (C2, C6)。 -/
theorem v3_pressure_pending : countStatus pressureChannels ECSStatus.pending_data = 2 := by decide

/-- v3 压力通道守恒: 红 2 + 黄 2 + 绿 0 + pending 2 = 6。 -/
theorem v3_pressure_conservation :
    countStatus pressureChannels ECSStatus.red
      + countStatus pressureChannels ECSStatus.yellow
      + countStatus pressureChannels ECSStatus.green
      + countStatus pressureChannels ECSStatus.pending_data = 6 := by decide

/-- v3 解锁红计数 = 0。 -/
theorem v3_unlock_red : countStatus unlockChannels ECSStatus.red = 0 := by decide

/-- v3 解锁黄计数 = 1 (C8)。 -/
theorem v3_unlock_yellow : countStatus unlockChannels ECSStatus.yellow = 1 := by decide

/-- v3 解锁绿计数 = 1 (C7)。 -/
theorem v3_unlock_green : countStatus unlockChannels ECSStatus.green = 1 := by decide

/-- v3 解锁通道守恒: 红 0 + 黄 1 + 绿 1 = 2。 -/
theorem v3_unlock_conservation :
    countStatus unlockChannels ECSStatus.red
      + countStatus unlockChannels ECSStatus.yellow
      + countStatus unlockChannels ECSStatus.green = 2 := by decide

/-- 中止规则 (预注册 §2.2): pending ≥ 3 → 仅通道级报告。
    v3: pending 总数 2 < 3, 全局状态已报告。 -/
theorem v3_abort_rule_not_fired :
    countStatus (pressureChannels ++ unlockChannels) ECSStatus.pending_data < 3 := by decide

/-- v3 S2 双红: C2/C6 均 pending → 未触发。 -/
theorem v3_s2_dual_red_not_fired :
    s2DualRed (v3Status ECSChannel.C2_amoc) (v3Status ECSChannel.C6_social) = false := by decide

/-- v3 全局状态 (主定理): 记录状态映射 → 状态机 → CRITICAL。

    pending = 2, S2 = false, 压力红 = 2, 解锁红 = 0, 解锁黄 = 1;
    对应快照 synthesis.state_machine = "CRITICAL"
    (A2 修正后自 v2 的 TRIGGER_PREP 降级: 压力红 3 → 2)。 -/
theorem v3_global_state :
    stateOf (countStatus (pressureChannels ++ unlockChannels) ECSStatus.pending_data)
      (s2DualRed (v3Status ECSChannel.C2_amoc) (v3Status ECSChannel.C6_social))
      (countStatus pressureChannels ECSStatus.red)
      (countStatus unlockChannels ECSStatus.red)
      (countStatus unlockChannels ECSStatus.yellow)
      = ECSGlobalState.CRITICAL := by decide

/-- v3 状态优先级: 压力红 = 2 (< 4) 且 S2 未触发 → 非 TRIGGER。 -/
theorem v3_state_not_trigger :
    stateOf 2 false 2 0 1 ≠ ECSGlobalState.TRIGGER := by decide

/-- v3 状态降级登记: 压力红 = 2 (< 3) → 非 TRIGGER_PREP
    (v2 的 TRIGGER_PREP 被 v3 取代, A2 §0.5)。 -/
theorem v3_state_not_trigger_prep :
    stateOf 2 false 2 0 1 ≠ ECSGlobalState.TRIGGER_PREP := by decide

-- ------------------------------------------------------------
-- §4.2 v3 记录指标与判决一致性 (记录值 vs 冻结阈值)
-- ------------------------------------------------------------

/-! 记录指标 (Int 缩放登记, 缩放因子见各注释)。

    来源: v3 快照 #channels.*.metrics / .intermediates。
    C1 ×10⁴ (°C; A2-1 裕度形式); C3 ×100 (Gt/yr, mm);
    C4 ×1000 (ZJ/yr); C5 ×100 (ppm) / 整数 (计数);
    C7 ×100 (%); C8 ×1000 (%, pp/yr)。 -/

/-- M1 = +0.0334 (°C; A2-1 裕度形式 1.5 − T_12m, GISTEMP
    2025-08…2026-07 滑动均值, A1-1 基线链)。 -/
abbrev v3_M1_x1e4 : Int := 334

/-- M3a = 245.07 (GIS 损失, Gt/yr; IMBIE 2020-02-28 近 10 年)。 -/
abbrev v3_M3a_x100 : Int := 24507

/-- M3b = 196.25 (AIS 损失, Gt/yr; IMBIE 2018-07-23 近 10 年)。 -/
abbrev v3_M3b_x100 : Int := 19625

/-- 外推 2100 合计 SLR = 118.82 (mm, A1-6 逐序列外推规则)。 -/
abbrev v3_slr2100_x100 : Int := 11882

/-- M4a = 10.521 (OHC 0-2000m 趋势, ZJ/yr; NCEI FTP NetCDF)。 -/
abbrev v3_M4a_x1000 : Int := 10521

/-- M5a = 6 (PB2023 越界数, 文献快照 F* 层, 非重算观测)。 -/
abbrev v3_M5a_pb : Int := 6

/-- M5b = 75.62 (ppm; NOAA GML 2025 年均值 425.62 − 350)。 -/
abbrev v3_M5b_x100 : Int := 7562

/-- M7a LR = 37.21 (%; OWID LCOE × capacity 对数学习率, β = −0.6713)。 -/
abbrev v3_M7a_x100 : Int := 3721

/-- M7b = 8.57 (%/yr; LCOE 5 年 CAGR 降幅)。 -/
abbrev v3_M7b_x100 : Int := 857

/-- M8a = 20.301 (%; OECD SDMX G14_B, 2025 值 OBS_STATUS = B)。 -/
abbrev v3_M8a_x1000 : Int := 20301

/-- M8b = 6.022 (pp/yr; 2024→2025 变化)。 -/
abbrev v3_M8b_x1000 : Int := 6022

/-- C1 交叉源 |GISTEMP − HadCRUT5| = 0.0656 (°C)。 -/
abbrev v3_C1_crossdiff_x1e4 : Int := 656

/-- §2 Rat 锚点的同缩放 Int 镜像 (判决一致性核对用)。 -/
abbrev c1_target_x1e4 : Int := 15000
abbrev c1_red_x1e4 : Int := 0
abbrev c1_green_M1_x1e4 : Int := 3000
abbrev c1_crossgate_x1e4 : Int := 1000
abbrev c3_gis_red_x100 : Int := 27000
abbrev c3_gis_yellow_x100 : Int := 15000
abbrev c3_ais_red_x100 : Int := 18000
abbrev c3_slr_red_x100 : Int := 100000
abbrev c4_red_x1000 : Int := 10000
abbrev c5_pb_green_int : Int := 4
abbrev c5_co2_yellow_lo_x100 : Int := 7000
abbrev c5_co2_red_x100 : Int := 8500
abbrev c7_lr_green_x100 : Int := 2000
abbrev c7_m7b_green_x100 : Int := 800
abbrev c8_m8a_yellow_lo_x1000 : Int := 15000
abbrev c8_m8a_green_x1000 : Int := 30000
abbrev c8_m8b_red_x1000 : Int := 1000

/-- C1 判决一致性 (A2-1 裕度形式): 0 < M1 = 0.0334 ≤ 0.30 → yellow
    (记录状态 yellow; v2 旧形式 −0.0334 ≤ 0 → red 被取代)。 -/
theorem v3_C1_yellow_band :
    c1_red_x1e4 < v3_M1_x1e4 ∧ v3_M1_x1e4 ≤ c1_green_M1_x1e4 := by decide

/-- C1 交叉源门槛: 0.0656 ≤ 0.10 → 无分歧 (记录 disagreement = false)。 -/
theorem v3_C1_cross_gate_pass : v3_C1_crossdiff_x1e4 ≤ c1_crossgate_x1e4 := by decide

/-- C3 判决一致性: AIS 损失 196.25 > 180 → red (AIS 分支触发)。 -/
theorem v3_C3_ais_red_rule : v3_M3b_x100 > c3_ais_red_x100 := by decide

/-- C3: GIS 损失 245.07 ≤ 270 → GIS 分支非红 (处黄带上界内)。 -/
theorem v3_C3_gis_not_red : v3_M3a_x100 ≤ c3_gis_red_x100 := by decide

/-- C3: GIS 损失 245.07 > 150 → GIS 处黄带 (150-270)。 -/
theorem v3_C3_gis_yellow_band : c3_gis_yellow_x100 < v3_M3a_x100 := by decide

/-- C3: 外推 SLR 118.82 mm < 1000 mm → SLR 分支非红。 -/
theorem v3_C3_slr_not_red : v3_slr2100_x100 < c3_slr_red_x100 := by decide

/-- C4 判决一致性: M4a = 10.521 > 10 → red (A1-5 部分可判定:
    M4a 单指标即判红, M4b 未部署不影响该分支)。 -/
theorem v3_C4_red_rule : v3_M4a_x1000 > c4_red_x1000 := by decide

/-- C5 判决一致性: M5b = 75.62 ∈ [70, 85) → yellow (M5b 分支;
    M5a = 6 ≠ 5, M5b 分支单独触发黄)。 -/
theorem v3_C5_yellow_band :
    c5_co2_yellow_lo_x100 ≤ v3_M5b_x100 ∧ v3_M5b_x100 < c5_co2_red_x100 := by decide

/-- C5: red 需 M5a ≥ 6 ∧ M5b ≥ 85; M5b = 75.62 < 85 → red 未触发。 -/
theorem v3_C5_red_not_fired : v3_M5b_x100 < c5_co2_red_x100 := by decide

/-- C5: green 需 M5a ≤ 4; M5a = 6 > 4 → green 未触发。 -/
theorem v3_C5_green_not_fired : c5_pb_green_int < v3_M5a_pb := by decide

/-- C7 判决一致性: LR = 37.21 ≥ 20 ∧ M7b = 8.57 ≥ 8 → green
    (解锁双条件均过)。 -/
theorem v3_C7_green_rule :
    c7_lr_green_x100 ≤ v3_M7a_x100 ∧ c7_m7b_green_x100 ≤ v3_M7b_x100 := by decide

/-- C8 判决一致性: M8a = 20.301 ∈ [15, 30) → yellow (M8a 分支;
    M8b = 6.022 ∉ [1,3) 不触发黄, 但 M8a 已入黄带)。 -/
theorem v3_C8_yellow_band :
    c8_m8a_yellow_lo_x1000 ≤ v3_M8a_x1000 ∧ v3_M8a_x1000 < c8_m8a_green_x1000 := by decide

/-- C8: red 需 M8a < 15 ∨ M8b < 1; M8b = 6.022 ≥ 1 → M8b 分支未触发。 -/
theorem v3_C8_m8b_not_red : v3_M8b_x1000 ≥ c8_m8b_red_x1000 := by decide

-- ============================================================
-- §5 Stouffer 辅助合成: 分离语义与记录值算术
-- ============================================================

/-! z 参与通道 (v3 快照 stouffer_auxiliary.z_excluded 逐字):
    排除 C3 (双指标通道, 无预注册单 z 折叠规则), C7 (无预注册
    z 程序), C6 (时长计数指标, 无可观测 σ), C2 (pending)。
    k 与排除清单显式报告 (预注册 §0 条款 6)。 -/

def zPressureChannels : List ECSChannel :=
  [.C1_temperature, .C4_biosphere, .C5_biogeochemical]

def zUnlockChannels : List ECSChannel :=
  [.C8_information]

/-- 合成分离 (T3-g 条款 3): 压力 z 通道全部为压力方向。 -/
theorem z_pressure_separation : (zPressureChannels.all isPressure) = true := by decide

/-- 合成分离: 解锁 z 通道全部为解锁方向。 -/
theorem z_unlock_separation : (zUnlockChannels.all (fun c => !isPressure c)) = true := by decide

/-- 合成分离: 压力/解锁 z 通道表互斥 (压力/解锁不混同)。 -/
theorem z_lists_disjoint :
    (zPressureChannels.any (fun c => zUnlockChannels.any (fun u => decide (c = u)))) = false := by
  decide

theorem z_k_pressure : zPressureChannels.length = 3 := by decide
theorem z_k_unlock : zUnlockChannels.length = 1 := by decide

/-! 记录 z 值 (×10⁴, v3 快照 stouffer_auxiliary.z_by_channel;
    z = margin/σ, 管线以未舍入中间值计算, 本模块按记录值登记, 不重算)。

    符号约定 (预注册 §2.3 压力方向统一 + A2-1): z 越大越安全。
    C1 裕度形式红界在 M 下方: z = (M−θ)/σ = +0.3288
    (v2 旧公式记录 −0.3288, 纯符号翻转, A2 §0.5 取代);
    C4/C5 红界在 M 上方: z = (θ−M)/σ (快照 sign_note);
    C8 解锁方向: z 越大 = 解锁越强。 -/

abbrev zC1_x1e4 : Int := 3288
abbrev zC4_x1e4 : Int := -669
abbrev zC5_x1e4 : Int := 74360
abbrev zC8_x1e4 : Int := 21565
abbrev Zpressure_x1e4 : Int := 44444
abbrev Zunlock_x1e4 : Int := 21565
abbrev Zgap_x1e4 : Int := -22879

/-- 压力 z 和: 0.3288 − 0.0669 + 7.436 = 7.6979 (×10⁴)。 -/
theorem v3_sum_z_pressure : zC1_x1e4 + zC4_x1e4 + zC5_x1e4 = 76979 := by decide

/-- 解锁合成 (k = 1, √1 = 1): Z_unlock = z_C8 精确成立。 -/
theorem v3_Z_unlock_identity : Zunlock_x1e4 = zC8_x1e4 := by decide

/-- Z_gap = Z_unlock − Z_pressure = 2.1565 − 4.4444 = −2.2879 (精确)。 -/
theorem v3_Z_gap_identity : Zunlock_x1e4 - Zpressure_x1e4 = Zgap_x1e4 := by decide

/-- Stouffer 平方恒等式 (规避 √3 的无理性):
    k·Z_pressure² = (Σz)² 成立至记录舍入容差。

    Z_pressure = 4.4444, k = 3, Σz = 7.6979 (×10⁴):
    |3·44444² − 76979²| = 40967 ≤ 10⁶ (×10⁻⁸ 单位 = 10⁻²)。
    容差论证: z 值记录至 4 位小数 (各 ±5×10⁻⁵), Z 记录至
    4 位小数, 传播界 ≈ 2|Σz|·3·5×10⁻⁵ + 2k|Z|·5×10⁻⁵ ≈ 3.6×10⁻³;
    注册容差 10⁻² ≈ 3× 传播界, 实际偏差 4.1×10⁻⁴。 -/
theorem v3_stouffer_pressure_squared :
    (3 * Zpressure_x1e4 * Zpressure_x1e4 - 76979 * 76979).natAbs ≤ 1000000 := by decide

/-- Z_gap 符号登记: v3 为负 (压力侧领先解锁侧) — Z_gap 是 R 的
    方向代理 (≠ R 本身), 记录值 −2.2879 (v2 −1.9082 的幅度加深
    源于 C1 z 符号统一后的再合成, 非 T 值变化)。**A3 §0.5:
    v3 的 Z_gap 记录值方向缺陷, 被 §5.5 的 v4 记录取代
    (和式形式); 本条保留供 A3-1 不变量溯源。** -/
theorem v3_Z_gap_negative : Zgap_x1e4 < 0 := by decide

-- ------------------------------------------------------------
-- §5.5 A3 修订案: v4 合成层登记 (Z_gap 和式形式)
-- ------------------------------------------------------------

/-! A3 [F] (2026-08-30, v4 管线启动前登记): Z_gap := Z_unlock +
    Z_pressure (安全方向统一约定)。根因: v1.0 §2.3 统一条款 (z 越大
    越安全, 被执行约定, A2-1 一致) 与字面减号公式 (预设危险方向)
    的内部张力 — 被执行约定下减号使 R 方向代理反向 (v2→v3 逆响应
    证据: ΔZ_gap = −ΔZ_pressure = −0.3797 精确)。

    修订范围: 仅辅助合成层; 通道 z、Z_pressure、Z_unlock、全部
    判决与状态机不变 (v4 快照与 v3 逐字节相同, 唯一变化量 =
    Z_gap)。阈值/判决/状态机变更数 = 0。

    来源: H:\cdd_ecs_channel_pipeline_results_v4.json
    #synthesis.stouffer_auxiliary (SHA256 0B655C69…1AE, 管线 v4.0,
    2026-08-30; A3-1 实现守卫断言冻结公式字符串后计算)。 -/

/-- v4 记录 Z_gap = +6.6009 (×10⁴; 和式形式 2.1565 + 4.4444)。 -/
abbrev ZgapV4_x1e4 : Int := 66009

/-- v4 Z_gap 恒等式 (A3-1 和式): Z_unlock + Z_pressure =
    2.1565 + 4.4444 = 6.6009 (精确)。 -/
theorem v4_Z_gap_sum_identity : Zunlock_x1e4 + Zpressure_x1e4 = ZgapV4_x1e4 := by decide

/-- A3-1 不变量 (重复合恒等式): Z_gap_v4 = Z_gap_v3 + 2·Z_pressure —
    同一通道 z 与同一 k 上的纯公式变更 (A3 §5 登记的不变量:
    −2.2879 + 2×4.4444 = 6.6009, 此处机械核对)。 -/
theorem a3_1_gap_recomposition : Zgap_x1e4 + 2 * Zpressure_x1e4 = ZgapV4_x1e4 := by decide

/-- A3-1 方向修正: v4 Z_gap 为正 — 解锁侧领先压力侧的安全裕度合成
    (v3 记录值 −2.2879 为方向缺陷所致, A3 §0.5 取代)。 -/
theorem a3_1_gap_positive : 0 < ZgapV4_x1e4 := by decide

/-- A3-1 逆响应消除: v4 > v3 — 压力侧安全化 (A2-1 之后 Z_pressure
    4.0647 → 4.4444) 不再使 R 代理恶化 (v2→v3 的 ΔZ_gap = −ΔZ_pressure
    逆响应缺陷已由和式形式消除)。 -/
theorem a3_1_gap_improves : Zgap_x1e4 < ZgapV4_x1e4 := by decide

/- 口径边界 (诚实登记): Z_gap (含 v4 值) 是方向代理与记录值,
    不是 σ 标准化检验统计量 — 声明层统计量 (Z_R = Z_gap/√2)、
    通道贡献上限与族级聚合属 6σ 框架 v2 预注册材料
    (H:\cdd_ecs_6sigma_framework_20260830.md §1/§3/§5),
    冻结前不进入本模块。(v2 冻结后由 T4_ClaimLadder 模块登记) -/

-- ============================================================
-- §6 A1 实现修正常数 + A2-1 符号翻转不变量 (C1 基线链)
-- ============================================================

/-! A1-1 [F]: 基线 offset 由 HadCRUT5 月距平运行时推导
    (快照 C1.offsets, ×10⁴ °C 单位)。 -/

abbrev a1_off1850_x1e4 : Int := 3565
abbrev a1_off1951_x1e4 : Int := 766
abbrev a1_pi_offset_x1e4 : Int := 2799
abbrev a1_fallback_pi_offset_x1e4 : Int := 2800

/-- A1-1 恒等式: off_1850_1900 − off_1951_1980 = pi_offset
    (0.3565 − 0.0766 = 0.2799, 精确)。 -/
theorem a1_offset_identity : a1_off1850_x1e4 - a1_off1951_x1e4 = a1_pi_offset_x1e4 := by decide

/-- A1-1 回退常数 = 测量值的 4 位小数舍入: |0.2799 − 0.28| = 10⁻⁴。 -/
theorem a1_fallback_rounding :
    (a1_pi_offset_x1e4 - a1_fallback_pi_offset_x1e4).natAbs = 1 := by decide

/-- v3 C1 中间值: T_12m vs 1951-1980 基线 = 1.1867 (°C)。 -/
abbrev v3_t12_1951_x1e4 : Int := 11867

/-- v3 C1 中间值: T_12m vs 1850-1900 基线 = 1.4666 (°C)。 -/
abbrev v3_t12_1850_x1e4 : Int := 14666

/-- C1 基线链: 1.1867 + 0.2799 = 1.4666 (GISTEMP 1951-1980 基线
    + A1-1 offset → 1850-1900 基线, 精确; 与 v2 快照逐值相同)。 -/
theorem v3_t12_chain : v3_t12_1951_x1e4 + a1_pi_offset_x1e4 = v3_t12_1850_x1e4 := by decide

/-- C1 指标链 (A2-1 裕度形式): M1 = 1.5 − 1.4666 = +0.0334
    (精确, 1.5 = c1_target 锚点)。 -/
theorem v3_M1_chain : c1_target_x1e4 - v3_t12_1850_x1e4 = v3_M1_x1e4 := by decide

/-! A2-1 符号翻转不变量: v2 与 v3 管线在**同一缓存数据、同一
    T_12m、同一 σ** 上计算; 唯一差异是指标形式的符号。旧形式
    (T_12m − 1.5) 记录 −0.0334, 新形式 (1.5 − T_12m) 记录
    +0.0334; |M1| 与 |z| 逐值相等 (被取代的 v2 记录值在此冻结
    登记, 供不变量核对)。 -/

/-- 被取代的 v2 记录 M1 (旧形式 T_12m − 1.5 = −0.0334, ×10⁴)。 -/
abbrev supersededV2_M1_x1e4 : Int := -334

/-- 被取代的 v2 记录 z_C1 (旧形式下 −0.3288, ×10⁴)。 -/
abbrev supersededV2_zC1_x1e4 : Int := -3288

/-- A2-1 不变量 (指标): M1_v2 + M1_v3 = 0 — 纯符号翻转,
    |M1| 逐值相等 (A2 §2 登记的不变量, 此处机械核对)。 -/
theorem a2_1_M1_sign_flip : supersededV2_M1_x1e4 + v3_M1_x1e4 = 0 := by decide

/-- A2-1 不变量 (z 通道): z_C1_v2 + z_C1_v3 = 0 — 同一 T_12m
    与 σ 上的纯符号翻转, |z| 不变 (幅度差仅进入 Z_pressure 的
    合成再计算, §5)。 -/
theorem a2_1_z_sign_flip : supersededV2_zC1_x1e4 + zC1_x1e4 = 0 := by decide

-- ============================================================
-- §7 溯源注册表 (SHA256 与再生命令)
-- ============================================================

/-! 快照与判据文件的 SHA256 注册表: v3 快照
    pipeline.preregistration 节登记的六个哈希 (prereg v1.0 ×2 +
    A1 ×2 + A2 ×2) + 快照文件自身哈希 (后者 2026-08-30 于文件
    冻结后计算) + 被取代的 v2 快照哈希 (A2-1 不变量溯源)。
    Lean 仅登记字符串; 哈希一致性核对在管线/审计层完成
    (同 DataProvenance §5 口径)。 -/

def preregMdSha256 : String :=
  "65C412855B37F17F35605EDB143F65F92A315B28DCA946F4EF899FB3976633D2"

def preregJsonSha256 : String :=
  "3C195E9A20CF6557164E9F91DA3C2D8E8294E5DACB81425E68D721A38F4480F0"

def a1MdSha256 : String :=
  "03F98C5176450A81CC9955A7B46241A01AADB9DC27012E9C176ACF7032528738"

def a1JsonSha256 : String :=
  "0F9D4CC4E10CE5228592E9A69AD63E1455699EF948F29E0CB50073DEEC1E420E"

def a2MdSha256 : String :=
  "BBF5811E7E229B503F680E3F50955979E88F02E3CED1340F8929B1E5544BE50D"

def a2JsonSha256 : String :=
  "92123AD1A3AAC90DE2D4DBD3B2ED2181CB59AF9EFD8F8B720C9730CF7571EDF4"

def snapshotV3Sha256 : String :=
  "5409F01F1A49ADA011503BB62BB401A6509E7349764674B42D1946FB40129026"

/-- 被取代的 v2 快照哈希 (A2 §0.5: C1 判决及下游被 v3 取代;
    文件冻结不覆盖, 保留供 A2-1 符号翻转不变量溯源)。 -/
def supersededSnapshotV2Sha256 : String :=
  "5FF712C84200270810FD62EBCA1FE609250A82BA31CF172144D9A35C48308430"

def pipelineScriptPath : String := "H:\\cdd_lean4\\scripts\\cdd_ecs_channel_pipeline_v3.py"

def snapshotV3Path : String := "H:\\cdd_ecs_channel_pipeline_results_v3.json"

def regenerationCommand : String := "python H:\\cdd_lean4\\scripts\\cdd_ecs_channel_pipeline_v3.py"

/-- 哈希格式核对: 七个注册 SHA256 均为 64 个十六进制字符长度。 -/
theorem sha256_format : preregMdSha256.length = 64 ∧ preregJsonSha256.length = 64
  ∧ a1MdSha256.length = 64 ∧ a1JsonSha256.length = 64
  ∧ a2MdSha256.length = 64 ∧ a2JsonSha256.length = 64
  ∧ snapshotV3Sha256.length = 64 := by decide

-- ============================================================
-- §8 T3 验证汇总 (项目惯例: 同 Kakeya/T1/T2 summary)
-- ============================================================

/-- T3 verification summary: 6+2 通道预注册判据锚点与 v3 快照核心结论合取。

    陈述逐项重述 §1-§7 已证定理的命题 (每项均有实质内容, 无重言式项),
    证明项逐一引用对应定理:
    G1-G4 通道计数与方向分区; G5-G12 8 通道判据带序/换算恒等式;
    G13-G18 v3 快照状态守恒与全局状态机; G19-G24 逐通道判决一致性;
    G25-G31 Stouffer 分离合成与算术; G32-G34 A1/A2 基线与指标链;
    G35 A2-1 符号翻转不变量; G36 溯源格式。 -/
theorem T3_verification_summary :
    pressureChannels.length + unlockChannels.length = 8 ∧            -- G1: 6+2=8
    (pressureChannels.all isPressure) = true ∧                       -- G2: 压力列表全压力方向
    (unlockChannels.all (fun c => !isPressure c)) = true ∧           -- G3: 解锁列表全解锁方向
    (pressureChannels.any (fun c =>
      unlockChannels.any (fun u => decide (c = u)))) = false ∧      -- G4: 压力/解锁互斥
    c1_red_M1 < c1_green_M1 ∧                                        -- G5: C1 0 < 0.30
    c2_warning_margin_Sv + c2_collapse_Sv = c2_warning_level_Sv ∧    -- G6: C2 5+10=15
    c3_gt_per_mm * mkRat 3 4 = c3_gis_red ∧                          -- G7: C3 360×3/4=270
    c4_ohc_yellow < c4_ohc_red ∧                                     -- G8: C4 5<10
    (c5_pb_green < c5_pb_yellow ∧ c5_pb_yellow < c5_pb_red) ∧        -- G9: C5 4<5<6
    c6_yellow < c6_red ∧                                             -- G10: C6 5<15
    c7_lr_red < c7_lr_green ∧                                        -- G11: C7 12<20
    c8_adoption_red < c8_adoption_green ∧                            -- G12: C8 15<30
    (countStatus pressureChannels ECSStatus.red
      + countStatus pressureChannels ECSStatus.yellow
      + countStatus pressureChannels ECSStatus.green
      + countStatus pressureChannels ECSStatus.pending_data = 6) ∧   -- G13: 压力守恒
    (countStatus unlockChannels ECSStatus.red
      + countStatus unlockChannels ECSStatus.yellow
      + countStatus unlockChannels ECSStatus.green = 2) ∧            -- G14: 解锁守恒
    countStatus (pressureChannels ++ unlockChannels)
      ECSStatus.pending_data < 3 ∧                                   -- G15: 中止规则未触发
    s2DualRed (v3Status ECSChannel.C2_amoc)
      (v3Status ECSChannel.C6_social) = false ∧                      -- G16: S2 双红未触发
    stateOf (countStatus (pressureChannels ++ unlockChannels) ECSStatus.pending_data)
      (s2DualRed (v3Status ECSChannel.C2_amoc) (v3Status ECSChannel.C6_social))
      (countStatus pressureChannels ECSStatus.red)
      (countStatus unlockChannels ECSStatus.red)
      (countStatus unlockChannels ECSStatus.yellow)
      = ECSGlobalState.CRITICAL ∧                                    -- G17: 全局状态
    stateOf 2 false 2 0 1 ≠ ECSGlobalState.TRIGGER ∧                 -- G18: 非 TRIGGER
    (c1_red_x1e4 < v3_M1_x1e4 ∧ v3_M1_x1e4 ≤ c1_green_M1_x1e4) ∧     -- G19: C1 → yellow
    v3_M3b_x100 > c3_ais_red_x100 ∧                                  -- G20: C3 AIS → red
    v3_M4a_x1000 > c4_red_x1000 ∧                                    -- G21: C4 → red
    (c5_co2_yellow_lo_x100 ≤ v3_M5b_x100
      ∧ v3_M5b_x100 < c5_co2_red_x100) ∧                             -- G22: C5 → yellow
    (c7_lr_green_x100 ≤ v3_M7a_x100
      ∧ c7_m7b_green_x100 ≤ v3_M7b_x100) ∧                           -- G23: C7 → green
    (c8_m8a_yellow_lo_x1000 ≤ v3_M8a_x1000
      ∧ v3_M8a_x1000 < c8_m8a_green_x1000) ∧                         -- G24: C8 → yellow
    (zPressureChannels.all isPressure) = true ∧                      -- G25: 压力 z 分离
    (zUnlockChannels.all (fun c => !isPressure c)) = true ∧          -- G26: 解锁 z 分离
    zPressureChannels.length = 3 ∧                                   -- G27: k_pressure=3
    zUnlockChannels.length = 1 ∧                                     -- G28: k_unlock=1
    Zunlock_x1e4 - Zpressure_x1e4 = Zgap_x1e4 ∧                      -- G29: Z_gap 恒等式
    (3 * Zpressure_x1e4 * Zpressure_x1e4
      - 76979 * 76979).natAbs ≤ 1000000 ∧                            -- G30: k·Z²≈(Σz)²
    Zgap_x1e4 < 0 ∧                                                  -- G31: Z_gap<0
    a1_off1850_x1e4 - a1_off1951_x1e4 = a1_pi_offset_x1e4 ∧         -- G32: offset 链
    v3_t12_1951_x1e4 + a1_pi_offset_x1e4 = v3_t12_1850_x1e4 ∧       -- G33: T_12m 链
    c1_target_x1e4 - v3_t12_1850_x1e4 = v3_M1_x1e4 ∧                -- G34: M1 链 (A2 形式)
    supersededV2_M1_x1e4 + v3_M1_x1e4 = 0 ∧                          -- G35: A2-1 符号翻转
    (preregMdSha256.length = 64 ∧ preregJsonSha256.length = 64
      ∧ a1MdSha256.length = 64 ∧ a1JsonSha256.length = 64
      ∧ a2MdSha256.length = 64 ∧ a2JsonSha256.length = 64
      ∧ snapshotV3Sha256.length = 64) :=                             -- G36: 哈希格式
  ⟨channel_count_consistency, pressure_list_consistent, unlock_list_consistent,
    pressure_unlock_disjoint, c1_band_order, c2_margin_level_identity,
    c3_gis_red_slr_rate, c4_ohc_band_order, c5_pb_band_order, c6_band_order,
    c7_lr_band_order, c8_adoption_band_order, v3_pressure_conservation,
    v3_unlock_conservation, v3_abort_rule_not_fired, v3_s2_dual_red_not_fired,
    v3_global_state, v3_state_not_trigger, v3_C1_yellow_band, v3_C3_ais_red_rule,
    v3_C4_red_rule, v3_C5_yellow_band, v3_C7_green_rule, v3_C8_yellow_band,
    z_pressure_separation, z_unlock_separation, z_k_pressure, z_k_unlock,
    v3_Z_gap_identity, v3_stouffer_pressure_squared, v3_Z_gap_negative,
    a1_offset_identity, v3_t12_chain, v3_M1_chain, a2_1_M1_sign_flip, sha256_format⟩

end CDD.T3.ECSChannels
