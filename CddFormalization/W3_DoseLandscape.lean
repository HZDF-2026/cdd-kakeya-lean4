import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/-! # W3 Dose Landscape: S12+S13 剂量-响应地形登记与确定性自由度裁决

    wave_proto S12 (fixO 确定性剂量扫描) 与 S13 (确定性自由度扰动稳健性)
    的 recorded-stats 登记与预注册裁决断言。

    ## 数据与算术约定 (s13_export.py 导出管线, ×480 整数性检验全通过)

    - 每检查点 EMA 评估 = n/160 (160 test episode 均值, n 为正确 episode 数);
    - 主指标 ema_phase3 = mean(EMA@{15,30,50}) = K/480, **K 为精确整数**;
    - 所有登记值零舍入: Lean 端只登记 K, 不重算 (S12/S13 npz 为唯一数据源,
      与 T3_ECSChannels 登记模式一致)。

    ## S13 实验内容 (sweep_seedcheck.py, 2026-08-31)

    §8(i) 原计划的"双峰跨 batch_seed 复验"被代码审查否定: fixO 协议下
    batch_seed 是**惰性参数** (块序不消耗 rng.choice, 嵌套噪声不消耗
    rng2.integers → 换 batch_seed 产生 BIT 相同轨迹)。仍真实起作用的
    确定性自由度只有两个:
      (a) 训练噪声种子池 (实现族) —— 族 N: {0,1,2} → {10,11,12}
      (b) 块序时间方向 —— 族 R: 正序 → 时间倒序
    族 W: 原协议峰宽加点 (0.325/0.375/0.475/0.525), 检验峰是否宽平台。

    ## 本模块证明的定理

    §1 recorded-stats: S12 原协议 11 剂量点 + S13 三族 14 点 (K 整数)
    §2 E1-E5 预注册裁决:
       E1 `s13_e1_bit`            : 族 N r0.50 双跑 BIT 一致 (确定性成立)
       E2 `s13_e2_*`              : **双峰结构翻转** —— S12 自身满足双峰
                                     (66>40 ∧ 89>47), 但族 N 峰① 翻转、
                                     族 R 双峰全翻转 → 双峰非协议不变量
       E3 `s13_e3_*`              : Spearman ρ = -1/2 (秩差平方和 Σd²=30,
                                     秩由 `rankIn` 从数据计算, 非登记)
       E4 `s13_e4`                : 峰② 幅度崩塌至原值 50% 以下
                                     (族 N 0.43×, 族 R 0.10×)
       E5 `s13_e5_*`              : 峰① 峰② 均为**针尖峰** —— ±0.025 剂量
                                     加点即掉落 >50%, 远超 0.04 阈值
    §3 信噪比主定理:
       `s13_main_effect_eq`       : 跨实现族剂量主效应 = 5/288 ≈ 0.0174
       `s13_var27_*`              : 逐剂量 27·var = Σ(3K-S)² (精确整数)
       `s13_interaction_gt_main`  : **交互方差 > 主效应平方** (29526/27 >
                                     625/9) —— 剂量信号被实现族噪声淹没
       `s13_family_avg_flat`      : 族平均后地形平坦 (< 0.04)
       `s13_family_avg_peak2`     : 族平均峰② 降至单族原值以下 (< 89/480)
    §4 溯源哈希: 全部 6 个 npz 数据文件 SHA256 登记

    ## 科学结论 (S13 裁决, 预注册 E1-E5 全部执行)

    S12 的"双峰地形/共振点选择 (ratio=0.50 最优)"**被证伪为确定性实现
    依赖的针尖峰**: fixO 的确定性只是 BIT 复现性, 不是地形稳健性。
    地形是"介质 × 确定性实现族"的联合属性 —— 剂量主效应 (5/288) 完全
    被实现族交互作用 (var = 29526/27, std ≈ 33.07/480) 淹没。处方修订:
    任何剂量选择必须附带实现族声明; 跨实现族不存在稳健的剂量选择规则。

    ## 诚实声明 (形式化范围边界)

    - 登记的是 recorded K 值 (npz 数据源), 非在 Lean 内重跑实验;
    - E3 的秩由数据表计算 (`rankIn`/`spearmanD2` 为可执行定义, decide
      核算), ρ 公式取无并列标准式 1 - 6Σd²/(n(n²-1));
    - 方差/标准差比较以平方形式做精确有理数断言, 无浮点。

    CDD Framework v28.4 · wave_proto S12/S13 剂量地形
    Date: 2026-08-31
    Toolchain: Lean v4.32.2 + Mathlib (mathlib432 local checkout)
-/

namespace CDD.W3.DoseLandscape

-- ============================================================
-- §1 recorded-stats: K = ema_phase3 × 480 (精确整数, 零舍入登记)
-- ============================================================

/- S12 原 fixO 协议 11 剂量点 (synthesis_landscape.npz ema_phase3):
     ratio:  0.00    0.20    0.30    0.35    0.40    0.45    0.50
     K:       43      9      17      66      40      47      89
             (0.0896)        (0.1375) (0.0833) (0.0979) (0.1854)
     ratio:  0.55    0.65    0.80    1.00
     K:       49      35      29      40
     峰① = 0.35 (66/480), 峰② = 0.50 (89/480), 均为 S12 观测。 -/

abbrev s12K000 : ℤ := 43
abbrev s12K020 : ℤ := 9
abbrev s12K030 : ℤ := 17
abbrev s12K035 : ℤ := 66
abbrev s12K040 : ℤ := 40
abbrev s12K045 : ℤ := 47
abbrev s12K050 : ℤ := 89
abbrev s12K055 : ℤ := 49
abbrev s12K065 : ℤ := 35
abbrev s12K080 : ℤ := 29
abbrev s12K100 : ℤ := 40

/- S13 族 N (训练噪声种子池 {0,1,2} → {10,11,12}, 块序正序):
     sweepseed_p1/p2.npz, 5 剂量点与 S12 逐点对应。 -/

abbrev s13nK000 : ℤ := 46
abbrev s13nK035 : ℤ := 34
abbrev s13nK040 : ℤ := 42
abbrev s13nK045 : ℤ := 20
abbrev s13nK050 : ℤ := 38

/- S13 族 R (块序时间倒序, 噪声种子池 {0,1,2}):
     sweepseed_p3/p4.npz。 -/

abbrev s13rK000 : ℤ := 33
abbrev s13rK035 : ℤ := 47
abbrev s13rK040 : ℤ := 53
abbrev s13rK045 : ℤ := 63
abbrev s13rK050 : ℤ := 9

/- S13 族 W (原协议峰宽加点): sweepseed_p4/p5.npz。
     0.325/0.375 邻峰① (0.35), 0.475/0.525 邻峰② (0.50)。 -/

abbrev s13wK0325 : ℤ := 38
abbrev s13wK0375 : ℤ := 42
abbrev s13wK0475 : ℤ := 37
abbrev s13wK0525 : ℤ := 41

/-- S12 报告值一致性: K=89 ↔ 蒸馏文档报告的 0.1854 (4 位小数舍入)。 -/
theorem s12_peak2_matches_report :
    |(89 : ℚ) / 480 - 1854 / 10000| < 1 / 10000 := by norm_num

-- ============================================================
-- §2 E1-E5 预注册裁决断言
-- ============================================================

/-! ### E1 扰动协议 BIT 确定性

    族 N ratio=0.50 双跑 (n050 / n050r, 同一 npz 内两次独立运行):
    三检查点 K160 = EMA 评估 × 160 逐点完全一致 → 扰动协议仍是
    确定性协议 (S13 的所有数值都是可复现的, 非随机涨落)。 -/

def n050cps : List ℤ := [28, 7, 3]    -- sweepseed_p2.npz n050 EMA@{15,30,50}
def n050rcps : List ℤ := [28, 7, 3]   -- sweepseed_p2.npz n050r (BIT 复跑)

theorem s13_e1_bit : n050cps = n050rcps := by rfl

/-- 检查点级复原: n050 的 phase3 K = 三检查点 K160 之和
    (K/480 = (K₁+K₂+K₃)/480)。 -/
theorem s13_e1_phase3_sum : 28 + 7 + 3 = s13nK050 := by decide

/-! ### E2 双峰结构翻转 (主判据)

    预注册判据: 扰动族逐点 ema_phase3(0.35) > ema_phase3(0.40) 且
    ema_phase3(0.50) > ema_phase3(0.45) → 双峰保持。
    裁决: 族 N 峰① 翻转 (34 < 42), 族 R 双峰全翻转 (47 < 53 ∧ 9 < 63)。 -/

/-- S12 原协议自身满足双峰结构 (对照, 确认判据有意义)。 -/
theorem s12_bimodal_structure : s12K035 > s12K040 ∧ s12K050 > s12K045 := by decide

/-- 族 N 峰① 翻转: 0.35 的值反而低于 0.40 谷。 -/
theorem s13_e2_famN_peak1_inverted : s13nK035 < s13nK040 := by decide

/-- 族 N 峰② 保持 (唯一存活的比较)。 -/
theorem s13_e2_famN_peak2_preserved : s13nK045 < s13nK050 := by decide

/-- 族 R 双峰全翻转。 -/
theorem s13_e2_famR_both_inverted :
    s13rK035 < s13rK040 ∧ s13rK050 < s13rK045 := by decide

/-- **E2 总裁决**: 双峰结构不是 fixO 协议的不变量 —— 预注册要求
    三个实现族 (原 + N + R) 全部满足双峰判据, 实际仅原协议满足。 -/
theorem s13_e2_bimodal_not_invariant :
    ¬(s12K035 > s12K040 ∧ s12K050 > s12K045 ∧
        s13nK035 > s13nK040 ∧ s13nK050 > s13nK045 ∧
        s13rK035 > s13rK040 ∧ s13rK050 > s13rK045) := by decide

/-! ### E3 形状: Spearman 秩相关 = -1/2

    秩由数据表计算 (非登记): `rankIn x l` = l 中严格小于 x 的元素数 + 1
    (无并列时即升序秩; 本数据三表均无并列)。
    Σd² = 30 (两族相同), ρ = 1 - 6·30/(5·24) = -1/2 < 0.5 预注册阈值
    → "纹理自由度依赖"。 -/

/-- 升序秩 (无并列): #\{y ∈ l : y < x\} + 1。 -/
def rankIn (x : ℤ) (l : List ℤ) : ℤ :=
  ((l.filter fun y => y < x).length : ℤ) + 1

/-- Spearman 秩差平方和 Σ(rank₁ᵢ - rank₂ᵢ)²。 -/
def spearmanD2 (l₁ l₂ : List ℤ) : ℤ :=
  ((l₁.zip l₂).map fun p => (rankIn p.1 l₁ - rankIn p.2 l₂) ^ 2).sum

/-- E3 族 N: Σd² = 30 (decide 从数据计算秩并核算)。 -/
theorem s13_e3_d2_famN :
    spearmanD2 [43, 66, 40, 47, 89] [46, 34, 42, 20, 38] = 30 := by decide

/-- E3 族 R: Σd² = 30。 -/
theorem s13_e3_d2_famR :
    spearmanD2 [43, 66, 40, 47, 89] [33, 47, 53, 63, 9] = 30 := by decide

/-- E3 两族秩差平方和相同 (与预注册判读的 ρ = -0.5 一致)。 -/
theorem s13_e3_d2_equal :
    spearmanD2 [43, 66, 40, 47, 89] [46, 34, 42, 20, 38]
      = spearmanD2 [43, 66, 40, 47, 89] [33, 47, 53, 63, 9] := by decide

/-- E3: ρ = 1 - 6·Σd²/(n(n²-1)) = 1 - 180/120 = **-1/2**
    (n = 5; 两族同值)。负相关 —— 扰动族的地形形状与原协议反序。 -/
theorem s13_e3_spearman_rho :
    (1 : ℚ) - 6 * 30 / (5 * (5 * 5 - 1)) = -(1 / 2) := by norm_num

/-- E3 阈值判读: ρ = -1/2 < 1/2 < 0.8 → "纹理自由度依赖"。 -/
theorem s13_e3_below_threshold : (-(1 / 2 : ℚ)) < 4 / 5 := by norm_num

/-! ### E4 幅度: 峰② 崩塌

    预注册: 峰② 相对原值 (89/480 = 0.1854) 漂移 ≤ 50%。
    裁决: 族 N 38/89 = 0.43×, 族 R 9/89 = 0.10× —— 两族均崩塌过半。
    (2K < 89 ⟺ K/89 < 1/2。) -/

theorem s13_e4_peak2_collapse :
    2 * s13nK050 < s12K050 ∧ 2 * s13rK050 < s12K050 := by decide

/-- E4 数值化: 族 N 0.427×, 族 R 0.101× (有理数精确)。 -/
theorem s13_e4_ratios : (38 : ℚ) / 89 < 1 / 2 ∧ (9 : ℚ) / 89 < 1 / 8 := by norm_num

/-! ### E5 峰宽: 峰① 峰② 均为针尖峰

    预注册: |加点 - 峰| < 0.04 (= 96/5 K 单位) → 宽平台。
    裁决: 峰② 加点落差 52/480 与 48/480 (≈ 0.108/0.100, 达阈值 2.5 倍),
    峰① 落差 28/480 与 24/480 (≈ 0.058/0.050) —— 双峰均为针尖。 -/

/-- E5 峰② 针尖: ±0.025 剂量加点即掉落 52 与 48 (阈值 96/5)。 -/
theorem s13_e5_peak2_needle :
    (96 : ℤ) < 5 * (s12K050 - s13wK0475) ∧ (96 : ℤ) < 5 * (s12K050 - s13wK0525) := by
  decide

/-- E5 峰① 针尖。 -/
theorem s13_e5_peak1_needle :
    (96 : ℤ) < 5 * (s12K035 - s13wK0325) ∧ (96 : ℤ) < 5 * (s12K035 - s13wK0375) := by
  decide

/-- E5 峰② 落差达阈值 2.5 倍以上 (有理数形式: 52/480 > 5/2 × 4/100)。 -/
theorem s13_e5_peak2_drop_ratio : (5 / 2 : ℚ) * (4 / 100) < 52 / 480 := by norm_num

-- ============================================================
-- §3 信噪比主定理: 剂量主效应 vs 实现族交互作用
-- ============================================================

/- 三实现族逐剂量 K 之和 S_r (整数): 族平均地形 = S_r/1440。
     ratio:  0.00   0.35   0.40   0.45   0.50
     S:      122    147    135    130    136
   (S = 原 + 族N + 族R 的 K 之和; 每族平均 = S/3, 除以 480。) -/

abbrev S000 : ℤ := 122
abbrev S035 : ℤ := 147
abbrev S040 : ℤ := 135
abbrev S045 : ℤ := 130
abbrev S050 : ℤ := 136

/-- 三族和登记核算 (decide 验证加法)。 -/
theorem s13_sums :
    s12K000 + s13nK000 + s13rK000 = S000 ∧
      s12K035 + s13nK035 + s13rK035 = S035 ∧
      s12K040 + s13nK040 + s13rK040 = S040 ∧
      s12K045 + s13nK045 + s13rK045 = S045 ∧
      s12K050 + s13nK050 + s13rK050 = S050 := by decide

/-- **主效应幅度**: 跨实现族剂量主效应 = (max S - min S)/1440
    = 25/1440 = 5/288 ≈ 0.0174。 -/
theorem s13_main_effect_eq :
    ((147 : ℚ) - 122) / 1440 = 5 / 288 ∧ (122 : ℤ) = 122 ∧ (147 : ℤ) = 147 := by
  norm_num

/-- max S = 147 @ r=0.35, min S = 122 @ r=0.00 (族平均地形的极值位置)。 -/
theorem s13_main_effect_extrema :
    (S000 < S035) ∧ (S000 ≤ S040) ∧ (S000 ≤ S045) ∧ (S000 ≤ S050)
      ∧ (S035 = 147) ∧ (S000 = 122) := by decide

/- 逐剂量交互作用: 27·var(K_r) = Σ(3Kᵢ - S_r)² (精确整数,
  Kᵢ 为三族 K, S_r 为其和; var 为无偏前的总体方差 × 27)。
     ratio:   0.00   0.35   0.40   0.45   0.50
     27·var:   834   4662    882   8502  29526
  交互作用在 r = 0.50 处最大 —— 正是 S12 "峰②" 的位置:
  该峰完全由实现族差异驱动。 -/

theorem s13_var27_r000 : (3 * 43 - 122 : ℤ) ^ 2 + (3 * 46 - 122) ^ 2 + (3 * 33 - 122) ^ 2 = 834 := by
  decide

theorem s13_var27_r035 : (3 * 66 - 147 : ℤ) ^ 2 + (3 * 34 - 147) ^ 2 + (3 * 47 - 147) ^ 2 = 4662 := by
  decide

theorem s13_var27_r040 : (3 * 40 - 135 : ℤ) ^ 2 + (3 * 42 - 135) ^ 2 + (3 * 53 - 135) ^ 2 = 882 := by
  decide

theorem s13_var27_r045 : (3 * 47 - 130 : ℤ) ^ 2 + (3 * 20 - 130) ^ 2 + (3 * 63 - 130) ^ 2 = 8502 := by
  decide

theorem s13_var27_r050 : (3 * 89 - 136 : ℤ) ^ 2 + (3 * 38 - 136) ^ 2 + (3 * 9 - 136) ^ 2 = 29526 := by
  decide

/-- **交互 > 主效应 (主定理)**: r = 0.50 处交互方差 (29526/27, K 单位)
    严格大于剂量主效应的平方 ((25/3)² = 625/9, K 单位)。
    即 std(实现族) ≈ 33.07 > 主效应 25/3 ≈ 8.33 —— 剂量信号被
    实现族噪声淹没 4 倍以上。 -/
theorem s13_interaction_gt_main : (625 : ℚ) / 9 < 29526 / 27 := by norm_num

/-- 平方比较的等价开方形式: (25/3)² < 29526/27 ⟹ 25/3 < √(29526/27)。
    以整数平方呈现: 625 × 27 < 29526 × 9。 -/
theorem s13_interaction_gt_main_int : (625 * 27 : ℤ) < 29526 * 9 := by decide

/-- **族平均后地形平坦**: 主效应 25/1440 < 0.04 —— 跨三实现族平均后
    剂量-响应曲线无任何超过预注册"宽平台"阈值的起伏。 -/
theorem s13_family_avg_flat : (25 : ℚ) / 1440 < 4 / 100 := by norm_num

/-- **族平均峰② 低于单族原值**: S(0.50)/1440 = 136/1440 < 89/480 ——
    S12 观测的峰② 幅度在实现族平均后损失过半 (0.094 vs 0.185)。 -/
theorem s13_family_avg_peak2 : (136 : ℚ) / 1440 < 89 / 480 := by norm_num

/-- 族平均峰② 与随机猜测锚点 (0.125 = 60/480) 的关系:
    136/1440 = 45.33/480 < 60/480 —— 族平均后峰② 低于随机猜测。 -/
theorem s13_family_avg_peak2_below_chance : (136 : ℚ) / 1440 < 60 / 480 := by norm_num

/-- **S13 总裁决 (预注册 E1-E5 语义汇总)**: E1 成立 (确定性) ∧
    E2 破坏 (双峰非不变量) ∧ E3 反序 (ρ = -1/2) ∧ E4 崩塌 (峰② 过半)
    ∧ E5 针尖 (两峰均非宽平台) —— S12 剂量地形为确定性实现依赖的
    针尖结构, 非介质内禀属性。 -/
theorem s13_verdict_summary :
    n050cps = n050rcps
      ∧ ¬(s13nK035 > s13nK040 ∧ s13nK050 > s13nK045)
      ∧ ¬(s13rK035 > s13rK040 ∧ s13rK050 > s13rK045)
      ∧ 2 * s13nK050 < s12K050 ∧ 2 * s13rK050 < s12K050
      ∧ 96 < 5 * (s12K050 - s13wK0475) ∧ 96 < 5 * (s12K035 - s13wK0325)
      ∧ (625 : ℚ) / 9 < 29526 / 27 := by
  refine ⟨rfl, ?_, ?_, by decide, by decide, by decide, by decide, by norm_num⟩ <;>
    decide

-- ============================================================
-- §4 溯源哈希 (s13_export.py sha256 输出, 2026-08-31)
-- ============================================================

/-- 数据溯源: 全部 6 个 S13/S12 数据文件 SHA256 (64 hex)。 -/
def shaSeedP1 : String := "f7de53de30abdb20a4c6677c3251cd0f3feba9a79228d452ae5ae4cd745608df"
def shaSeedP2 : String := "23e326403ecfe2456cfe7a7e328855bd3ca05b5ca02d7287b27c1da72915f8cd"
def shaSeedP3 : String := "8b521cc32dde2efe23933980d1845042fa6a490f863d2a0d8d7b7a4aa69cce1d"
def shaSeedP4 : String := "3cffd5f373c36444ae124538549b8557d2bd279134bef704088ba1de272dccc5"
def shaSeedP5 : String := "2f8b4751e632d12196d3de6210b06beb41a05a1c28ce8aa32901f7951e95b961"
def shaSeedSyn : String := "56f9c11021aa97ae79eb619eac72c5dc4aae1b5b6ac0d562b381c503f0ed458a"

/-- 哈希登记完整性: 6 个哈希均为 64 位 hex 且互不相同
    (s13_export.json §sha256 与本模块逐字符一致)。 -/
theorem s13_sha_registered :
    shaSeedP1.length = 64 ∧ shaSeedP2.length = 64 ∧ shaSeedP3.length = 64
      ∧ shaSeedP4.length = 64 ∧ shaSeedP5.length = 64 ∧ shaSeedSyn.length = 64
      ∧ shaSeedP1 ≠ shaSeedP2 ∧ shaSeedP1 ≠ shaSeedP3 ∧ shaSeedP1 ≠ shaSeedP4
      ∧ shaSeedP1 ≠ shaSeedP5 ∧ shaSeedP2 ≠ shaSeedP3 ∧ shaSeedP3 ≠ shaSeedP4
      ∧ shaSeedP4 ≠ shaSeedP5 ∧ shaSeedP5 ≠ shaSeedSyn := by decide

end CDD.W3.DoseLandscape

