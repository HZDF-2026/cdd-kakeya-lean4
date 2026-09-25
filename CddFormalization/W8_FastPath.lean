import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Module.Basic
import CddFormalization.W2_MeasureEMA

/-! # W8 FastPath: 快速通道混合线性性与 EMA-仿射交换 (S18 形式化)

    wave_proto S18 快速通道 (s18_fastpath.py train_s18) 核心数学性质的
    Lean 4 形式化。物理设置 (design_efficiency_20260901.txt §2, 预注册
    v1 + v1a, 执行前冻结):

      双时间尺度介质系统 (统一物理因果, 非模块拼装):
        慢系统   phic fixO 梯度流 (与 S12-S17 逐位同构)
        快系统   冻结痕迹 φ_hip (非梯度存储, P2 制度化)
        快速通道 phic_eff,t = (1−g_t)·phic_t + g_t·φ_hip
                 (log 空间仿射混合); α_eff = exp(c2f(phic_eff))
        门控     g_t = g*·𝟙[t > trans_v3] (步进, 检测器 v3 驱动)

    ## 本模块证明的定理 (全部 Mathlib 支撑, 零 sorry)

    T-H EMA-仿射交换 (预注册 §9):
    1.  `emaRec_affine`     : EMA 与仿射映射可交换 (常数 g 基础)
    2.  `emaRec_eff_const`  : 常数 g 分解 = (1−g)·EMA(x) + g·(1−β^t)·ψ
    3.  `emaRec_eff_prefix` : t ≤ τ ⇒ EMA_eff ≡ 冷 EMA (R5 前缀不变量)
    4.  `emaRec_eff_decomp` : 步进 g 精确分解定理 (主定理):
         EMA_eff(τ+n) = (1−g*)·EMA(x;τ+n) + g*·(β^n·EMA(x;τ) + (1−β^n)·ψ)
    5.  `trace_weight_mono` : 痕迹权重 g*·(1−β^n) 单调不减
    6.  `trace_weight_le`   : 痕迹权重上界 g*
    7.  `emaBC_trace_coeff_ge`    : 冻结痕迹读出权重 ≥ g*·(1−β^n)
    8.  `emaBC_warmstart_coeff_le`: 单步注入读出权重 ≤ β^{t−1−s₀}
                                (7 ∧ 8 = E1 修复的数学分野)

    T-G 混合线性性 (几何加权介质, 预注册 §2.4):
    9.  `c2f_mix_comm`       : 仿射混合与线性插值交换
    10. `band_support_preserved`: 带外谱支撑在仿射混合下保持
    11. `log_alpha_eff_affine`  : log α_eff = (1−g)·log α_slow + g·log α_hip
    12. `alpha_eff_geometric`   : α_eff = α_slow^(1−g)·α_hip^g (几何加权介质)

    §4 recorded-stats (S18 裁决登记, s18_merge.json 唯一数据源,
       2026-09-03 16:26 merge, 量化值 ℚ 精确):
    13. `s18_f1_non_geometric`  : F1 非几何归因 (L2 边际 −2/160 违例)
    14. `s18_f2a_refuted`       : F2a 通道救援否证 (L2 gain −5/160)
    15. `s18_f2b_spectral`      : F2b 频谱内容通道 (3/3 池边际 < 1/160)
    16. `s18_f3_refuted`        : F3 E1 修复否证 (fL0 30/160 < 35/160)
    17. `s18_f4_fail`           : F4 split-half 败 (L2 双半 < 3/80)
    18. `s18_t1_negative`       : T1 负结果 (f2L0 9/160 < 12/160)
    19. `s18_gstar_nonmonotonic`/`s18_trace_quality_q3`: 次级登记
    20. `s18_verdict_summary`   : 总裁决组合 (M5 否证)

    ## 与代码的对应 (s18_fastpath.py train_s18, 逐条)

      gateStep τ g* s       ← g = g_star if (crossed and trace is not None) else 0.0
                               (1-indexed 步 s; crossed 自 s = τ+1 起为真)
      effField              ← phic_eff = (1.0 - g) * phic + g * trace
      emaRec_eff_prefix     ← "检测器运行于 α_eff 的 ρ, 跃迁前与冷 ρ 逐位
                               一致" (R5 附加前缀不变量的数学内容)
      emaRec_eff_decomp     ← phic_eff_ema 递推的闭式解
      trace_weight_mono     ← "痕迹冻结 ⇒ 痕迹在 EMA_eff 中权重不减" (§2.6)
      alpha_eff_geometric   ← "c2f 线性 ⇒ log α_eff 几何加权" (§2.4)

    ## 诚实声明 (形式化范围边界)

    - 本模块形式化的是**混合与 EMA 的代数性质**, 非对 Python 数值代码
      的等价性验证;
    - c2f 的具体实现 (FFT 零填充分块上采样, adjoint.py:19) 以抽象线性
      映射 L 登记: 线性性为其注册数学性质; 带限谱支撑 (support ⊆ 粗网格
      频带) 的数值面由 wave_proto 端 Python 校准 (band_support_preserved
      只登记"线性 + 双方带限 ⇒ 混合带限"的传递性);
    - T-H 定理为标量形式: EMA 递推逐元素无交叉耦合, per-point 形式化
      即覆盖 16×16 全场 (W2 惯例);
    - 检测器 v3 (双条件阈值触发) 的标定不在本模块 —— 其由
      s18_calib_check.py 在注册轨迹上复算, 不属于混合代数;
    - R2-R6/F1-F4/T1 门断言 (recorded-stats) 从 s18_merge.json 登记
      (Lean 只登记不重算, §4); 裁决值为协议量化值 (k/160, k/80) ⇒ ℚ
      精确登记, 无舍入条款; R 系逐位一致性为 numpy 侧裁决 (max|Δ|=0),
      Lean 只登记结论; 溯源 SHA256 见 JSON meta 段。

    CDD Framework v28.4 · wave_proto S18 快速通道
    Date: 2026-09-03
    Toolchain: Lean v4.32.2 + Mathlib (mathlib432 local checkout)
-/

namespace CDD.W8.FastPath

open CDD.W2.MeasureEMA

-- ============================================================
-- §1 门控与有效场 (s18_fastpath.py train_s18 逐字对应)
-- ============================================================

/-- 步进门控: g_s = 0 (s ≤ τ), g* (s > τ)。
    τ = trans_v3 (检测器 v3 跃迁 iter, 1-indexed); 跃迁 iter 本身以
    g=0 运行, 混合自 τ+1 起 (预注册 §2.5)。 -/
def gateStep (τ : ℕ) (gstar : ℝ) (s : ℕ) : ℝ :=
  if s ≤ τ then 0 else gstar

/-- 有效场: log 空间仿射混合 φ_eff,s = (1−g_s)·x_s + g_s·ψ。
    x = phic (慢系统轨迹), ψ = φ_hip (冻结痕迹, 与 s 无关)。 -/
def effField (τ : ℕ) (gstar : ℝ) (x : ℕ → ℝ) (ψ : ℝ) (s : ℕ) : ℝ :=
  (1 - gateStep τ gstar s) * x s + gateStep τ gstar s * ψ

-- ============================================================
-- §2 T-H EMA-仿射交换 (预注册 §9)
-- ============================================================

/-- **T-H1 (EMA-仿射交换)**: EMA 递推与仿射映射可交换 —— 对常数门控 g,
    混合场的 EMA 等于各分量 EMA 的同一仿射组合。
    这是"常数 g 下 EMA 与仿射映射可交换"的逐字形式化。 -/
theorem emaRec_affine (β g : ℝ) (x : ℕ → ℝ) (ψ : ℝ) (t : ℕ) :
    emaRec β (fun s => (1 - g) * x s + g * ψ) t
      = (1 - g) * emaRec β x t + g * emaRec β (fun _ => ψ) t := by
  induction t with
  | zero => simp [emaRec]
  | succ t ih =>
      simp only [emaRec]
      rw [ih]
      ring

/-- **T-H2 (常数 g 分解)**: 常数门控下混合场 EMA 分解为慢系统 EMA 的
    (1−g) 倍加冻结痕迹的 g·(1−β^t) 倍 —— 痕迹以完整未衰减因子
    (1−β^t) 常驻 (W2 `emaRec_const` 的通道版)。 -/
theorem emaRec_eff_const (β g : ℝ) (x : ℕ → ℝ) (ψ : ℝ) (t : ℕ) :
    emaRec β (fun s => (1 - g) * x s + g * ψ) t
      = (1 - g) * emaRec β x t + g * (1 - β ^ t) * ψ := by
  rw [emaRec_affine, emaRec_const]
  ring

/-- **T-H3 (前缀不变量)**: 跃迁前 (t ≤ τ) 有效场 EMA 与冷 EMA 逐点相等
    —— 门控未开 ⇒ 混合恒等 ⇒ EMA 轨迹不变。
    这是 R5 附加前缀不变量 ("rho[:trans] 与冷 rho 前缀逐位一致")
    的数学内容。 -/
theorem emaRec_eff_prefix (β gstar : ℝ) (x : ℕ → ℝ) (ψ : ℝ) (τ : ℕ) :
    ∀ t ≤ τ, emaRec β (effField τ gstar x ψ) t = emaRec β x t := by
  intro t
  induction t with
  | zero => intro _; simp [emaRec]
  | succ t ih =>
      intro ht
      have hg : effField τ gstar x ψ (t + 1) = x (t + 1) := by
        simp only [effField, gateStep, if_pos ht]
        ring
      simp only [emaRec, hg]
      rw [ih (by omega)]

/-- **T-H4 (步进 g 精确分解, 主定理)**: 跃迁 τ 之后第 n 步, 混合场 EMA
    闭式分解为三项 —— 慢系统 EMA 的 (1−g*) 倍 + 跃迁时刻 EMA 状态的
    g*·β^n 倍 (几何衰减记忆) + 冻结痕迹的 g*·(1−β^n) 倍 (单调驻留)。

    物理读法: 痕迹不进入慢系统梯度 (P2), 其在读出 EMA 中的系数只由
    门控开后的几何权重累积决定, 与慢系统后续动力学完全解耦。 -/
theorem emaRec_eff_decomp (β gstar : ℝ) (x : ℕ → ℝ) (ψ : ℝ) (τ : ℕ) (n : ℕ) :
    emaRec β (effField τ gstar x ψ) (τ + n)
      = (1 - gstar) * emaRec β x (τ + n)
        + gstar * (β ^ n * emaRec β x τ + (1 - β ^ n) * ψ) := by
  induction n with
  | zero =>
      rw [Nat.add_zero, pow_zero,
          emaRec_eff_prefix β gstar x ψ τ τ (Nat.le_refl τ)]
      ring
  | succ n ih =>
      have hassoc : τ + (n + 1) = τ + n + 1 := by omega
      rw [hassoc]
      have hg : effField τ gstar x ψ (τ + n + 1)
          = (1 - gstar) * x (τ + n + 1) + gstar * ψ := by
        have h : ¬(τ + n + 1 ≤ τ) := by omega
        simp only [effField, gateStep, if_neg h]
      simp only [emaRec, hg]
      rw [ih, pow_succ]
      ring

/-- **T-H5 (痕迹权重单调不减)**: β ∈ [0,1], g* ≥ 0 时, 痕迹系数
    g*·(1−β^n) 随 n 单调不减 —— "痕迹冻结 ⇒ EMA_eff 中痕迹权重不减"
    (预注册 §2.6, E1 修复的机制载体) 的逐字形式化。 -/
theorem trace_weight_mono (β gstar : ℝ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hg : 0 ≤ gstar) (n : ℕ) :
    gstar * (1 - β ^ n) ≤ gstar * (1 - β ^ (n + 1)) := by
  have h : β ^ (n + 1) ≤ β ^ n :=
    calc β ^ (n + 1) = β ^ n * β := pow_succ β n
      _ ≤ β ^ n * 1 := mul_le_mul_of_nonneg_left hβ1 (pow_nonneg hβ n)
      _ = β ^ n := mul_one _
  have h3 : 0 ≤ gstar * (β ^ n - β ^ (n + 1)) :=
    mul_nonneg hg (sub_nonneg.mpr h)
  have heq : gstar * (1 - β ^ (n + 1)) - gstar * (1 - β ^ n)
      = gstar * (β ^ n - β ^ (n + 1)) := by ring
  linarith

/-- **T-H6 (痕迹权重上界)**: 痕迹系数不超过 g* —— 权重从 0 单调逼近
    但永不超过门控耦合系数 (β ∈ [0,1] 的推论)。 -/
theorem trace_weight_le (β gstar : ℝ) (hβ : 0 ≤ β) (hg : 0 ≤ gstar)
    (n : ℕ) : gstar * (1 - β ^ n) ≤ gstar := by
  have h : 0 ≤ β ^ n := pow_nonneg hβ n
  have h2 : gstar * (1 - β ^ n) ≤ gstar * 1 :=
    mul_le_mul_of_nonneg_left (by linarith) hg
  linarith

/-- **T-H7 (冻结痕迹读出权重下界)**: 偏差修正 EMA (emaBC) 中冻结痕迹的
    系数 g*·(1−β^n)/(1−β^t) ≥ g*·(1−β^n) —— 分母 ≤ 1 只会放大权重。
    注册协议数值 (β=0.9, g*=0.5, τ=15, t=50, n=35): 权重 ≥
    0.5·(1−0.9^35) ≈ 0.487, 即痕迹以近满额 g* 常驻读出。 -/
theorem emaBC_trace_coeff_ge (β gstar : ℝ) (hβ : 0 ≤ β) (hβ1 : β < 1)
    (hg : 0 ≤ gstar) {τ t : ℕ} (hτ : τ < t) :
    gstar * (1 - β ^ (t - τ))
      ≤ gstar * (1 - β ^ (t - τ)) / (1 - β ^ t) := by
  have ht : 1 ≤ t := by omega
  have hβt : 0 < 1 - β ^ t := one_sub_pow_pos β hβ hβ1 ht
  have hβn : β ^ (t - τ) ≤ 1 := pow_le_one₀ hβ hβ1.le
  have hnum : 0 ≤ gstar * (1 - β ^ (t - τ)) :=
    mul_nonneg hg (sub_nonneg.mpr hβn)
  rw [le_div_iff₀ hβt]
  have hβtnn : 0 ≤ β ^ t := pow_nonneg hβ t
  have key : gstar * (1 - β ^ (t - τ)) * (1 - β ^ t)
      ≤ gstar * (1 - β ^ (t - τ)) * 1 :=
    mul_le_mul_of_nonneg_left (by linarith) hnum
  nlinarith [key]

/-- **T-H8 (单步注入读出权重上界, E1 对照)**: emaBC 中任一单步 s₀ 的
    系数 (1−β)·β^{t−1−s₀}/(1−β^t) ≤ β^{t−1−s₀} —— 几何衰减。
    热启动 φ₀ 模式 (E1 失败: 痕迹仅经初始条件一次性注入) 的读出权重
    属此类; 注册协议数值 (β=0.9, s₀=0, t=50): ≤ 0.9^49 ≈ 0.0057。
    与 T-H7 对照: 0.487 vs 0.0057 —— 两个数量级, E1 修复与 E1 冲刷
    的数学分野。 -/
theorem emaBC_warmstart_coeff_le (β : ℝ) (hβ : 0 ≤ β) (hβ1 : β < 1)
    {t s₀ : ℕ} (hs₀ : s₀ < t) :
    (1 - β) * β ^ (t - 1 - s₀) / (1 - β ^ t) ≤ β ^ (t - 1 - s₀) := by
  have ht : 1 ≤ t := by omega
  have hβt : 0 < 1 - β ^ t := one_sub_pow_pos β hβ hβ1 ht
  have hβtle : β ^ t ≤ β := by
    have := pow_le_pow_of_le_one hβ hβ1.le ht
    simpa using this
  have hc : 0 ≤ β ^ (t - 1 - s₀) := pow_nonneg hβ _
  rw [div_le_iff₀ hβt]
  have hprod : β ^ (t - 1 - s₀) * β ^ t ≤ β ^ (t - 1 - s₀) * β :=
    mul_le_mul_of_nonneg_left hβtle hc
  nlinarith [hprod]

-- ============================================================
-- §3 T-G 混合线性性 (几何加权介质, 预注册 §2.4)
-- ============================================================

variable {ι ι' κ : Type*}

/-- **T-G1 (混合-插值交换)**: 线性插值 c2f (FFT 零填充分块上采样,
    adjoint.py:19, 以线性映射 L 登记) 与仿射混合交换 —— 粗网格上的
    log 空间仿射混合提升为细网格上的同一仿射混合。 -/
theorem c2f_mix_comm (L : (ι → ℝ) →ₗ[ℝ] (ι' → ℝ)) (g : ℝ) (φ ψ : ι → ℝ) :
    L ((1 - g) • φ + g • ψ) = (1 - g) • L φ + g • L ψ := by
  rw [map_add, map_smul, map_smul]

/-- **T-G2 (带限支撑保持)**: 谱变换 F 下, 若慢场与痕迹场的细网格像都
    在带外频率集 S 上消没, 则仿射混合的像也在 S 上消没 —— 带限谱支撑
    经快速通道保持 (线性性 ⇒ 消没集传递)。
    S = 带外频率集; F(c2f) 的具体 FFT 数值面由 wave_proto 校准。 -/
theorem band_support_preserved (L : (ι → ℝ) →ₗ[ℝ] (ι' → ℝ))
    (F : (ι' → ℝ) →ₗ[ℝ] (κ → ℝ)) (g : ℝ) (φ ψ : ι → ℝ) (S : Set κ)
    (hφ : ∀ k ∈ S, F (L φ) k = 0) (hψ : ∀ k ∈ S, F (L ψ) k = 0) :
    ∀ k ∈ S, F (L ((1 - g) • φ + g • ψ)) k = 0 := by
  intro k hk
  rw [c2f_mix_comm, map_add, map_smul, map_smul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hφ k hk, hψ k hk]
  ring

/-- **T-G3 (log α_eff 仿射分解)**: 有效介质对数的仿射分解
    log α_eff = (1−g)·log α_slow + g·log α_hip (预注册 §2.4 的逐字
    形式化; exp-log 恒等 + T-G1)。 -/
theorem log_alpha_eff_affine (L : (ι → ℝ) →ₗ[ℝ] (ι' → ℝ)) (g : ℝ)
    (φ ψ : ι → ℝ) (p : ι') :
    Real.log (Real.exp (L ((1 - g) • φ + g • ψ) p))
      = (1 - g) * Real.log (Real.exp (L φ p))
        + g * Real.log (Real.exp (L ψ p)) := by
  rw [Real.log_exp, Real.log_exp, Real.log_exp, c2f_mix_comm]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- **T-G4 (几何加权介质)**: log 空间仿射混合的指数像 = 幂几何加权
    α_eff = α_slow^(1−g) · α_hip^g —— "几何加权介质" 的数学登记
    (c2f 线性 ⇒ log α_eff 几何加权, 预注册 §2.4)。 -/
theorem alpha_eff_geometric (L : (ι → ℝ) →ₗ[ℝ] (ι' → ℝ)) (g : ℝ)
    (φ ψ : ι → ℝ) (p : ι') :
    Real.exp (L ((1 - g) • φ + g • ψ) p)
      = (Real.exp (L φ p)) ^ (1 - g) * (Real.exp (L ψ p)) ^ g := by
  rw [c2f_mix_comm]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
  congr 1
  ring

-- ============================================================
-- §4 R2-R6 / F1-F4 / T1 门断言 (recorded-stats)
-- ============================================================

/- S18 裁决记录 (s18_merge.py 于阶段 B (p4-p7, 15:50-15:54) 完成后执行,
   2026-09-03 16:26; s18_merge.json 为唯一数据源, 全部源 npz 与预注册
   文本 SHA256 溯源见其 meta 段; Lean 只登记不重算, 沿 W2 §6 /
   DataProvenance 口径):

     R 系构造门 6/6 PASS (实现无缺陷 ⇒ F/T 裁决为正式 formal):
       R1-R4 逐位一致 max|Δ| = 0 (z/cLk/xhLk/rep0 ↔ 注册轨迹);
              rep0_phicema 再评估精确复现 36/160 (逐 episode 亦 0)。
       R5     18 pathway 臂 (fwL0 除外, v1a) trans_v3 与冷跃迁一致
              {L0:15, L1:8, L2:8, L3:10, τ2/L0:8}, ρ 前缀 max|Δ| = 0。
       R6     q 族 init_std = φ* std (0.088938);
              fr/rf2 族 trace_std = φ_hip std (0.086488)。

     F/T 裁决 (读出协议量化 1/160, split-half 1/80 ⇒ ℚ 精确登记;
     float64 均值计算以 merge TOL = 1e-12 护栏, 见 s18_merge.py):
       F1  池救援归因  Δ = (L1:+8, L2:−2, L3:+10)/160
           → 非几何归因 (L2 的 q_max 26/160 反超 xhL2 24/160;
              S17 悬案: 池救援为频谱/涨落, 非 φ* 几何内容)
       F2a 通道救援    gain = (L1:+6, L2:−5, L3:+23)/160
           → REFUTED (架构主张否证: 主声明 8/160 线 L1/L2 未达,
              降级 5/160 线 L2 违例 —— 通道救援非池通用, L2 有害)
       F2b 通道内容    margin = (L1:−9, L2:−12, L3:−4)/160
           → 频谱内容通道 (3/3 池真痕迹弱于 max 随机相位痕迹)
       F3  E1 修复     fL0 = 30/160, fr_max_L0 = 17/160, 门槛 35/160
           → REFUTED (F3a 败 ∧ F3b 过: 差冷基线 6/160 > 容差 1/160)
       F4  split-half  (L1:(+3,+3), L2:(−3,−2), L3:(+10,+13))/80
           → FAIL (L2 双半违例, 与 F2a 同向)
       T1  τ2 迁移     f2L0 = 9/160, 门槛 12/160, 内容边际 −19/160
           → 负结果登记 (τ2 前导单点, 不触发架构否证) -/

/-- **F1 裁决推导 (recorded)**: 每池归因边际
    Δ_k = EMA@50(xhLk) − max_i EMA@50(q_iLk) (单位 1/160):
    L1 = +8, L2 = −2, L3 = +10。几何归因门要求 3/3 池 Δ ≥ 1;
    L2 违例 (q_max 26/160 反超 xhL2 24/160) ⇒ 非几何归因 ——
    S17 池救援悬案裁决: 频谱/涨落所致, 非 φ* 几何内容。 -/
theorem s18_f1_non_geometric :
    ¬ ((8 : ℚ) / 160 ≥ 1 / 160
        ∧ (-2 : ℚ) / 160 ≥ 1 / 160
        ∧ (10 : ℚ) / 160 ≥ 1 / 160) := by
  norm_num

/-- **F2a 裁决推导 (recorded, 架构主门)**: 每池通道增益
    gain_k = EMA_eff@50(fLk) − EMA@50(cLk) (单位 1/160):
    L1 = +6, L2 = −5, L3 = +23。主声明需 3/3 池 ≥ 8; 降级需
    3/3 池 ≥ 5。L1 < 8 (主声明败) ∧ L2 < 5 (降级败) ⇒ REFUTED:
    快速通道救援主张否证 (L2 池上通道有害)。 -/
theorem s18_f2a_refuted :
    ((6 : ℚ) / 160 < 8 / 160)
      ∧ ¬ ((6 : ℚ) / 160 ≥ 5 / 160
            ∧ (-5 : ℚ) / 160 ≥ 5 / 160
            ∧ (23 : ℚ) / 160 ≥ 5 / 160) := by
  norm_num

/-- **F2b 裁决推导 (recorded)**: 真痕迹相对随机相位痕迹的内容边际
    (单位 1/160): L1 = −9, L2 = −12, L3 = −4。几何内容门要求
    3/3 池 ≥ 1; 三池全部 < 1 ⇒ 频谱内容通道 —— 通道效应主要由
    痕迹频谱统计驱动, 非几何任务内容 (降级标签, 架构声明附限定)。 -/
theorem s18_f2b_spectral :
    ((-9 : ℚ) / 160 < 1 / 160)
      ∧ ((-12 : ℚ) / 160 < 1 / 160)
      ∧ ((-4 : ℚ) / 160 < 1 / 160) := by
  norm_num

/-- **F3 裁决推导 (recorded, E1 修复)**: fL0 = 30/160 < 门槛
    35/160 (= 冷 36/160 − 1/160 容差) 即 F3a 败; 同时
    max fr_iL0 = 17/160 < 35/160 即 F3b 过 (未达线非随机注入
    可比) ⇒ F3 否证: 通道在同任务 (τ1/L0) 上不足以无腐蚀恢复
    E1 损失 (差冷基线 6/160 > 容差 1/160)。 -/
theorem s18_f3_refuted :
    ((30 : ℚ) / 160 < 35 / 160) ∧ ((17 : ℚ) / 160 < 35 / 160) := by
  norm_num

/-- **F4 裁决推导 (recorded, split-half)**: 每池每半增益
    (单位 1/80): L1 = (+3, +3), L2 = (−3, −2), L3 = (+10, +13)。
    门要求 3/3 池 × 2 半全部 ≥ 3; L2 双半违例 ⇒ FAIL
    (与 F2a 同向, L2 为一致有害池)。 -/
theorem s18_f4_fail :
    ¬ ((3 : ℚ) / 80 ≥ 3 / 80 ∧ (3 : ℚ) / 80 ≥ 3 / 80
        ∧ (-3 : ℚ) / 80 ≥ 3 / 80 ∧ (-2 : ℚ) / 80 ≥ 3 / 80
        ∧ (10 : ℚ) / 80 ≥ 3 / 80 ∧ (13 : ℚ) / 80 ≥ 3 / 80) := by
  norm_num

/-- **T1 裁决推导 (recorded, τ2 迁移)**: f2L0 = 9/160 < 门槛
    12/160 (= z2 基线 10/160 + 2/160), 且内容边际
    9 − 28 = −19 (单位 1/160, rf2bL0 = 28/160 反超) < 1/160
    ⇒ 负结果登记: 海马痕迹通道不迁移到前导单点 τ2
    (预注册: 不触发架构否证)。 -/
theorem s18_t1_negative :
    ((9 : ℚ) / 160 < 12 / 160)
      ∧ ((9 - 28 : ℚ) / 160 < 1 / 160) := by
  norm_num

/-- **次级登记: g* 敏感性非单调** (fL0 族, EMA@50, 单位 1/160):
    g = 0.25 → 17, g = 0.50 → 30, g = 0.75 → 23 —— g* = 0.5 为
    局部最优, 门控强度非单调增强 (存在内部工作点)。 -/
theorem s18_gstar_nonmonotonic :
    ((17 : ℚ) / 160 < 30 / 160) ∧ ((23 : ℚ) / 160 < 30 / 160) := by
  norm_num

/-- **次级登记: Q3 痕迹质量** (fL0 族, 单位 1/160): EMA 固化痕迹
    (fL0) = 30 优于原始 φ* 痕迹 (fL0raw) = 24, 差 ≥ 1 ——
    海马式 EMA 收割提升痕迹读出质量 (P2 制度化痕迹的意义)。 -/
theorem s18_trace_quality_q3 :
    ((24 : ℚ) / 160 < 30 / 160) ∧ ((30 - 24 : ℚ) / 160 ≥ 1 / 160) := by
  norm_num

/-- **S18 总裁决 (recorded, 0831 §11 M5 输入)**: 构造门 6/6 全过
    (R1-R6, 数据可信) 之下, F2a 通道救援否证 ∧ F3 E1 修复否证 ∧
    F1 非几何归因 ∧ F2b 频谱内容通道 ∧ F4 split-half 败 ∧ T1 负
    结果 —— 预注册的"介质级混合 + 步进门控"快速通道救援主张在
    本实验族下不成立; S17 池救援悬案归因为非几何 (频谱/涨落)。 -/
theorem s18_verdict_summary :
    (¬ ((8 : ℚ) / 160 ≥ 1 / 160
          ∧ (-2 : ℚ) / 160 ≥ 1 / 160
          ∧ (10 : ℚ) / 160 ≥ 1 / 160))
      ∧ ((6 : ℚ) / 160 < 8 / 160
          ∧ ¬ ((6 : ℚ) / 160 ≥ 5 / 160
                ∧ (-5 : ℚ) / 160 ≥ 5 / 160
                ∧ (23 : ℚ) / 160 ≥ 5 / 160))
      ∧ ((-9 : ℚ) / 160 < 1 / 160
          ∧ (-12 : ℚ) / 160 < 1 / 160
          ∧ (-4 : ℚ) / 160 < 1 / 160)
      ∧ ((30 : ℚ) / 160 < 35 / 160 ∧ (17 : ℚ) / 160 < 35 / 160)
      ∧ (¬ ((3 : ℚ) / 80 ≥ 3 / 80 ∧ (3 : ℚ) / 80 ≥ 3 / 80
            ∧ (-3 : ℚ) / 80 ≥ 3 / 80 ∧ (-2 : ℚ) / 80 ≥ 3 / 80
            ∧ (10 : ℚ) / 80 ≥ 3 / 80 ∧ (13 : ℚ) / 80 ≥ 3 / 80))
      ∧ ((9 : ℚ) / 160 < 12 / 160
          ∧ (9 - 28 : ℚ) / 160 < 1 / 160) :=
  ⟨s18_f1_non_geometric, s18_f2a_refuted, s18_f2b_spectral,
    s18_f3_refuted, s18_f4_fail, s18_t1_negative⟩

end CDD.W8.FastPath
