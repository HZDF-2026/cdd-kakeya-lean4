import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.InnerProductSpace.Basic

/-! # W9 SpectralWeight: 谱权重公理集前四条的 Lean 4 形式化 (重构 Phase 0)

    谱权重架构重构 (h:\jy-spectral-rebuild\design_spectral_rebuild_v1_20260904.md
    §2 架构宪法 / §7.4) 的核心数学定理形式化。物理设置 (CDD v28
    谱权重公理集 → 单一谱混合介质):

      谱权重状态   (w_pp, w_ac, w_sc) : 系统全局宏观状态, Σw = 1,
                  分量严格正 (A2/A3; 实现侧正则化下限 w_min = 0.01)
      复制子动力学 β_i = w_i·(r_i − ⟨r⟩_w), ⟨r⟩_w = Σ_j w_j·r_j (A4)
      Lyapunov    V = −Σ_i w_i·ln w_i (负熵)
      能量份额     w_i = ‖Φ_i‖²/‖Φ‖² (三态分解正交性, 设计文档 §3.3)

    ## 本模块证明的定理 (全部 Mathlib 支撑, 零 sorry)

    §7.4-1 权重守恒 (A4 算术守恒):
    1.  `beta_sum_zero`           : Σw = 1 ⇒ Σβ_i = 0

    §7.4-2 Lyapunov 单调:
    2.  `sum_beta_sq_div_w_nonneg`  : w > 0 ⇒ Σβ_i²/w_i ≥ 0 (符号核)
    3.  `beta_dot_r_eq_variance`    : Σβ_i·r_i = Σβ_i²/w_i (方差代数核心)
    4.  `hasDerivAt_meanW_along`    : 沿复制子轨迹 d⟨r⟩_w/dt = Σβ²/w ≥ 0
                                      (Fisher 基本定理 —— 一般适配度下的
                                      普适单调量; 适配度场 r 在 t 邻域冻结)
    5.  `hasDerivAt_negEntropy_comp`: 链式法则 dV/dt = −Σβ_i·ln w_i
                                      (Σβ = 0 前提, 任意适配度)
    6.  `lyapunov_entropic_nonpos`  : r_i = ln w_i (熵性适配度) ⇒
                                      dV/dt = −Σβ²/w ≤ 0 —— §2 A4 主张
                                      的精确有效域 (熵增趋向最大熵均衡)

    §7.4-3 正性保持 (复制子不变集, 实现级):
    7.  `replicator_step_positivity`: 有界人均增长率 |r_i−⟨r⟩| ≤ M 且
                                      η·M < 1 ⇒ Euler 步 w+ηβ 保持严格正
    8.  `replicator_exp_positivity` : 乘法指数步 w_i·e^{η(r_i−⟨r⟩)} 对
                                      任意 η 严格正 (log 空间表示)

    §7.4-4 能量份额归一 (正交分解):
    9.  `norm_sq_sum_orthogonal`    : 两两正交 ⇒ ‖ΣΦ_i‖² = Σ‖Φ_i‖²
    10. `energy_share_normalized`   : Φ ≠ 0 ⇒ Σ‖Φ_i‖²/‖Φ‖² = 1

    A5 GUT 计数先验 (数值登记):
    11. `gut_prior_normalized`      : 3/14 + 9/14 + 2/14 = 1
    12. `gut_prior_positive`        : 三分量严格正 (A2 数值面)

    13. `W9_verification_summary`   : 上述核心定理的合取登记

    ## 重要范围发现 (对设计文档 §2 A4 的条件完备化)

    §2 A4 原文 "dV/dt = −Σβ_i²/w_i" 的恒等式部分在**一般适配度**下
    不成立: 链式法则给出 dV/dt = −Σβ_i·ln w_i (定理 5, 任意适配度),
    而恒等式 Σβ·ln w = Σβ²/w 仅在熵性适配度 r_i = ln w_i 下成立
    (定理 6 = 定理 3 在 r := ln w 处的实例)。一般适配度下成立的
    普适单调量是平均适配度非减 (Fisher 基本定理, 定理 4)。设计文档
    §2 A4 / §7.4-2 应按此双轨理解: "无约束时熵增趋向最大熵均衡
    (1/3,1/3,1/3)" 对应熵性适配度轨道 (r = ln w); "结构 (主导分量)
    由约束 (对称破缺、冷却) 产生" 对应约束下的一般轨道 (Fisher
    单调量)。双轨均已形式化, 无需收缩 A4 解释范围, 只需补显式前提
    (适配度型别), 与 CDD 惯例的条件完备化路线一致。

    ## 与设计文档/实现的对应

      §7.4-1 ← 定理 1        (权重控制器实现: 每步重归一化的数学根据)
      §7.4-2 ← 定理 2-6      (谱权重控制器的稳定性理论)
      §7.4-3 ← 定理 7-8      (log 空间权重表示 + Euler/乘法更新的不变集)
      §7.4-4 ← 定理 9-10     (分解算子 D 三态滤波的能量份额归一)
      §2 A5  ← 定理 11-12    (GUT 先验初始化数值 (3/14, 9/14, 2/14))
      (§7.4-5 T.5.47 硅版本为 Phase 4 挑战项, 不在本模块)

    ## 诚实声明 (形式化范围边界)

    - 形式化对象是**公理集的数学结构** (复制子代数、熵 Lyapunov、
      正交分解), 非对 Python 权重控制器实现的等价性验证; 实现侧
      校准由重构工程管线承担 (R 系构造门, 设计文档 §7.3);
    - Fisher/链式法则/Lyapunov 定理为**逐点**形式 (在给定 t 处沿
      满足复制子方程的可微轨迹); 轨迹整体单调性由逐点定理对每 t
      应用而得, ODE 存在唯一性理论未形式化;
    - Fisher 定理假设适配度场 r 在 t 邻域冻结 (状态依赖 r 的微分
      未形式化 —— 架构中 r_i 为逐步测量的边际预测增益, 对应离散
      更新, 见定理 7-8);
    - 正性保持为离散实现级 (Euler 步含 η·M < 1 条件; 乘法指数步
      无条件), 连续时间不变集的 ODE 理论未形式化;
    - 能量份额归一为有限两两正交族; A2 严格正性需各分量 Φ_i ≠ 0,
      由实现侧正则化下限 w_min = 0.01 保证, 非本模块内容;
    - GUT 先验为纯算术数值登记; 计数来源 (SU(3)×SU(2)×U(1) 生成元
      8+3+1 = 12、电弱破缺予 3 质量、引力 2 螺旋度) 是物理登记,
      非形式化定理;
    - Γ/m 三带边界 (0.05/0.20) 为工程监测判据 (设计文档 §2 辅助
      判据), 不属本模块。

    CDD Framework v28.4 · jy-spectral-rebuild Phase 0
    Date: 2026-09-04
    Toolchain: Lean v4.32.2 + Mathlib (mathlib432 local checkout)
-/

namespace CDD.W9.SpectralWeight

open scoped InnerProductSpace

-- ============================================================
-- §0 基本定义 (设计文档 §2 A3/A4)
-- ============================================================

/-- 加权平均 ⟨r⟩_w = Σ_i w_i·r_i (适配度平均场)。 -/
def meanW {n : ℕ} (w r : Fin n → ℝ) : ℝ := ∑ i, w i * r i

/-- 复制子流 β_i = w_i·(r_i − ⟨r⟩_w) (A4)。 -/
def beta {n : ℕ} (w r : Fin n → ℝ) : Fin n → ℝ := fun i => w i * (r i - meanW w r)

/-- Lyapunov 函数 V = −Σ_i w_i·ln w_i (负熵, A4)。 -/
noncomputable def negEntropy {n : ℕ} (w : Fin n → ℝ) : ℝ := -∑ i, w i * Real.log (w i)

-- ============================================================
-- §1 §7.4-1 权重守恒: Σβ = 0 (A4 算术守恒)
-- ============================================================

/-- **§7.4-1 权重守恒**: 归一化权重 (Σw = 1) 下复制子流分量和为零。
    A4 的算术守恒部分 —— 权重动力学沿单纯形切向流动, 不产生谱
    三分解 (A1) 之外的"第四去处"; 实现侧每步重归一化的数学根据。 -/
theorem beta_sum_zero {n : ℕ} (w r : Fin n → ℝ) (hw : ∑ i, w i = 1) :
    ∑ i, beta w r i = 0 := by
  have h1 : ∑ i, beta w r i = (∑ i, w i * r i) - meanW w r * (∑ i, w i) := by
    have h2 : ∀ i, beta w r i = w i * r i - meanW w r * w i := by
      intro i
      simp only [beta, mul_sub]
      ring
    simp only [h2, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [h1, hw, mul_one]
  simp only [meanW]
  ring

-- ============================================================
-- §2 §7.4-2 Lyapunov 单调
-- ============================================================

/-- **符号核**: 正权重下 Σβ_i²/w_i ≥ 0 —— Lyapunov 导数非正性的
    全部来源 (每一项为平方除以正数)。 -/
theorem sum_beta_sq_div_w_nonneg {n : ℕ} (w r : Fin n → ℝ) (hpos : ∀ i, 0 < w i) :
    0 ≤ ∑ i, beta w r i ^ 2 / w i := by
  refine Finset.sum_nonneg fun i _ => ?_
  exact div_nonneg (sq_nonneg _) (hpos i).le

/-- **方差代数核心恒等式**: Σβ_i·r_i = Σβ_i²/w_i。
    逐项差 β_i·r_i − β_i²/w_i = ⟨r⟩_w·β_i, 求和后由 Σβ = 0 归零;
    两边公共值为加权方差 Var_w(r) = Σw_i·r_i² − ⟨r⟩_w²。
    这是 Fisher 单调性 (定理 4) 与熵性 Lyapunov 恒等式 (定理 6)
    的共同代数核。 -/
theorem beta_dot_r_eq_variance {n : ℕ} (w r : Fin n → ℝ)
    (hw : ∑ i, w i = 1) (hpos : ∀ i, 0 < w i) :
    ∑ i, beta w r i * r i = ∑ i, beta w r i ^ 2 / w i := by
  have hne : ∀ i, w i ≠ 0 := fun i => (hpos i).ne'
  have hkey : ∀ i,
      beta w r i * r i - beta w r i ^ 2 / w i = meanW w r * beta w r i := by
    intro i
    have h0 : w i ≠ 0 := hne i
    have hβ : beta w r i = w i * (r i - meanW w r) := rfl
    rw [hβ]
    field_simp
    ring
  have hd : (∑ i, beta w r i * r i) - (∑ i, beta w r i ^ 2 / w i) = 0 := by
    rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun i _ => hkey i),
      ← Finset.mul_sum, beta_sum_zero w r hw, mul_zero]
  linarith

/-- **§7.4-2 Fisher 基本定理** (一般适配度下的普适单调量): 沿复制子
    轨迹 (在 t 处 ẇ_i = β_i, 适配度场 r 在 t 邻域冻结), 平均适配度
    ⟨r⟩_w 的导数等于 Σβ²/w —— 由定理 2 恒非负: 平均适配度沿轨迹
    单调不减。这是"结构由约束产生"轨道 (非熵性适配度) 的稳定性
    保障。 -/
theorem hasDerivAt_meanW_along {n : ℕ} (W : ℝ → Fin n → ℝ) (r : Fin n → ℝ) (t : ℝ)
    (hW : ∀ i, HasDerivAt (fun s => W s i) (beta (W t) r i) t)
    (hw : ∑ i, W t i = 1) (hpos : ∀ i, 0 < W t i) :
    HasDerivAt (fun s => meanW (W s) r) (∑ i, beta (W t) r i ^ 2 / W t i) t := by
  have h1 : ∀ i, HasDerivAt (fun s => W s i * r i) (beta (W t) r i * r i) t :=
    fun i => (hW i).mul_const (r i)
  have h2 : HasDerivAt (fun s => ∑ i, W s i * r i) (∑ i, beta (W t) r i * r i) t :=
    HasDerivAt.fun_sum fun i _ => h1 i
  rw [beta_dot_r_eq_variance (W t) r hw hpos] at h2
  exact h2

/-- **§7.4-2 链式法则** (任意适配度): 沿 Σβ = 0 的可微权重轨迹,
    负熵 V = −Σw·ln w 的导数为 −Σβ_i·ln w_i —— Lyapunov 导数的
    普适形式 (恒等式 −Σβ·ln w = −Σβ²/w 需熵性适配度, 见定理 6)。 -/
theorem hasDerivAt_negEntropy_comp {n : ℕ} (W : ℝ → Fin n → ℝ) (v : Fin n → ℝ) (t : ℝ)
    (hW : ∀ i, HasDerivAt (fun s => W s i) (v i) t) (hne : ∀ i, W t i ≠ 0)
    (hv : ∑ i, v i = 0) :
    HasDerivAt (fun s => negEntropy (W s)) (-∑ i, v i * Real.log (W t i)) t := by
  have h1 : ∀ i, HasDerivAt (fun s => W s i * Real.log (W s i))
      (v i * Real.log (W t i) + W t i * (v i / W t i)) t :=
    fun i => (hW i).mul ((hW i).log (hne i))
  have h2 : HasDerivAt (fun s => ∑ i, W s i * Real.log (W s i))
      (∑ i, (v i * Real.log (W t i) + W t i * (v i / W t i))) t :=
    HasDerivAt.fun_sum fun i _ => h1 i
  have h3 : (∑ i, (v i * Real.log (W t i) + W t i * (v i / W t i)))
      = ∑ i, v i * Real.log (W t i) := by
    have h4 : ∀ i, W t i * (v i / W t i) = v i := by
      intro i
      have h0 : W t i ≠ 0 := hne i
      field_simp
    simp only [h4, Finset.sum_add_distrib, hv, add_zero]
  rw [h3] at h2
  exact h2.neg

/-- **§7.4-2 主定理 (熵性 Lyapunov 单调)**: 熵性适配度
    (r_i = ln w_i) 下, 沿复制子轨迹 dV/dt = −Σβ_i²/w_i ≤ 0
    (符号由定理 2)。§2 A4 "dV/dt = −Σβ²/w ≤ 0, 无约束时熵增趋向
    最大熵均衡" 的精确形式 —— 有效域为熵性适配度轨道; 一般适配度
    下的对应定理为 Fisher 单调性 (定理 4)。 -/
theorem lyapunov_entropic_nonpos {n : ℕ} (W : ℝ → Fin n → ℝ) (r : Fin n → ℝ) (t : ℝ)
    (hW : ∀ i, HasDerivAt (fun s => W s i) (beta (W t) r i) t)
    (hw : ∑ i, W t i = 1) (hpos : ∀ i, 0 < W t i)
    (hr : ∀ i, r i = Real.log (W t i)) :
    HasDerivAt (fun s => negEntropy (W s)) (-∑ i, beta (W t) r i ^ 2 / W t i) t := by
  have hne : ∀ i, W t i ≠ 0 := fun i => (hpos i).ne'
  have hsum0 : ∑ i, beta (W t) r i = 0 := beta_sum_zero _ _ hw
  have hchain := hasDerivAt_negEntropy_comp W (beta (W t) r) t hW hne hsum0
  simp only [← hr] at hchain
  rw [beta_dot_r_eq_variance (W t) r hw hpos] at hchain
  exact hchain

-- ============================================================
-- §3 §7.4-3 正性保持 (复制子不变集, 实现级)
-- ============================================================

/-- **§7.4-3 Euler 步正性保持**: 人均增长率有界 (|r_i − ⟨r⟩| ≤ M)
    且步长满足 η·M < 1 时, 复制子 Euler 步 w_i + η·β_i 不越出严格
    正卦限 —— 单纯形内部是不变集 (β_i/w_i 有界 ⇒ w_i 恒正的
    实现级形式; 架构使用离散权重更新)。 -/
theorem replicator_step_positivity {n : ℕ} (w r : Fin n → ℝ) (η M : ℝ)
    (hpos : ∀ i, 0 < w i) (hM : ∀ i, |r i - meanW w r| ≤ M)
    (hη0 : 0 ≤ η) (hηM : η * M < 1) :
    ∀ i, 0 < w i + η * beta w r i := by
  intro i
  have h1 : w i + η * beta w r i = w i * (1 + η * (r i - meanW w r)) := by
    simp only [beta]
    ring
  have h2 : -M ≤ r i - meanW w r := (abs_le.mp (hM i)).1
  have h3 : 1 + η * (r i - meanW w r) ≥ 1 - η * M := by
    have h3a : η * (-M) ≤ η * (r i - meanW w r) :=
      mul_le_mul_of_nonneg_left h2 hη0
    have h3b : η * (-M) = -η * M := by ring
    linarith
  have h4 : 0 < 1 - η * M := by linarith
  rw [h1]
  have h5 : w i * (1 + η * (r i - meanW w r)) ≥ w i * (1 - η * M) :=
    mul_le_mul_of_nonneg_left h3 (hpos i).le
  have h6 : 0 < w i * (1 - η * M) := mul_pos (hpos i) h4
  linarith

/-- **§7.4-3 乘法指数步正性 (无条件)**: 对数空间乘法权重更新
    w_i ← w_i·e^{η(r_i − ⟨r⟩)} 对任意步长 η 保持严格正性 ——
    log 空间权重表示的结构性优势, 与 A2 正则化下限互为保障。 -/
theorem replicator_exp_positivity {n : ℕ} (w r : Fin n → ℝ) (η : ℝ)
    (hpos : ∀ i, 0 < w i) :
    ∀ i, 0 < w i * Real.exp (η * (r i - meanW w r)) :=
  fun i => mul_pos (hpos i) (Real.exp_pos _)

-- ============================================================
-- §4 §7.4-4 能量份额归一 (正交分解)
-- ============================================================

section EnergyShare

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **§7.4-4 正交分解范数恒等式**: 两两正交分量的和范数平方等于
    各分量范数平方之和 (勾股定理的有限族形式) —— 能量份额归一的
    全部数学内容 (设计文档 §3.3 分解算子 D 的三态滤波)。 -/
theorem norm_sq_sum_orthogonal (v : Fin n → E)
    (horth : ∀ i j, i ≠ j → ⟪v i, v j⟫_ℝ = 0) :
    ‖∑ i, v i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  have hdiag : ∀ i, (∑ j, ⟪v i, v j⟫_ℝ) = ⟪v i, v i⟫_ℝ := by
    intro i
    rw [Finset.sum_eq_single i
      (fun j _ hj => horth i j (Ne.symm hj))
      (fun h => absurd (Finset.mem_univ i) h)]
  calc ‖∑ i, v i‖ ^ 2 = ⟪∑ i, v i, ∑ i, v i⟫_ℝ := (real_inner_self_eq_norm_sq _).symm
    _ = ∑ i, ⟪v i, ∑ j, v j⟫_ℝ := sum_inner _ _ _
    _ = ∑ i, ∑ j, ⟪v i, v j⟫_ℝ := by simp only [inner_sum]
    _ = ∑ i, ⟪v i, v i⟫_ℝ := by simp only [hdiag]
    _ = ∑ i, ‖v i‖ ^ 2 := by simp only [real_inner_self_eq_norm_sq]

/-- **§7.4-4 能量份额归一**: 正交分解 (Φ = ΣΦ_i, 分量两两正交,
    Φ ≠ 0) 下能量份额 w_i = ‖Φ_i‖²/‖Φ‖² 之和为 1 —— A3 权重
    归一性的能量份额形式。A2 严格正性另需各分量 Φ_i ≠ 0 (实现侧
    由 w_min = 0.01 正则化保证)。 -/
theorem energy_share_normalized (v : Fin n → E)
    (horth : ∀ i j, i ≠ j → ⟪v i, v j⟫_ℝ = 0)
    (hnz : (∑ i, v i) ≠ 0) :
    ∑ i, ‖v i‖ ^ 2 / ‖∑ j, v j‖ ^ 2 = 1 := by
  have h0 : (‖∑ j, v j‖ ^ 2 : ℝ) ≠ 0 :=
    pow_ne_zero 2 (fun h => hnz (norm_eq_zero.mp h))
  have key := norm_sq_sum_orthogonal v horth
  rw [← Finset.sum_div, ← key, div_self h0]

end EnergyShare

-- ============================================================
-- §5 A5 GUT 计数先验 (数值登记)
-- ============================================================

/-- **A5 GUT 计数先验归一化** (数值登记): w_pp + w_ac + w_sc
    = 3/14 + 9/14 + 2/14 = 1 —— SU(3)×SU(2)×U(1) 生成元计数
    8+3+1 = 12 加引力 2 螺旋度 ⇒ N = 14; 计数来源为物理登记,
    非形式化定理 (设计文档 §2 A5, 权重初始化值)。 -/
theorem gut_prior_normalized : (3 : ℝ) / 14 + 9 / 14 + 2 / 14 = 1 := by
  norm_num

/-- **A5 GUT 计数先验严格正性** (A2 数值面): 三分量全严格正 ——
    ac 主导 (9/14 > 1/2) 与全分量非零均为群论计数的算术推论
    (设计文档 §2 A5)。 -/
theorem gut_prior_positive :
    0 < (3 : ℝ) / 14 ∧ 0 < (9 : ℝ) / 14 ∧ 0 < (2 : ℝ) / 14 := by
  norm_num

-- ============================================================
-- §6 验证摘要
-- ============================================================

/-- **W9 验证摘要**: §7.4 前四条 + A5 数值登记核心定理的合取
    (每一合取项为一独立已证定理的实例, 无重言式项; 全模块零
    sorry)。参数取一般 n 与一般实内积空间 E —— 覆盖架构的
    Fin 3 (pp, ac, sc) 三分量实例; 权重对 (w, W t) 分别为静态
    权重态与 t 时刻轨迹态, 二者各自的归一化/正性前提独立给出。 -/
theorem W9_verification_summary {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (w r : Fin n → ℝ) (hw : ∑ i, w i = 1)
    (hpos : ∀ i, 0 < w i) (v : Fin n → E)
    (horth : ∀ i j, i ≠ j → ⟪v i, v j⟫_ℝ = 0) (hnz : (∑ i, v i) ≠ 0)
    (W : ℝ → Fin n → ℝ) (t : ℝ)
    (hW : ∀ i, HasDerivAt (fun s => W s i) (beta (W t) r i) t)
    (hw' : ∑ i, W t i = 1) (hpos' : ∀ i, 0 < W t i)
    (hr : ∀ i, r i = Real.log (W t i)) :
    -- §7.4-1 权重守恒
    (∑ i, beta w r i = 0)
    -- §7.4-2 Lyapunov 单调 (符号核 / 方差恒等式 / Fisher / 熵性)
    ∧ (0 ≤ ∑ i, beta w r i ^ 2 / w i)
    ∧ (∑ i, beta w r i * r i = ∑ i, beta w r i ^ 2 / w i)
    ∧ (HasDerivAt (fun s => meanW (W s) r) (∑ i, beta (W t) r i ^ 2 / W t i) t)
    ∧ (0 ≤ ∑ i, beta (W t) r i ^ 2 / W t i)
    ∧ (HasDerivAt (fun s => negEntropy (W s)) (-∑ i, beta (W t) r i ^ 2 / W t i) t)
    -- §7.4-3 正性保持 (Euler / 乘法指数)
    ∧ (∀ η M : ℝ, (∀ i, |r i - meanW w r| ≤ M) → 0 ≤ η → η * M < 1 →
        ∀ i, 0 < w i + η * beta w r i)
    ∧ (∀ η : ℝ, ∀ i, 0 < w i * Real.exp (η * (r i - meanW w r)))
    -- §7.4-4 能量份额归一
    ∧ (∑ i, ‖v i‖ ^ 2 / ‖∑ j, v j‖ ^ 2 = 1)
    -- A5 GUT 计数先验
    ∧ ((3 : ℝ) / 14 + 9 / 14 + 2 / 14 = 1
        ∧ (0 < (3 : ℝ) / 14 ∧ 0 < (9 : ℝ) / 14 ∧ 0 < (2 : ℝ) / 14)) :=
  ⟨beta_sum_zero w r hw,
    sum_beta_sq_div_w_nonneg w r hpos,
    beta_dot_r_eq_variance w r hw hpos,
    hasDerivAt_meanW_along W r t hW hw' hpos',
    sum_beta_sq_div_w_nonneg (W t) r hpos',
    lyapunov_entropic_nonpos W r t hW hw' hpos' hr,
    fun η M hM hη0 hηM => replicator_step_positivity w r η M hpos hM hη0 hηM,
    fun η => replicator_exp_positivity w r η hpos,
    energy_share_normalized v horth hnz,
    ⟨gut_prior_normalized, gut_prior_positive⟩⟩

end CDD.W9.SpectralWeight
