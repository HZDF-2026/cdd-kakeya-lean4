import CddFormalization.RH_WeakConvergence
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open scoped ENNReal

noncomputable section

/-! # Riemann Hypothesis: 偏差测度 d(R) (阶段 2c, 节点 12-14)

    本模块将 RH 的测度论等价网络 (`RH_MeasureTheory`, 节点 1-5;
    `RH_WeakConvergence`, 节点 6-7) 扩展到定量偏差维度, 构造截断投影
    经验测度在临界线补集上的质量 —— 偏差测度, 并证明:

        节点 12 (显式公式): d(R) = N_off(R)/N(R)   (非空截断; 空截断 d = 0)
        节点 13 (零偏差等价): RH ⟺ ∀ R, d(R) = 0
        节点 14 (定量灵敏度): d(R) > 0 ⟺ 截断内存在偏线零点;
                              截断内偏线零点迫使 d(R) ≥ 1/N(R);
                              RH ⟹ d(R) → 0 (R → ∞, 单向)

    ## 定位: 零密度估计与 RH 之间的测度论余量接口

    偏差测度是连接两个世界的枢纽对象:
    - 估值侧: 零密度估计 (Guth-Maynard 2024) 给出 N_off(T) 的上界增长;
    - RH 侧: 断言 N_off ≡ 0.
    d(R) 把两者的差距浓缩为 [0,1] 内的单个实数, 且 (节点 13) RH ⟺ 该余量
    在**每个**截断上精确为零 —— 逐截断陈述, 与节点 6/7 共享同一方法论铁律:
    渐近衰减陈述会遗忘稀疏偏离 (有限个甚至零密度偏线零点被归一化稀释).

    ## 与开放问题的接口

    d(R) 的非平凡精确衰减率 (RH 伪情形) 无先验估计; 若可表为 (log R)^{-c} 型,
    将为零密度估计提供新测度论入口 (主报告开放问题 3). 本模块给出其
    无条件灵敏度刻画 (节点 14) 与 RH 下的平凡情形 (d ≡ 0).

    证明结构:
    * 显式公式: ν_R 的 Measure 层归一化展开 (`toMeasure_normalize_eq_of_nonzero`)
      + 推前测度的计数公式 (`truncatedReMeasure_apply`) 直接给出 d = N⁻¹·N_off;
    * 零偏差等价: 正向由节点 6 (逐截断退化) + Dirac 无偏差;
      反向由单零点计数下界 (一个偏线零点 ⟹ N_off ≥ 1) + ENNReal 乘法正性
      得 d > 0, 与 ∀R, d = 0 矛盾;
    * 灵敏度: d > 0 ⟺ N_off > 0 ⟺ 截断偏线集非空 (计数测度零测 ⟺ 空集).

    数学基础:
    - RH_WeakConvergence.truncatedProjectedMeasure (ν_R, 节点 6)
    - FiniteMeasure.toMeasure_normalize_eq_of_nonzero (归一化的 Measure 层展开)
    - Measure.coe_nnreal_smul_apply / FiniteMeasure.ennreal_mass
    - ENNReal: mul_pos, inv_pos, inv_ne_zero, coe_inv

    References:
    - Guth & Maynard (2024) New large value estimates for Dirichlet polynomials
      (零密度估计背景: 偏差测度所度量的余量)
    - Billingsley (1999) Convergence of Probability Measures
    - RH_WeakConvergence.lean (节点 6-7: 逐截断退化与支撑刚性)
-/

namespace RHDeviationMeasure

open MeasureTheory Set RHMeasureTheory RHWeakConvergence Complex Filter Topology

-- ============================================================
-- 1. 截断偏线零点集与计数
-- ============================================================

/-- R-截断偏线零点集: 截断内实部偏离 1/2 的非平凡零点.

    交序与 `truncatedReMeasure_apply` 对齐, 使计数公式
    `offLineCount R = (Re_* μ_Z^R)({1/2}ᶜ)` 成为定义性恒等式. -/
def truncatedOffLineZeros (R : ℝ) : Set ℂ :=
  Complex.re ⁻¹' ({(1 / 2 : ℝ)}ᶜ) ∩ truncatedZeros R

/-- 截断偏线零点集 = 偏线零点集与闭球的交 (语义同一性). -/
theorem truncatedOffLineZeros_eq (R : ℝ) :
    truncatedOffLineZeros R = offLineZeros ∩ Metric.closedBall (0 : ℂ) R := by
  ext z
  simp only [truncatedOffLineZeros, Set.mem_inter_iff, Set.mem_preimage,
    Set.mem_compl_iff, Set.mem_singleton_iff, offLineZeros, Set.mem_sdiff,
    criticalLine, truncatedZeros, Set.mem_setOf_eq]
  tauto

theorem truncatedOffLineZeros_subset_truncated (R : ℝ) :
    truncatedOffLineZeros R ⊆ truncatedZeros R :=
  Set.inter_subset_right

theorem truncatedOffLineZeros_subset_offLine (R : ℝ) :
    truncatedOffLineZeros R ⊆ offLineZeros :=
  (truncatedOffLineZeros_eq R).subset.trans Set.inter_subset_left

/-- 截断偏线零点计数 `N_off(R)` (ℝ≥0∞ 值): 偏差测度的分子. -/
def offLineCount (R : ℝ) : ℝ≥0∞ := Measure.count (truncatedOffLineZeros R)

theorem offLineCount_eq (R : ℝ) :
    offLineCount R = Measure.count (Complex.re ⁻¹' ({(1 / 2 : ℝ)}ᶜ) ∩ truncatedZeros R) :=
  rfl

/-- **单零点计数下界**: 截断 R 内的偏线零点至少贡献计数 1.

    节点 14 定量下界的引擎: 单个偏线零点即产生可测偏差. -/
theorem one_le_offLineCount {z : ℂ} (hz : z ∈ nontrivialZeros)
    (hnc : Complex.re z ≠ 1 / 2) {R : ℝ} (hR : z ∈ truncatedZeros R) :
    (1 : ℝ≥0∞) ≤ offLineCount R := by
  have hsub : ({z} : Set ℂ) ⊆ truncatedOffLineZeros R := by
    intro w hw
    simp only [Set.mem_singleton_iff] at hw
    subst hw
    exact ⟨by simpa using hnc, hR⟩
  calc (1 : ℝ≥0∞) = Measure.count ({z} : Set ℂ) := (Measure.count_singleton z).symm
    _ ≤ offLineCount R := measure_mono hsub

-- ============================================================
-- 2. 偏差测度: 定义与显式公式 (节点 12)
-- ============================================================

/-- **偏差测度** `d(R)`: 截断投影经验测度 ν_R 在临界线补集上的质量.

    测度论余量: 偏线零点在截断经验分布中所占的比例质量;
    取值于 [0, 1] (`zero_le_deviation`, `deviation_le_one`). -/
def deviation (R : ℝ) : ℝ≥0∞ :=
  (truncatedProjectedMeasure R : Measure ℝ) ({(1 / 2 : ℝ)}ᶜ)

theorem deviation_def (R : ℝ) :
    deviation R = (truncatedProjectedMeasure R : Measure ℝ) ({(1 / 2 : ℝ)}ᶜ) :=
  rfl

/-- 截断投影测度的总质量即截断零点计数 (归一化的分母). -/
theorem truncatedReFM_mass (R : ℝ) : ((truncatedReFM R).mass : ℝ≥0∞) = zeroCount R := by
  rw [FiniteMeasure.ennreal_mass, truncatedReMeasure_apply R MeasurableSet.univ, zeroCount]
  simp

/-- Dirac 测度无偏差: δ_a 在 {a}ᶜ 上零测. -/
theorem dirac_compl_eq_zero (a : ℝ) : (Measure.dirac a) ({a}ᶜ) = 0 := by
  rw [Measure.dirac_apply]
  exact Set.indicator_of_notMem (by simp) _

/-- **节点 12 (空截断)**: 截断内无零点时偏差为零 (约定 ν_R = δ_{1/2}). -/
theorem deviation_of_empty {R : ℝ} (he : truncatedZeros R = ∅) : deviation R = 0 := by
  rw [deviation_def, truncatedProjectedMeasure_of_empty he]
  exact dirac_compl_eq_zero (1 / 2 : ℝ)

/-- **节点 12 (显式公式)**: 非空截断下 `d(R) = N(R)⁻¹ · N_off(R)`.

    偏差测度 = 截断偏线零点计数 / 截断零点总数:
    估值侧 (零密度上界) 与 RH 侧 (零偏差) 的公共货币. -/
theorem deviation_of_nonempty {R : ℝ} (hne : (truncatedZeros R).Nonempty) :
    deviation R = (zeroCount R)⁻¹ * offLineCount R := by
  have hmassne : (truncatedReFM R).mass ≠ 0 := by
    intro h0
    exact (zeroCount_ne_zero hne) (by rw [← truncatedReFM_mass R, h0, ENNReal.coe_zero])
  have hμne : (truncatedReFM R) ≠ 0 := (truncatedReFM R).mass_nonzero_iff.mp hmassne
  rw [deviation_def, truncatedProjectedMeasure_of_nonempty hne,
    (truncatedReFM R).toMeasure_normalize_eq_of_nonzero hμne,
    Measure.coe_nnreal_smul_apply, ENNReal.coe_inv hmassne, truncatedReFM_mass R,
    truncatedReMeasure_apply R ((measurableSet_singleton (1 / 2 : ℝ)).compl)]
  rfl

/-- **节点 12 (除法形式, 无条件)**: `d(R) = N_off(R)/N(R)` 对所有 R 成立
    (空截断时 0/0 的 ENNReal 算术约定恰为 0, 与 d = 0 一致). -/
theorem deviation_eq_div (R : ℝ) : deviation R = offLineCount R / zeroCount R := by
  by_cases hne : (truncatedZeros R).Nonempty
  · rw [deviation_of_nonempty hne, ENNReal.div_eq_inv_mul]
  · have he : truncatedZeros R = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hoff : truncatedOffLineZeros R = ∅ :=
      Set.eq_empty_of_subset_empty
        ((truncatedOffLineZeros_subset_truncated R).trans he.subset)
    rw [deviation_of_empty he,
      show offLineCount R = 0 from Measure.count_eq_zero_iff.mpr hoff]
    simp

theorem zero_le_deviation (R : ℝ) : 0 ≤ deviation R := by
  simp

/-- **节点 12 (界)**: 偏差测度取值于 [0, 1] (概率测度的集合质量). -/
theorem deviation_le_one (R : ℝ) : deviation R ≤ 1 := by
  rw [deviation_def]
  calc (truncatedProjectedMeasure R : Measure ℝ) ({(1 / 2 : ℝ)}ᶜ)
      ≤ (truncatedProjectedMeasure R : Measure ℝ) univ :=
        measure_mono (Set.subset_univ _)
    _ = 1 := measure_univ

-- ============================================================
-- 3. 节点 13: 零偏差等价
-- ============================================================

/-- **节点 13 (正向)**: RH ⟹ 偏差测度在所有截断上为零. -/
theorem deviation_eq_zero_of_rh (hRH : riemannHypothesis) (R : ℝ) : deviation R = 0 := by
  rw [deviation_def, (rh_iff_truncated_projected_eq_dirac.mp hRH) R]
  exact dirac_compl_eq_zero (1 / 2 : ℝ)

/-- **节点 13 (零偏差等价)**: RH ⟺ 偏差测度在每个截断上为零.

    逐截断陈述 (方法论铁律): 渐近版本 `d(R) → 0` 严格弱于 RH
    (有限个偏线零点在归一化下被稀释); 等价内容必须是每个有限
    截断上的精确零偏差.
    [K3 语义标注, 2026-09-08] **等价重述 (definitional / 初等重构),
    非 RH 证明** — 本网络证明 RH 的各等价形式互推, 尚未证明 (也未否定)
    RH 本身. -/
theorem rh_iff_deviation_eq_zero :
    riemannHypothesis ↔ ∀ R, deviation R = 0 := by
  constructor
  · exact deviation_eq_zero_of_rh
  · intro h z hz
    by_contra hnc
    have hzne : Complex.re z ≠ 1 / 2 := fun hc => hnc hc
    have hzR : z ∈ truncatedZeros ‖z‖ := mem_truncatedZeros_norm hz
    have h1 : (1 : ℝ≥0∞) ≤ offLineCount ‖z‖ := one_le_offLineCount hz hzne hzR
    have hne0 : offLineCount ‖z‖ ≠ 0 := by
      intro h0
      rw [h0] at h1
      exact absurd h1 (by simp)
    have hpos : 0 < deviation ‖z‖ := by
      rw [deviation_of_nonempty ⟨z, hzR⟩]
      exact ENNReal.mul_pos (ENNReal.inv_ne_zero.2 (zeroCount_ne_top ‖z‖)) hne0
    rw [h ‖z‖] at hpos
    exact lt_irrefl 0 hpos

-- ============================================================
-- 4. 节点 14: 定量灵敏度与衰减接口
-- ============================================================

/-- **节点 14 (灵敏度)**: 偏差测度恰好检测截断内偏线零点的存在性.

    `d(R) > 0 ⟺ 截断 R 内存在偏线零点` —— 偏差测度不遗漏也不虚报:
    灵敏度 (单个偏线零点 ⟹ 正偏差) 与特异性 (零偏差 ⟹ 无偏线零点). -/
theorem deviation_pos_iff (R : ℝ) :
    0 < deviation R ↔ (truncatedOffLineZeros R).Nonempty := by
  constructor
  · intro hpos
    by_cases hne : (truncatedZeros R).Nonempty
    · by_cases hoff : (truncatedOffLineZeros R).Nonempty
      · exact hoff
      · exfalso
        have h0 : offLineCount R = 0 :=
          Measure.count_eq_zero_iff.mpr (Set.not_nonempty_iff_eq_empty.mp hoff)
        rw [deviation_of_nonempty hne, h0, mul_zero] at hpos
        exact lt_irrefl 0 hpos
    · exfalso
      rw [deviation_of_empty (Set.not_nonempty_iff_eq_empty.mp hne)] at hpos
      exact lt_irrefl 0 hpos
  · intro hoff
    obtain ⟨z, hz⟩ := hoff
    have hzR : z ∈ truncatedZeros R := truncatedOffLineZeros_subset_truncated R hz
    have h1 : (1 : ℝ≥0∞) ≤ offLineCount R :=
      one_le_offLineCount hz.2.1 (by simpa using hz.1) hzR
    have hne0 : offLineCount R ≠ 0 := by
      intro h0
      rw [h0] at h1
      exact absurd h1 (by simp)
    rw [deviation_of_nonempty ⟨z, hzR⟩]
    exact ENNReal.mul_pos (ENNReal.inv_ne_zero.2 (zeroCount_ne_top R)) hne0

/-- **节点 14 (单零点定量下界)**: 截断 R 内的偏线零点迫使 `d(R) ≥ 1/N(R)`.

    单个偏线零点即产生不小于其经验占比的偏差 —— RH 的定量灵敏度:
    偏差测度可检测任意单个偏线零点, 并给出数值下界. -/
theorem inv_zeroCount_le_deviation {z : ℂ} (hz : z ∈ nontrivialZeros)
    (hnc : Complex.re z ≠ 1 / 2) {R : ℝ} (hR : z ∈ truncatedZeros R) :
    (zeroCount R)⁻¹ ≤ deviation R := by
  have hne : (truncatedZeros R).Nonempty := ⟨z, hR⟩
  have h1 : (1 : ℝ≥0∞) ≤ offLineCount R := one_le_offLineCount hz hnc hR
  rw [deviation_of_nonempty hne]
  calc (zeroCount R)⁻¹ = (zeroCount R)⁻¹ * 1 := (mul_one _).symm
    _ ≤ (zeroCount R)⁻¹ * offLineCount R := mul_le_mul_right h1 _

/-- **节点 14 (衰减接口, 单向)**: RH ⟹ d(R) → 0 (R → ∞).

    由节点 13, RH 下 d ≡ 0, 收敛平凡. 注意单向性 (与节点 6 的弱收敛
    推论同构): 渐近衰减严格弱于 RH —— 有限个 (甚至零密度) 偏线零点
    使 d(R) → 0 但破坏 RH. d(R) 的非平凡精确衰减率 (RH 伪情形)
    是主报告开放问题 3, 本模块不宣称任何进展. -/
theorem rh_imp_deviation_tendsto_zero (hRH : riemannHypothesis) :
    Tendsto deviation atTop (𝓝 (0 : ℝ≥0∞)) := by
  have h : deviation = fun _ : ℝ => (0 : ℝ≥0∞) :=
    funext ((rh_iff_deviation_eq_zero).mp hRH)
  rw [h]
  exact tendsto_const_nhds

end RHDeviationMeasure
