import CddFormalization.RH_MeasureTheory
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.ContinuousMap.Bounded.Basic

open scoped ENNReal NNReal BoundedContinuousFunction

noncomputable section

/-! # Riemann Hypothesis: 弱收敛等价网络 (阶段 1)

    本模块将 RH 的测度论等价网络 (`RH_MeasureTheory`) 扩展到弱收敛 (收敛分布) 维度,
    构造 R-截断零点实部经验测度并建立其与 δ_{1/2} 的退化等价:

        RH  ↔  ∀ R, ν_R = δ_{1/2}                    (逐截断退化, 节点 6)
           ↔  ∀ R, supp (Re_* μ_Z^R) ⊆ {1/2}         (逐截断支撑刚性, 节点 7)
        RH  →  ν_R ⇒ δ_{1/2}  (R → ∞, 弱收敛)         (推论, 单向)

    其中 `ν_R := normalize (Re_* (count ↾ truncatedZeros R))` 是 R-截断非平凡零点
    实部经验分布的归一化 (概率测度).

    ## 方法论要点: 为什么等价必须"逐截断"陈述

    渐近弱收敛 `ν_R ⇒ δ_{1/2} (R → ∞)` **严格弱于** RH: 若偏线零点只有有限个
    (甚至零密度), 经验分布仍弱收敛到 δ_{1/2} —— 极限陈述会遗忘稀疏偏离.
    因此与 RH 真正等价的是逐截断的精确退化: **每个**截断的经验分布都是 δ_{1/2}.
    这把 "零点能级全同简并于临界线" (Hilbert-Pólya 谱语言的简并性) 形式化为
    有限阶段的恒等式, 而非仅在无穷远处成立的极限性质.

    ## 证明结构

    * 正向: RH ⟹ 截断集 ⊆ 临界线 ⟹ `Re_* μ = N(R) • δ_{1/2}`
      (map_congr + map_const) ⟹ 归一化为 δ_{1/2};
    * 反向: 偏线零点 z 落入截断 R = |z|, 其实部单点集质量 ≥ 1 > 0,
      与 δ_{1/2} 的零质量矛盾;
    * 弱收敛推论: 逐截断退化使 R ↦ ν_R 为常值映射, 收敛平凡成立 ——
      该单向性是上述方法论要点的形式化体现.

    数学基础:
    - Mathlib.MeasureTheory.Measure.FiniteMeasure (FiniteMeasure, normalize)
    - Mathlib.MeasureTheory.Measure.DiracProba (diracProba)
    - Mathlib.MeasureTheory.Measure.Dirac (map_const, dirac_apply)
    - Mathlib.MeasureTheory.Measure.Map (map_congr, map_apply)
    - ProbabilityMeasure.eq_of_forall_apply_eq (概率测度相等判据)
    - ProbabilityMeasure.tendsto_iff_forall_integral_tendsto (弱收敛的 BCF 特征)

    References:
    - Billingsley (1999) Convergence of Probability Measures (弱收敛经典框架)
    - RH_MeasureTheory.lean (既有测度论等价网络: 节点 1-5)
-/

namespace RHWeakConvergence

open MeasureTheory Set RHMeasureTheory Complex Filter Topology

-- ============================================================
-- 1. 截断零点的有限测度结构与实部投影
-- ============================================================

/-- 截断零点集可测 (可测零点集 ∩ 闭球). -/
theorem measurableSet_truncatedZeros (R : ℝ) : MeasurableSet (truncatedZeros R) :=
  measurableSet_nontrivialZeros.inter Metric.isClosed_closedBall.measurableSet

/-- 截断零点计数 `N(R) = |{ρ ∈ nontrivialZeros : |ρ| ≤ R}|` (ℝ≥0∞ 值).

    这是经验测度归一化的分母; 由截断有限性, `N(R) < ∞` 无条件成立. -/
def zeroCount (R : ℝ) : ℝ≥0∞ := Measure.count (truncatedZeros R)

theorem zeroCount_ne_zero {R : ℝ} (hne : (truncatedZeros R).Nonempty) : zeroCount R ≠ 0 :=
  fun h => hne.ne_empty (Measure.count_eq_zero_iff.mp h)

theorem zeroCount_ne_top (R : ℝ) : zeroCount R ≠ ∞ :=
  ((Measure.count_apply_lt_top).mpr (truncatedZeros_finite R)).ne

/-- 截断计数测度是有限测度: 截断集有限 ⇒ 总质量有限.

    有限性是零密度估计 (Guth-Maynard 2024) 的形式化锚点:
    它使截断计数测度可打包为 `FiniteMeasure`, 从而可归一化. -/
theorem isFiniteMeasure_truncatedZeroMeasure (R : ℝ) :
    IsFiniteMeasure (Measure.count.restrict (truncatedZeros R)) := by
  constructor
  rw [Measure.restrict_apply_univ]
  exact (Measure.count_apply_lt_top).mpr (truncatedZeros_finite R)

/-- R-截断零点计数有限测度: 截断集上计数测度的 `FiniteMeasure` 打包. -/
def truncatedZeroFM (R : ℝ) : FiniteMeasure ℂ :=
  ⟨Measure.count.restrict (truncatedZeros R), isFiniteMeasure_truncatedZeroMeasure R⟩

@[simp]
theorem truncatedZeroFM_toMeasure (R : ℝ) :
    (truncatedZeroFM R : Measure ℂ) = Measure.count.restrict (truncatedZeros R) :=
  rfl

/-- 截断实部经验测度 (归一化前): 截断零点计数测度在 Re 下的推前. -/
def truncatedReFM (R : ℝ) : FiniteMeasure ℝ :=
  (truncatedZeroFM R).map Complex.re

@[simp]
theorem truncatedReFM_toMeasure (R : ℝ) :
    (truncatedReFM R : Measure ℝ) =
      Measure.map Complex.re (Measure.count.restrict (truncatedZeros R)) :=
  rfl

/-- 截断实部经验测度的显式集合公式 (无条件):
    `(Re_* μ_Z^R)(A) = count {ρ ∈ truncatedZeros R : Re ρ ∈ A}`. -/
theorem truncatedReMeasure_apply (R : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    (truncatedReFM R : Measure ℝ) A =
      Measure.count (Complex.re ⁻¹' A ∩ truncatedZeros R) := by
  rw [truncatedReFM_toMeasure, Measure.map_apply Complex.measurable_re hA,
    Measure.restrict_apply' (measurableSet_truncatedZeros R)]

-- ============================================================
-- 2. 零点落入截断: 质量下界引理
-- ============================================================

/-- 任意非平凡零点落入其模长截断 (闭球以 0 为中心). -/
theorem mem_truncatedZeros_norm {z : ℂ} (hz : z ∈ nontrivialZeros) :
    z ∈ truncatedZeros ‖z‖ :=
  ⟨hz, Metric.mem_closedBall.mpr (by rw [Complex.dist_eq, sub_zero])⟩

/-- 任意零点在模长截断的实部单点预像中被计入 (计数下界).

    这是反向论证的核心: 任意零点 z 都使截断经验测度在其实部单点集
    `{Re z}` 上质量 ≥ 1, 无需任何额外假设. -/
theorem one_le_count_truncated_re_singleton {z : ℂ} (hz : z ∈ nontrivialZeros) :
    (1 : ℝ≥0∞) ≤
      Measure.count (Complex.re ⁻¹' {Complex.re z} ∩ truncatedZeros ‖z‖) := by
  calc (1 : ℝ≥0∞) = Measure.count ({z} : Set ℂ) := (Measure.count_singleton z).symm
    _ ≤ Measure.count (Complex.re ⁻¹' {Complex.re z} ∩ truncatedZeros ‖z‖) := by
        refine measure_mono ?_
        intro w hw
        simp only [Set.mem_singleton_iff] at hw
        subst hw
        exact ⟨rfl, mem_truncatedZeros_norm hz⟩

/-- 偏线零点在模长截断的临界线补集预像中被计入.

    由单点集下界经 `{Re z} ⊆ {1/2}ᶜ` (Re z ≠ 1/2) 单调性导出. -/
theorem one_le_count_truncated_re_preimage {z : ℂ} (hz : z ∈ nontrivialZeros)
    (hnc : Complex.re z ≠ 1 / 2) :
    (1 : ℝ≥0∞) ≤
      Measure.count (Complex.re ⁻¹' ({(1 / 2 : ℝ)}ᶜ) ∩ truncatedZeros ‖z‖) := by
  refine le_trans (one_le_count_truncated_re_singleton hz) (measure_mono ?_)
  rintro w ⟨hw1, hw2⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hw1
  refine ⟨?_, hw2⟩
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
  rw [hw1]
  exact hnc

/-- Measure 层的质量下界: 截断投影测度在零点实部处质量 ≥ 1. -/
theorem one_le_truncatedReMeasure_apply {z : ℂ} (hz : z ∈ nontrivialZeros) :
    (1 : ℝ≥0∞) ≤ (truncatedReFM ‖z‖ : Measure ℝ) {Complex.re z} := by
  rw [truncatedReMeasure_apply _ (measurableSet_singleton _)]
  exact one_le_count_truncated_re_singleton hz

/-- ℝ≥0 层的质量下界 (FiniteMeasure 应用值). -/
theorem one_le_truncatedReFM_apply {z : ℂ} (hz : z ∈ nontrivialZeros) :
    (1 : ℝ≥0) ≤ (truncatedReFM ‖z‖) {Complex.re z} := by
  have h := one_le_truncatedReMeasure_apply hz
  rwa [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure, ← ENNReal.coe_one,
    ENNReal.coe_le_coe] at h

-- ============================================================
-- 3. 归一化引理: 纯量倍 Dirac 测度的归一化
-- ============================================================

/-- `diracProba` 的集合值公式 (rfl 展开). -/
theorem diracProba_apply {X : Type*} [MeasurableSpace X] (a : X) (s : Set X) :
    (diracProba a) s = (Measure.dirac a s).toNNReal :=
  rfl

/-- `diracProba` 在不含该点的集合上为零. -/
theorem diracProba_apply_of_notMem {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    {a : X} {s : Set X} (h : a ∉ s) : (diracProba a) s = 0 := by
  rw [diracProba_apply, Measure.dirac_apply, Set.indicator_of_notMem h, ENNReal.toNNReal_zero]

/-- **归一化引理**: 若有限测度是 Dirac 测度的纯量倍 `ν = c • δ_a` (c ≠ 0),
    则其归一化恰为 `δ_a`.

    经验测度退化的机制: 均匀缩放不改变分布形状.
    (c = ∞ 的情形对有限测度不可能: 总质量有限排除无穷纯量倍.) -/
theorem normalize_eq_diracProba_of_smul {X : Type*} [MeasurableSpace X] [Nonempty X]
    {ν : FiniteMeasure X} (a : X) {c : ℝ≥0∞} (hc0 : c ≠ 0)
    (h : (ν : Measure X) = c • Measure.dirac a) :
    ν.normalize = diracProba a := by
  have hmasscoe : (ν.mass : ℝ≥0∞) = c := by
    rw [FiniteMeasure.ennreal_mass, h, Measure.smul_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ a), smul_eq_mul, mul_one]
  have hmassne : ν.mass ≠ 0 := by
    intro h0
    exact hc0 (by rw [← hmasscoe, h0, ENNReal.coe_zero])
  have hνne : ν ≠ 0 := ν.mass_nonzero_iff.mp hmassne
  have hmass : c.toNNReal = ν.mass := by rw [← hmasscoe, ENNReal.toNNReal_coe]
  apply ProbabilityMeasure.eq_of_forall_apply_eq
  intro s _
  have h2 : (ν s : ℝ≥0∞) = c • (Measure.dirac a s) := by
    rw [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure, h, Measure.smul_apply]
  have h3 : ν s = c.toNNReal * (Measure.dirac a s).toNNReal := by
    have h4 := congrArg ENNReal.toNNReal h2
    rwa [ENNReal.toNNReal_coe, smul_eq_mul, ENNReal.toNNReal_mul] at h4
  rw [ν.normalize_eq_of_nonzero hνne, h3, hmass, diracProba_apply]
  exact inv_mul_cancel_left₀ hmassne _

-- ============================================================
-- 4. RH 下的显式形式: 截断投影测度 = N(R) • δ_{1/2}
-- ============================================================

/-- **RH 下的显式形式**: 截断实部经验测度是 δ_{1/2} 的 `N(R)` 倍.

    证明: RH ⟹ 截断集 ⊆ 临界线 ⟹ Re 在截断测度下几乎处处等于常值 1/2
    (map_congr) ⟹ 推前测度 = 总质量 • δ_{1/2} (map_const). -/
theorem truncatedReFM_eq_smul_dirac (hRH : riemannHypothesis) (R : ℝ) :
    (truncatedReFM R : Measure ℝ) = zeroCount R • Measure.dirac (1 / 2 : ℝ) := by
  have hae : Complex.re =ᵐ[Measure.count.restrict (truncatedZeros R)]
      fun _ : ℂ => 1 / 2 := by
    refine ae_restrict_of_forall_mem (measurableSet_truncatedZeros R) ?_
    intro z hz
    exact hRH hz.1
  unfold zeroCount
  rw [truncatedReFM_toMeasure, Measure.map_congr hae, Measure.map_const,
    Measure.restrict_apply_univ]

-- ============================================================
-- 5. 截断投影经验测度 (归一化) 与逐截断退化等价
-- ============================================================

open scoped Classical in
/-- **截断投影经验测度** `ν_R`: R-截断非平凡零点实部经验分布的归一化 (概率测度).

    空截断 (该半径内无零点) 时约定为 δ_{1/2}, 使定义对所有 R 全总,
    且 RH ⟹ ∀ R, ν_R = δ_{1/2} 无例外成立. -/
noncomputable def truncatedProjectedMeasure (R : ℝ) : ProbabilityMeasure ℝ :=
  if (truncatedZeros R).Nonempty then (truncatedReFM R).normalize else diracProba (1 / 2 : ℝ)

theorem truncatedProjectedMeasure_of_nonempty {R : ℝ} (hne : (truncatedZeros R).Nonempty) :
    truncatedProjectedMeasure R = (truncatedReFM R).normalize :=
  if_pos hne

theorem truncatedProjectedMeasure_of_empty {R : ℝ} (he : truncatedZeros R = ∅) :
    truncatedProjectedMeasure R = diracProba (1 / 2 : ℝ) :=
  if_neg (Set.not_nonempty_iff_eq_empty.mpr he)

/-- **等价节点 6 (逐截断退化)**: RH ⟺ 对每个 R, 截断投影经验测度退化为 δ_{1/2}.

    这是 RH 的收敛分布表述: 零点实部经验分布在**每个**有限截断上都
    全同简并于临界线, 而非仅在渐近极限中集中 (见模块文档的方法论要点).
    [K3 语义标注, 2026-09-08] **等价重述 (definitional / 初等重构),
    非 RH 证明** — 本网络证明 RH 的各等价形式互推, 尚未证明 (也未否定)
    RH 本身. -/
theorem rh_iff_truncated_projected_eq_dirac :
    riemannHypothesis ↔ ∀ R, truncatedProjectedMeasure R = diracProba (1 / 2 : ℝ) := by
  constructor
  · intro hRH R
    by_cases hne : (truncatedZeros R).Nonempty
    · rw [truncatedProjectedMeasure_of_nonempty hne,
        normalize_eq_diracProba_of_smul (1 / 2 : ℝ) (zeroCount_ne_zero hne)
          (truncatedReFM_eq_smul_dirac hRH R)]
    · exact truncatedProjectedMeasure_of_empty (Set.not_nonempty_iff_eq_empty.mp hne)
  · intro h z hz
    by_contra hnc
    have hzne : Complex.re z ≠ 1 / 2 := fun hc => hnc hc
    have hzR : z ∈ truncatedZeros ‖z‖ := mem_truncatedZeros_norm hz
    have hkey : (truncatedReFM ‖z‖).normalize = diracProba (1 / 2 : ℝ) := by
      have hR := h ‖z‖
      rwa [truncatedProjectedMeasure_of_nonempty ⟨z, hzR⟩] at hR
    have hge : (1 : ℝ≥0) ≤ (truncatedReFM ‖z‖) {Complex.re z} :=
      one_le_truncatedReFM_apply hz
    have hmass : (1 : ℝ≥0) ≤ (truncatedReFM ‖z‖).mass :=
      hge.trans ((truncatedReFM ‖z‖).apply_le_mass _)
    have hne : (truncatedReFM ‖z‖) ≠ 0 :=
      (truncatedReFM ‖z‖).mass_nonzero_iff.mp fun h0 => by
        rw [h0] at hmass
        exact absurd hmass (not_le.mpr zero_lt_one)
    have hpos : (0 : ℝ≥0) < (truncatedReFM ‖z‖).normalize {Complex.re z} := by
      rw [(truncatedReFM ‖z‖).normalize_eq_of_nonzero hne]
      exact mul_pos (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hmass))
        (lt_of_lt_of_le zero_lt_one hge)
    have hzero : (diracProba (1 / 2 : ℝ)) {Complex.re z} = 0 :=
      diracProba_apply_of_notMem (fun hm => hzne (Set.mem_singleton_iff.mp hm).symm)
    rw [hkey] at hpos
    rw [hzero] at hpos
    exact lt_irrefl 0 hpos

-- ============================================================
-- 6. 逐截断支撑刚性 (连接既有等价网络)
-- ============================================================

/-- **等价节点 7 (逐截断支撑刚性)**: RH ⟺ 对每个 R, 截断实部投影测度的支撑
    含于单点集 {1/2}.

    这是节点 5 (`rh_iff_map_re_support`, 全局边缘分布退化) 的截断化版本,
    两者通过 `support_subset_singleton_iff` 共享支撑-单点机制.
    [K3 语义标注, 2026-09-08] **等价重述 (definitional / 初等重构),
    非 RH 证明** — 本网络证明 RH 的各等价形式互推, 尚未证明 (也未否定)
    RH 本身. -/
theorem rh_iff_truncated_re_support :
    riemannHypothesis ↔ ∀ R, (truncatedReFM R : Measure ℝ).support ⊆ {(1 / 2 : ℝ)} := by
  simp only [support_subset_singleton_iff]
  constructor
  · intro hRH R
    rw [truncatedReMeasure_apply R (measurableSet_singleton _).compl,
      Measure.count_eq_zero_iff]
    apply eq_empty_iff_forall_notMem.mpr
    rintro z ⟨hz1, hz2⟩
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] at hz1
    exact hz1 (hRH hz2.1)
  · intro h z hz
    by_contra hnc
    have hzne : Complex.re z ≠ 1 / 2 := fun hc => hnc hc
    have hzR : z ∈ truncatedZeros ‖z‖ := mem_truncatedZeros_norm hz
    have h0 : (truncatedReFM ‖z‖ : Measure ℝ) ({(1 / 2 : ℝ)}ᶜ) = 0 := h ‖z‖
    rw [truncatedReMeasure_apply _ (measurableSet_singleton _).compl] at h0
    have h1 : (1 : ℝ≥0∞) ≤ Measure.count
        (Complex.re ⁻¹' ({(1 / 2 : ℝ)}ᶜ) ∩ truncatedZeros ‖z‖) :=
      one_le_count_truncated_re_preimage hz hzne
    rw [h0] at h1
    exact absurd h1 (by simp)

-- ============================================================
-- 7. 弱收敛推论 (单向)
-- ============================================================

/-- **弱收敛推论 (单向)**: RH ⟹ 截断投影经验测度弱收敛到 δ_{1/2} (R → ∞).

    由逐截断退化 (节点 6), RH 下 R ↦ ν_R 是常值映射 δ_{1/2},
    收敛在弱拓扑 (收敛分布拓扑) 中平凡成立.

    注意单向性: 渐近弱收敛严格弱于 RH —— 有限个 (甚至零密度) 偏线零点
    不破坏弱收敛, 但破坏 RH. 等价内容已在节点 6 中逐截断陈述. -/
theorem rh_imp_tendsto_dirac :
    riemannHypothesis → Tendsto truncatedProjectedMeasure atTop (𝓝 (diracProba (1 / 2 : ℝ))) := by
  intro hRH
  have h : truncatedProjectedMeasure = fun _ : ℝ => diracProba (1 / 2 : ℝ) :=
    funext (rh_iff_truncated_projected_eq_dirac.mp hRH)
  rw [h]
  exact tendsto_const_nhds

/-- **BCF 积分收敛**: RH ⟹ 对每个有界连续函数 f, ∫ f dν_R → f(1/2) (R → ∞).

    这是弱收敛的 Portmanteau 定义式特征 (对检验函数类 BCF 的积分收敛),
    由 `ProbabilityMeasure.tendsto_iff_forall_integral_tendsto` 从弱收敛导出. -/
theorem rh_imp_integral_tendsto (hRH : riemannHypothesis) (f : ℝ →ᵇ ℝ) :
    Tendsto (fun R : ℝ => ∫ x, f x ∂((truncatedProjectedMeasure R : Measure ℝ))) atTop
      (𝓝 (f (1 / 2 : ℝ))) := by
  have hlim := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (rh_imp_tendsto_dirac hRH) f
  have hdirac : (∫ x, f x ∂((diracProba (1 / 2 : ℝ) : Measure ℝ))) = f (1 / 2 : ℝ) := by
    rw [show ((diracProba (1 / 2 : ℝ) : Measure ℝ)) = Measure.dirac (1 / 2 : ℝ) from rfl,
      integral_dirac (f : ℝ → ℝ) (1 / 2 : ℝ)]
  rw [hdirac] at hlim
  exact hlim

end RHWeakConvergence
