import CddFormalization.RH_MeasureTheory
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Archimedean.Defs

open scoped ENNReal

noncomputable section

/-! # Riemann Hypothesis: 谱测度等价网络 (阶段 2d, 节点 15-17)

    本模块将 RH 的测度论等价网络 (`RH_MeasureTheory`, `RH_WeakConvergence`,
    `RH_DeviationMeasure`) 推进到 Hilbert-Pólya 谱路线的核心: 引入临界线嵌入
    `γ(t) = 1/2 + t·i` 与谱高度测度 `μ_spec = Im_* μ_Z`, 建立谱化等价网络:

        RH  ↔  ∃ μ : Measure ℝ, μ_Z = γ_* μ              (谱化等价, 节点 15)
           →  该 μ 典范唯一: μ = Im_* μ_Z                 (典范唯一性, 节点 16)
        RH  ↔  P_* μ_Z = μ_Z,  P = γ ∘ Im                (投影不动点, 节点 17)

    其中 `γ_* μ := Measure.map criticalLineEmbed μ` 是临界线嵌入的推前,
    `μ_Z := zeroCountingMeasure` 是零点计数测度.

    ## 谱解读 (Hilbert-Pólya 测度影子)

    Hilbert-Pólya 纲领寻求自伴算子 H 使其谱恰为非平凡零点的虚部 (能级高度).
    本模块的谱化等价把该纲领压缩为纯测度论陈述: "零点计数测度完全由某个
    高度测度经临界线嵌入重构" —— 即零点测度在嵌入 `γ` 下无信息损耗.
    典范唯一性来自 `Im ∘ γ = id` (临界线嵌入以虚部投影为左逆);
    投影不动点刻画 P 为临界线的保核收缩, RH ⟺ μ_Z 是 P 的不动点.

    ## 无条件的离散谱结构

    谱高度测度 **无条件** 满足离散谱性质 (不依赖 RH 真伪):
    * 局部有限性: 每个紧高度窗 `[-T, T]` 内能级有限 (横带内零点有限);
    * σ-有限性: `μ_spec` 是 σ-有限测度 (Radon-Nikodym 框架的入口).
    因此 RH 的内容不是 "高度谱是离散谱" (这无条件成立), 而是 "该离散谱
    承载了全部零点测度" —— 偏线零点测度恒为零 (与节点 3 的零测刻画一致).

    ## 证明结构

    * 节点 15 正向: RH ⟹ (γ ∘ Im) =ᵐ[μ_Z] id (零点在临界线上)
      ⟹ `map_congr` 使推前复合坍缩 ⟹ γ_* (Im_* μ_Z) = μ_Z;
    * 节点 15 反向: γ(ℝ) ⊆ 临界线 ⟹ μ_Z(临界线ᶜ) = (γ_* μ)(γ⁻¹' 临界线ᶜ)
      = μ(∅) = 0 ⟹ 由节点 3 (零测刻画) 得 RH;
    * 节点 16: `Im ∘ γ = id` ⟹ μ = id_* μ = (Im ∘ γ)_* μ
      = Im_* (γ_* μ) = Im_* μ_Z;
    * 节点 17: P = γ ∘ Im 且 P(ℂ) ⊆ 临界线 ⟹ 反向经零测刻画;
      正向坍缩为节点 15 正向 (推前复合的结合律).

    数学基础:
    - Mathlib.MeasureTheory.Measure.Map (map_map, map_congr, map_id)
    - Mathlib.MeasureTheory.Measure.Typeclasses.SFinite (SigmaFinite,
      FiniteSpanningSetsIn 的四字段结构)
    - Mathlib.MeasureTheory.Measure.Typeclasses.Finite (IsFiniteMeasure)
    - RH_MeasureTheory (zeroCountingMeasure, criticalLine,
      rh_iff_zeroCountingMeasure_compl, truncatedZeros_finite)

    References:
    - Hilbert-Pólya 纲领 (谱方法; 经由 Odlyzko (1987) 综述转述)
    - Berry & Keating (1999) The Riemann zeros and eigenvalue asymptotics
    - Connes (1999) Trace formula in noncommutative geometry and zeros of zeta
    - Rudnick & Sarnak (1996) Zeros of principal L-functions and random
      matrix theory (高度谱统计背景)
-/

namespace RHSpectralMeasure

open MeasureTheory Set RHMeasureTheory Complex

-- ============================================================
-- 1. 临界线嵌入 γ 与临界线投影 P = γ ∘ Im
-- ============================================================

/-- 临界线嵌入 `γ(t) = 1/2 + t·i`: 把实轴 (谱高度轴) 一一嵌入为临界线.

    这是 Hilbert-Pólya 谱路线的几何载体: 高度 t ∈ ℝ 对应临界线上的
    能级位置 `1/2 + t·i`. -/
def criticalLineEmbed : ℝ → ℂ := fun t => ⟨1 / 2, t⟩

@[simp]
theorem criticalLineEmbed_re (t : ℝ) : (criticalLineEmbed t).re = 1 / 2 := rfl

@[simp]
theorem criticalLineEmbed_im (t : ℝ) : (criticalLineEmbed t).im = t := rfl

/-- 嵌入的代数形式: `γ(t) = (1/2 : ℝ) + t·I` (用于连续性).

    注意常数项用实数嵌入 `((1/2 : ℝ) : ℂ)` 而非复数除法 `(1/2 : ℂ)`,
    前者定义性展开为 `⟨1/2, 0⟩`, 后者经求逆无法定义性规约. -/
theorem criticalLineEmbed_eq (t : ℝ) :
    criticalLineEmbed t = ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
  apply Complex.ext
  · show (1 / 2 : ℝ) = (1 / 2 : ℝ) + (t * 0 - 0 * 1)
    ring
  · show t = 0 + (t * 1 + 0 * 0)
    ring

/-- 临界线嵌入连续 (仿射映射: 常数 + 实嵌入 × I). -/
theorem continuous_criticalLineEmbed : Continuous criticalLineEmbed := by
  have h : criticalLineEmbed = fun t : ℝ => ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
    funext t
    exact criticalLineEmbed_eq t
  rw [h]
  exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)

/-- 临界线嵌入可测 (连续 ⇒ Borel 可测). -/
theorem measurable_criticalLineEmbed : Measurable criticalLineEmbed :=
  continuous_criticalLineEmbed.measurable

/-- 临界线嵌入单射: 高度可由能级位置恢复 (虚部投影是其左逆). -/
theorem criticalLineEmbed_injective : Function.Injective criticalLineEmbed := by
  intro a b h
  have h1 : (criticalLineEmbed a).im = (criticalLineEmbed b).im := by rw [h]
  simp only [criticalLineEmbed_im] at h1
  exact h1

/-- 嵌入的像恰为临界线: `γ(ℝ) = {Re s = 1/2}`. -/
theorem criticalLineEmbed_range : Set.range criticalLineEmbed = criticalLine := by
  ext z
  simp only [Set.mem_range, criticalLine, Set.mem_setOf_eq]
  constructor
  · rintro ⟨t, ht⟩
    rw [← ht]
    exact criticalLineEmbed_re t
  · intro hre
    exact ⟨z.im, Complex.ext (by rw [criticalLineEmbed_re, hre])
      (criticalLineEmbed_im z.im)⟩

/-- 临界线投影 `P(z) = γ(Im z)`: 任意点的临界线代表元 (高度不变, 实部归位).

    `P` 是临界线的保核收缩: `P ∘ P = P` 且 `P` 限制在临界线上为恒等. -/
def criticalLineProjection : ℂ → ℂ := fun z => criticalLineEmbed z.im

@[simp]
theorem criticalLineProjection_re (z : ℂ) : (criticalLineProjection z).re = 1 / 2 := rfl

@[simp]
theorem criticalLineProjection_im (z : ℂ) : (criticalLineProjection z).im = z.im := rfl

/-- 投影的复合形式: `P = γ ∘ Im`. -/
theorem criticalLineProjection_comp :
    criticalLineProjection = criticalLineEmbed ∘ Complex.im := rfl

/-- 投影是临界线的保核收缩: 临界线上的点是 P 的不动点. -/
theorem criticalLineProjection_eq_self {z : ℂ} (hz : z ∈ criticalLine) :
    criticalLineProjection z = z := by
  have hre : z.re = 1 / 2 := hz
  apply Complex.ext
  · rw [criticalLineProjection_re, hre]
  · exact criticalLineProjection_im z

theorem continuous_criticalLineProjection : Continuous criticalLineProjection :=
  continuous_criticalLineEmbed.comp Complex.continuous_im

theorem measurable_criticalLineProjection : Measurable criticalLineProjection :=
  continuous_criticalLineProjection.measurable

-- ============================================================
-- 2. 谱高度测度与谱化 RH (Hilbert-Pólya 测度影子)
-- ============================================================

/-- 谱高度测度 `μ_spec := Im_* μ_Z`: 非平凡零点虚部 (能级高度) 的分布.

    这是 Hilbert-Pólya 算子谱的测度影子: `μ_spec({t})` 是高度 t 处的
    能级简并度 (落在水平线 `Im s = t` 上的非平凡零点个数). -/
def spectralMeasure : Measure ℝ := Measure.map Complex.im zeroCountingMeasure

/-- 谱化 RH (Hilbert-Pólya 测度影子形式): 存在高度测度 μ 使零点计数测度
    完全由临界线嵌入重构: `μ_Z = γ_* μ`.

    直觉: 零点测度 " forgets" 临界线外的世界 —— 所有质量都来自
    某个高度谱经 γ 的搬运. -/
def spectralRH : Prop :=
  ∃ μ : Measure ℝ, zeroCountingMeasure = Measure.map criticalLineEmbed μ

/-- 谱高度测度的显式集合公式 (无条件): `μ_spec(A) = count {ρ ∈ 非平凡零点 : Im ρ ∈ A}`. -/
theorem spectralMeasure_apply {A : Set ℝ} (hA : MeasurableSet A) :
    spectralMeasure A = Measure.count (Complex.im ⁻¹' A ∩ nontrivialZeros) := by
  show (Measure.map Complex.im (Measure.count.restrict nontrivialZeros)) A
      = Measure.count (Complex.im ⁻¹' A ∩ nontrivialZeros)
  rw [Measure.map_apply Complex.measurable_im hA,
    Measure.restrict_apply' measurableSet_nontrivialZeros]

-- ============================================================
-- 3. 无条件的离散谱结构: 局部有限性与 σ-有限性
-- ============================================================

/-- 虚部预像的区间公式: `Im⁻¹' [-T, T] = {z : |Im z| ≤ T}` (横带). -/
theorem preimage_im_Icc (T : ℝ) :
    Complex.im ⁻¹' (Set.Icc (-T) T) = {z : ℂ | |z.im| ≤ T} := by
  ext z
  simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_setOf_eq, abs_le]

/-- 横带有限性 (无条件): 高度 `|Im| ≤ T` 的非平凡零点只有有限个.

    证明: 临界带内 `0 < Re < 1` 与 `|Im| ≤ T` 的交集含于闭球
    `‖z‖ ≤ |Re z| + |Im z| ≤ 1 + |T|`, 由紧集零点有限性得证.
    这是谱高度测度局部有限性的来源: 同一高度上的简并度有限. -/
theorem stripZeros_finite (T : ℝ) :
    (nontrivialZeros ∩ {z : ℂ | |z.im| ≤ T}).Finite := by
  have hsub : nontrivialZeros ∩ {z : ℂ | |z.im| ≤ T} ⊆ truncatedZeros (1 + |T|) := by
    rintro z ⟨hz, him⟩
    have hstrip : 0 < z.re ∧ z.re < 1 := hz.2
    refine ⟨hz, ?_⟩
    have hnorm : ‖z‖ ≤ 1 + |T| := by
      have h1 : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      have h2 : |z.re| < 1 := by
        rcases hstrip with ⟨hpos, hlt⟩
        rw [abs_lt]
        exact ⟨by linarith, by linarith⟩
      have him' : |z.im| ≤ T := him
      have h3 : |z.im| ≤ |T| := him'.trans (le_abs_self T)
      linarith
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hnorm
  exact (truncatedZeros_finite (1 + |T|)).subset hsub

/-- **局部有限性 (离散谱)** (无条件): 每个紧高度窗 `[-T, T]` 内能级有限.

    自伴算子紧预解式的谱论特征在零点高度谱上无条件成立;
    RH 的内容因此不在离散性本身, 而在 "离散谱承载全部零点测度". -/
theorem spectralMeasure_Icc_lt_top (T : ℝ) :
    spectralMeasure (Set.Icc (-T) T) < ∞ := by
  rw [spectralMeasure_apply measurableSet_Icc, preimage_im_Icc T]
  have hfin : ({z : ℂ | |z.im| ≤ T} ∩ nontrivialZeros).Finite := by
    have h := stripZeros_finite T
    rwa [Set.inter_comm] at h
  exact (Measure.count_apply_lt_top).mpr hfin

/-- 高度窗覆盖引理: `⋃ n : ℕ, [-n, n] = ℝ` (阿基米德性). -/
theorem iUnion_Icc_nat : (⋃ n : ℕ, Set.Icc (-(n : ℝ)) (n : ℝ)) = Set.univ := by
  refine Set.eq_univ_of_univ_subset ?_
  intro t _
  obtain ⟨n, hn⟩ := exists_nat_ge |t|
  exact Set.mem_iUnion.2 ⟨n, Set.mem_Icc.2 (abs_le.mp hn)⟩

instance sigmaFinite_spectralMeasure : SigmaFinite spectralMeasure :=
  ⟨⟨{ set := fun n : ℕ => Set.Icc (-(n : ℝ)) (n : ℝ)
      set_mem := fun _ => trivial
      finite := fun _ => spectralMeasure_Icc_lt_top _
      spanning := iUnion_Icc_nat }⟩⟩

-- ============================================================
-- 4. 节点 15: 谱化等价
-- ============================================================

/-- **节点 15 正向 (谱重构)**: RH ⟹ `γ_* μ_spec = μ_Z`.

    证明: 在 `μ_Z` 几乎处处 (即在每个非平凡零点处) `γ ∘ Im = id`
    (零点在临界线上 ⟹ `1/2 + Im(ρ)·i = ρ`), 由 `map_congr` 把推前复合
    坍缩为恒等推前. -/
theorem rh_imp_mapEmbed_spectralMeasure (hRH : riemannHypothesis) :
    Measure.map criticalLineEmbed spectralMeasure = zeroCountingMeasure := by
  show Measure.map criticalLineEmbed (Measure.map Complex.im
      (Measure.count.restrict nontrivialZeros)) = Measure.count.restrict nontrivialZeros
  rw [Measure.map_map measurable_criticalLineEmbed Complex.measurable_im]
  have hae : (criticalLineEmbed ∘ Complex.im)
      =ᵐ[Measure.count.restrict nontrivialZeros] (id : ℂ → ℂ) := by
    refine ae_restrict_of_forall_mem measurableSet_nontrivialZeros ?_
    intro z hz
    show criticalLineEmbed (Complex.im z) = z
    have hre : z.re = 1 / 2 := hRH hz
    apply Complex.ext
    · rw [criticalLineEmbed_re, hre]
    · exact criticalLineEmbed_im (Complex.im z)
  rw [Measure.map_congr hae, Measure.map_id]

/-- **节点 15 反向 (零测收缩)**: 谱化 RH ⟹ RH.

    证明: 若 `μ_Z = γ_* μ`, 则 `μ_Z(临界线ᶜ) = μ(γ⁻¹' 临界线ᶜ) = μ(∅) = 0`
    (γ 的像恒在临界线内, 预像为空), 由节点 3 的零测刻画得 RH. -/
theorem spectral_imp_rh (h : spectralRH) : riemannHypothesis := by
  obtain ⟨μ, hμ⟩ := h
  refine (rh_iff_zeroCountingMeasure_compl).mpr ?_
  rw [hμ, Measure.map_apply measurable_criticalLineEmbed measurableSet_criticalLine.compl]
  have hpre : criticalLineEmbed ⁻¹' criticalLineᶜ = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro t ht
    exact ht (criticalLineEmbed_re t)
  rw [hpre]
  simp

/-- **等价节点 15 (谱化等价)**: RH ⟺ 存在高度测度 μ 使 `μ_Z = γ_* μ`.

    这是 Hilbert-Pólya 纲领的测度论压缩: 零点计数测度完全由某个
    (不必显式构造的) 谱高度测度经临界线嵌入重构, 当且仅当 RH.
    [K3 语义标注, 2026-09-08] **等价重述 (definitional), 非 RH 证明** —
    本网络证明 RH 的各等价形式互推, 尚未证明 (也未否定) RH 本身;
    谱测度 μ 的存在性等价于 RH 本身, 未提供独立构造. -/
theorem rh_iff_spectral : riemannHypothesis ↔ spectralRH :=
  ⟨fun hRH => ⟨spectralMeasure, (rh_imp_mapEmbed_spectralMeasure hRH).symm⟩,
    spectral_imp_rh⟩

/-- **节点 15 强化 (离散谱形式)**: RH ⟺ 存在**局部有限**高度测度 μ
    使 `μ_Z = γ_* μ`.

    局部有限性 (`∀ T, μ([-T, T]) < ∞`) 是自伴算子紧预解式的谱论特征.
    正向用典范测度 `μ_spec` (其局部有限性无条件成立); 反向局部有限性
    并非必需 —— 裸存在性已蕴含 RH.
    [K3 语义标注, 2026-09-08] **等价重述 (definitional), 非 RH 证明** —
    本网络证明 RH 的各等价形式互推, 尚未证明 (也未否定) RH 本身. -/
theorem rh_iff_spectral_locallyFinite :
    riemannHypothesis ↔ ∃ μ : Measure ℝ,
      (∀ T : ℝ, μ (Set.Icc (-T) T) < ∞) ∧
      zeroCountingMeasure = Measure.map criticalLineEmbed μ := by
  constructor
  · intro hRH
    exact ⟨spectralMeasure, spectralMeasure_Icc_lt_top,
      (rh_imp_mapEmbed_spectralMeasure hRH).symm⟩
  · rintro ⟨μ, -, hμ⟩
    exact spectral_imp_rh ⟨μ, hμ⟩

-- ============================================================
-- 5. 节点 16: 典范唯一性
-- ============================================================

/-- **节点 16 强化 (无条件唯一性)**: 任何满足 `μ_Z = γ_* μ` 的高度测度 μ
    必为谱高度测度 `μ_spec = Im_* μ_Z` —— **不依赖 RH**.

    证明: `Im ∘ γ = id` ⟹ μ = id_* μ = (Im ∘ γ)_* μ = Im_* (γ_* μ)
    = Im_* μ_Z. 唯一性只用到临界线嵌入以虚部投影为左逆, 与 RH 真伪无关;
    RH 的作用 (节点 15) 仅在于保证这样的 μ 存在. -/
theorem spectral_measure_unique_of_spectral {μ : Measure ℝ}
    (hμ : zeroCountingMeasure = Measure.map criticalLineEmbed μ) :
    μ = spectralMeasure := by
  have hig : (Complex.im ∘ criticalLineEmbed) = (id : ℝ → ℝ) := funext fun _ => rfl
  have h1 : Measure.map Complex.im (Measure.map criticalLineEmbed μ) = μ := by
    rw [Measure.map_map Complex.measurable_im measurable_criticalLineEmbed, hig,
      Measure.map_id]
  calc μ = Measure.map Complex.im (Measure.map criticalLineEmbed μ) := h1.symm
    _ = Measure.map Complex.im zeroCountingMeasure := by rw [hμ]
    _ = spectralMeasure := rfl

/-- **等价节点 16 (典范唯一性)**: RH 下, 谱化测度必为谱高度测度
    `μ_spec = Im_* μ_Z`.

    证明: `Im ∘ γ = id` ⟹ μ = id_* μ = (Im ∘ γ)_* μ = Im_* (γ_* μ)
    = Im_* μ_Z. 谱化测度的唯一性是 `γ` 单射性 (以 Im 为左逆) 的直接
    推论: 能级位置决定高度, 无冗余参数. (证明本身不使用 RH 假设,
    见无条件强化版 `spectral_measure_unique_of_spectral`.) -/
theorem spectral_measure_unique (_hRH : riemannHypothesis) {μ : Measure ℝ}
    (hμ : zeroCountingMeasure = Measure.map criticalLineEmbed μ) :
    μ = spectralMeasure :=
  spectral_measure_unique_of_spectral hμ

-- ============================================================
-- 6. 节点 17: 投影不动点
-- ============================================================

/-- **节点 17 正向**: RH ⟹ `P_* μ_Z = μ_Z` (零点测度是投影的不动点).

    证明: `P = γ ∘ Im`, 由推前结合律 `P_* μ_Z = γ_* (Im_* μ_Z)
    = γ_* μ_spec`, 坍缩为节点 15 正向. -/
theorem rh_imp_projection_fixedPoint (hRH : riemannHypothesis) :
    Measure.map criticalLineProjection zeroCountingMeasure = zeroCountingMeasure := by
  have h1 : Measure.map criticalLineProjection zeroCountingMeasure
      = Measure.map criticalLineEmbed spectralMeasure := by
    show Measure.map criticalLineProjection zeroCountingMeasure
        = Measure.map criticalLineEmbed (Measure.map Complex.im zeroCountingMeasure)
    rw [criticalLineProjection_comp,
      ← Measure.map_map measurable_criticalLineEmbed Complex.measurable_im]
  rw [h1]
  exact rh_imp_mapEmbed_spectralMeasure hRH

/-- **节点 17 反向**: `P_* μ_Z = μ_Z` ⟹ RH.

    证明: `P(ℂ) ⊆ 临界线` ⟹ `μ_Z(临界线ᶜ) = (P_* μ_Z)(临界线ᶜ)
    = μ_Z(P⁻¹' 临界线ᶜ) = μ_Z(∅) = 0`, 由节点 3 的零测刻画得 RH. -/
theorem projection_fixedPoint_imp_rh
    (h : Measure.map criticalLineProjection zeroCountingMeasure = zeroCountingMeasure) :
    riemannHypothesis := by
  refine (rh_iff_zeroCountingMeasure_compl).mpr ?_
  rw [← h, Measure.map_apply measurable_criticalLineProjection measurableSet_criticalLine.compl]
  have hpre : criticalLineProjection ⁻¹' criticalLineᶜ = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z ht
    exact ht (criticalLineProjection_re z)
  rw [hpre]
  simp

/-- **等价节点 17 (投影不动点)**: RH ⟺ `P_* μ_Z = μ_Z`, 其中 `P = γ ∘ Im`
    是临界线的保核收缩.

    测度论解读: RH ⟺ 零点计数测度对临界线收缩算子不变 —— 把任何零点
    "拉回" 其临界线代表元不改变零点谱的测度结构. 偏线质量被 P 全部
    吸收进临界线, 不动性恰好排除这种吸收.
    [K3 语义标注, 2026-09-08] **等价重述 (definitional), 非 RH 证明** —
    本网络证明 RH 的各等价形式互推, 尚未证明 (也未否定) RH 本身. -/
theorem rh_iff_projection_fixedPoint :
    riemannHypothesis ↔
      Measure.map criticalLineProjection zeroCountingMeasure = zeroCountingMeasure :=
  ⟨rh_imp_projection_fixedPoint, projection_fixedPoint_imp_rh⟩

end RHSpectralMeasure
