import CddFormalization.RH_MeasureTheory
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Finset.Max

noncomputable section

/-! # Riemann Hypothesis: Li 判据形式化 (阶段 2a)

    本模块将 RH 等价网络扩展到 Li 判据 (Bombieri-Lagarias 1994) 维度:

        RH  ⟹  λₙ(R) ≥ 0  对所有 n 与截断 R        (节点 8, 正向, 无条件)
        BL 条件 + 对称假设 ⟹ RH                     (节点 9, 反向)

    其中截断 Li 系数定义为

        λₙ(R) = Σ_{ρ ∈ truncatedZeros R} Re[1 - (1 - 1/ρ)ⁿ].

    ## 正向的代数机制

    Li 判据正向方向的全部内容在代数层: 若 ρ 位于临界线, 则

        |1 - 1/ρ| = |ρ - 1| / |ρ| = 1    (Re ρ = 1/2 时分子分母相等),

    即 u(ρ) := 1 - 1/ρ 落在单位圆上. 单位圆上元素满足 Re[uⁿ] ≤ |u|ⁿ = 1,
    从而 Re[1 - uⁿ] = 1 - Re[uⁿ] ≥ 0 —— 临界线零点对 Li 系数的贡献逐项非负.

    ## 反向的辐角回归机制 (本模块核心贡献)

    反向方向需要: 若存在偏线零点 (Re ρ₀ < 1/2, 则 |u(ρ₀)| > 1),
    则某阶 λₙ < 0. 关键在于证明余弦序列 cos(n·arg u₀) 沿无界下标集
    回归到 1 的邻域:

    * 有理情形 (arg u₀ / 2π ∈ ℚ): 精确命中, n 取分母倍数;
    * 无理情形: 由 Mathlib 的 Dirichlet 无穷逼近
      (`Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational`)
      提取任意大分母逼近, 配合 |cos x| ≥ 1 - x²/2 给出回归.

    回归使 Re[u(ρ₀)ⁿ] ≥ (1-ε)|u(ρ₀)|ⁿ 指数增长; §多零点共振的处理
    中给出的同时回归版本进一步使**全体**项 Re[u(ρ)ⁿ] ≥ (1-ε)|u(ρ)|ⁿ,
    模长超过 1 的项指数增长支配常数项 |S|, 故有限和 Σ Re[1 - u(ρ)ⁿ]
    必然变负.

    ## 多零点共振的处理 (主导唯一假设的消除)

    完整 BL 定理的反向论证还需处理**多个同模偏线零点共振**的情形.
    本模块以**多维同时辐角回归** (`exists_simultaneous_cos_ge`,
    鸽笼 Dirichlet + 倍增) 直接处理该情形: 有限角族的余弦序列在
    同一无界下标集上同时回归到 1 的邻域, 使共振类全体
    Re[u(ρ)ⁿ] 同时取到指数下界, 模长最大项的指数增长支配常数项
    |S|. 因此节点 9 与 Li 等价主定理不再需要主导唯一性假设 `huniq`,
    仅保留零点对称 (函数方程实反射) 以 `hsym` 显式假设传入.

    References:
    - Bombieri & Lagarias (1994) Complements to Li's criterion
    - Li (1997) The positivity of a sequence related to Euler's constant
    - Mathlib.NumberTheory.DiophantineApproximation.Basic (Dirichlet 逼近)
    - RH_MeasureTheory.lean (截断零点基础设施)
-/

namespace RHLiCriterion

open RHMeasureTheory Complex Real Set Finset

-- ============================================================
-- 1. 幂增长与幂衰减的初等引理
-- ============================================================

/-- 幂增长: 底大于 1 的幂序列无界支配任意实数. -/
theorem exists_pow_gt_of_one_lt {a : ℝ} (ha : 1 < a) (x : ℝ) :
    ∃ n : ℕ, x < a ^ n := by
  have hpos : 0 < a - 1 := sub_pos.mpr ha
  obtain ⟨n, hn⟩ := exists_nat_gt ((x - 1) / (a - 1))
  refine ⟨n, ?_⟩
  have hbern : 1 + (n : ℝ) * (a - 1) ≤ (1 + (a - 1)) ^ n := by
    simpa using one_add_mul_le_pow (by linarith : -2 ≤ a - 1) n
  have heq : 1 + (a - 1) = a := by ring
  rw [heq] at hbern
  have h2 : x - 1 < (n : ℝ) * (a - 1) := by
    have h3 : (x - 1) / (a - 1) < (n : ℝ) := hn
    rwa [div_lt_iff₀ hpos] at h3
  linarith

/-- 幂衰减: 底在 [0,1) 的幂序列最终小于任意正数. -/
theorem exists_pow_le_delta_of_lt_one {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {δ : ℝ}
    (hδ : 0 < δ) : ∃ Q : ℕ, ∀ n : ℕ, Q ≤ n → a ^ n ≤ δ := by
  rcases eq_or_lt_of_le ha0 with rfl | hpos
  · refine ⟨1, fun n hn => ?_⟩
    rw [zero_pow (by omega : n ≠ 0)]
    exact hδ.le
  · have hinv : 1 < a⁻¹ := (one_lt_inv₀ hpos).mpr ha1
    obtain ⟨Q, hQ⟩ := exists_pow_gt_of_one_lt hinv δ⁻¹
    refine ⟨Q, fun n hn => ?_⟩
    have h1 : a ^ Q < δ := by
      have h2 : δ⁻¹ < (a⁻¹) ^ Q := hQ
      rw [inv_pow] at h2
      have hA : 0 < a ^ Q := pow_pos hpos Q
      exact (inv_lt_inv₀ hδ hA).mp h2
    exact le_of_lt (lt_of_le_of_lt (pow_le_pow_of_le_one hpos.le ha1.le hn) h1)

/-- 幂下界: 底大于 1 的幂序列最终超过任意常数. -/
theorem exists_pow_ge_const_of_one_lt {M : ℝ} (hM : 1 < M) (C : ℝ) :
    ∃ Q : ℕ, ∀ n : ℕ, Q ≤ n → C ≤ M ^ n := by
  obtain ⟨Q, hQ⟩ := exists_pow_gt_of_one_lt hM C
  refine ⟨Q, fun n hn => ?_⟩
  exact (le_of_lt hQ).trans (pow_le_pow_right₀ (le_of_lt hM) hn)

-- ============================================================
-- 2. Li 泛函代数层: 模长三分与单项非负
-- ============================================================

/-- normSq 恒等式: `|ρ-1|² - |ρ|² = 1 - 2·Re ρ`. -/
lemma normSq_sub_one_sub (ρ : ℂ) : (ρ - 1).normSq - ρ.normSq = 1 - 2 * ρ.re := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re, Complex.sub_im,
    Complex.one_im]
  ring

lemma norm_sq_eq_normSq (z : ℂ) : ‖z‖ ^ 2 = z.normSq := by
  have h : ‖z‖ ^ 2 = ‖z‖ * ‖z‖ := by ring
  rw [h, Complex.norm_mul_self_eq_normSq]

lemma norm_lt_norm_iff_normSq_lt (a b : ℂ) : ‖a‖ < ‖b‖ ↔ a.normSq < b.normSq := by
  rw [← norm_sq_eq_normSq a, ← norm_sq_eq_normSq b]
  constructor
  · intro h
    exact pow_lt_pow_left₀ h (norm_nonneg a) (by norm_num)
  · intro h
    rcases lt_or_ge (‖a‖) (‖b‖) with hlt | hge
    · exact hlt
    · exact absurd (pow_le_pow_left₀ (norm_nonneg b) hge 2) (by linarith)

lemma norm_eq_norm_iff_normSq_eq (a b : ℂ) : ‖a‖ = ‖b‖ ↔ a.normSq = b.normSq := by
  constructor
  · intro h
    rw [← norm_sq_eq_normSq, ← norm_sq_eq_normSq, h]
  · intro h
    have h2 : ‖a‖ ^ 2 = ‖b‖ ^ 2 := by
      rw [norm_sq_eq_normSq, norm_sq_eq_normSq, h]
    have habs : |‖a‖| = |‖b‖| := (sq_eq_sq_iff_abs_eq_abs ‖a‖ ‖b‖).mp h2
    rwa [abs_of_nonneg (norm_nonneg a), abs_of_nonneg (norm_nonneg b)] at habs

/-- 核心代数引理: `|1 - 1/ρ| = |ρ - 1| / |ρ|` (ρ ≠ 0). -/
lemma norm_one_sub_inv_div {ρ : ℂ} (hρ : ρ ≠ 0) :
    ‖(1 : ℂ) - ρ⁻¹‖ = ‖ρ - 1‖ / ‖ρ‖ := by
  have hkey : ((1 : ℂ) - ρ⁻¹) = (ρ - 1) * ρ⁻¹ := by field_simp
  rw [hkey, norm_mul, norm_inv, mul_comm, div_eq_inv_mul]

/-- **模长三分 (代数层核心)**: 临界线零点对应单位模.

    `Re ρ = 1/2 ⟹ |1 - 1/ρ| = 1`: 此时 |ρ-1| = |ρ|
    (关于临界线的左右对称), 即 Li 泛函的相位因子落在单位圆上. -/
theorem norm_one_sub_inv_eq_one {ρ : ℂ} (hre : ρ.re = 1 / 2) (hρ : ρ ≠ 0) :
    ‖(1 : ℂ) - ρ⁻¹‖ = 1 := by
  rw [norm_one_sub_inv_div hρ]
  have hns : (ρ - 1).normSq = ρ.normSq := by
    have h := normSq_sub_one_sub ρ
    rw [hre] at h
    have h0 : 1 - 2 * (1 / 2 : ℝ) = 0 := by ring
    rw [h0] at h
    linarith
  rw [(norm_eq_norm_iff_normSq_eq _ _).mpr hns,
    div_self (norm_ne_zero_iff.mpr hρ)]

/-- 模长三分: 临界线右侧零点对应模严格小于 1. -/
theorem norm_one_sub_inv_lt_one {ρ : ℂ} (hre : 1 / 2 < ρ.re) (hρ : ρ ≠ 0) :
    ‖(1 : ℂ) - ρ⁻¹‖ < 1 := by
  rw [norm_one_sub_inv_div hρ, div_lt_iff₀ (norm_pos_iff.mpr hρ), one_mul]
  have hns : (ρ - 1).normSq < ρ.normSq := by
    have h := normSq_sub_one_sub ρ
    linarith
  exact (norm_lt_norm_iff_normSq_lt (ρ - 1) ρ).mpr hns

/-- 模长三分: 临界线左侧零点对应模严格大于 1.

    这是反向论证的入口: Re ρ < 1/2 的零点使 Li 相位因子
    落在单位圆外, 其幂序列指数发散. -/
theorem norm_one_sub_inv_gt_one {ρ : ℂ} (hre : ρ.re < 1 / 2) (hρ : ρ ≠ 0) :
    1 < ‖(1 : ℂ) - ρ⁻¹‖ := by
  rw [norm_one_sub_inv_div hρ, lt_div_iff₀ (norm_pos_iff.mpr hρ), one_mul]
  have hns : ρ.normSq < (ρ - 1).normSq := by
    have h := normSq_sub_one_sub ρ
    have h2 : 0 < 1 - 2 * ρ.re := by linarith
    linarith
  exact (norm_lt_norm_iff_normSq_lt ρ (ρ - 1)).mpr hns

/-- **临界线单项非负性**: 单位模元素的 Li 泛函单项实部非负.

    |u| = 1 ⟹ Re[uⁿ] ≤ |u|ⁿ = 1 ⟹ Re[1 - uⁿ] ≥ 0.
    正向方向 (节点 8) 的全部内容. -/
theorem re_one_sub_pow_nonneg {u : ℂ} (hu : ‖u‖ = 1) (n : ℕ) :
    0 ≤ (1 - u ^ n).re := by
  have h1 : (u ^ n).re ≤ ‖u ^ n‖ := le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
  have h2 : ‖u ^ n‖ = ‖u‖ ^ n := Complex.norm_pow u n
  rw [hu, one_pow] at h2
  have hre : (1 - u ^ n).re = 1 - (u ^ n).re := by
    simp [Complex.sub_re]
  rw [hre]
  linarith

-- ============================================================
-- 3. 截断 Li 系数与正向节点
-- ============================================================

/-- Li 泛函单项: `liTerm ρ n = Re[1 - (1 - 1/ρ)ⁿ]`. -/
def liTerm (ρ : ℂ) (n : ℕ) : ℝ := (1 - (1 - ρ⁻¹) ^ n).re

/-- 截断 Li 系数: `λₙ(R) = Σ_{ρ ∈ truncatedZeros R} Re[1 - (1 - 1/ρ)ⁿ]`.

    截断零点集有限 (`truncatedZeros_finite`), 求和无歧义. 标准非截断
    Li 系数为 R → ∞ 的形式极限 (条件收敛); 截断版本保留了 BL 定理
    的全部代数机制且避免收敛性负担. -/
def liCoeffTrunc (n : ℕ) (R : ℝ) : ℝ :=
  ∑ ρ ∈ (truncatedZeros_finite R).toFinset, liTerm ρ n

/-- 非平凡零点非零 (实部严格为正). -/
lemma nontrivial_zero_ne_zero {ρ : ℂ} (hρ : ρ ∈ nontrivialZeros) : ρ ≠ 0 := by
  intro h
  rw [h] at hρ
  exact absurd hρ.2.1 (by simp)

/-- **节点 8 (正向, 无条件)**: RH ⟹ 所有截断 Li 系数非负.

    临界线零点逐项贡献 Re[1 - (1-1/ρ)ⁿ] ≥ 0 (单位模单项非负性),
    有限和保持非负. 这是 Li 判据正向方向 (RH ⟹ λₙ ≥ 0) 的完整
    形式化. -/
theorem rh_imp_liCoeffTrunc_nonneg (hRH : riemannHypothesis) (n : ℕ) (R : ℝ) :
    0 ≤ liCoeffTrunc n R := by
  unfold liCoeffTrunc liTerm
  refine Finset.sum_nonneg fun ρ hρ => ?_
  have hmem : ρ ∈ truncatedZeros R := (truncatedZeros_finite R).mem_toFinset.mp hρ
  have hre : ρ.re = 1 / 2 := hRH hmem.1
  have hρ0 : ρ ≠ 0 := nontrivial_zero_ne_zero hmem.1
  exact re_one_sub_pow_nonneg (norm_one_sub_inv_eq_one hre hρ0) n

-- ============================================================
-- 4. 辐角回归定理 (Dirichlet 逼近驱动)
-- ============================================================

/-- 余弦下方界: `cos x ≥ 1 - x²/2`. -/
lemma cos_ge_one_sub_half_sq (x : ℝ) : 1 - x ^ 2 / 2 ≤ Real.cos x :=
  Real.one_sub_sq_div_two_le_cos

/-- 无理数的 Dirichlet 逼近具有任意大分母.

    由逼近集无限 (`Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational`)
    反证: 若分母有界, 则逼近被 absorbed 到有限个分母纤维, 每个纤维
    落在有界整数区间故有限. -/
theorem exists_large_den_approx {α : ℝ} (hα : Irrational α) (Q : ℕ) :
    ∃ q : ℚ, Q < q.den ∧ |α - q| < 1 / (q.den : ℝ) ^ 2 := by
  by_contra hcon
  rw [not_exists] at hcon
  have hSinf : {q : ℚ | |α - q| < 1 / (q.den : ℝ) ^ 2}.Infinite :=
    Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hα
  have hSfin : {q : ℚ | |α - q| < 1 / (q.den : ℝ) ^ 2}.Finite := by
    have hsub : {q : ℚ | |α - q| < 1 / (q.den : ℝ) ^ 2} ⊆
        ⋃ d ∈ Set.Icc (1 : ℕ) Q, {q : ℚ | q.den = d ∧ |α - q| < 1 / (q.den : ℝ) ^ 2} := by
      intro q hq
      have hq' : |α - q| < 1 / (q.den : ℝ) ^ 2 := hq
      have hd : q.den ≤ Q := by
        by_contra hd'
        exact hcon q ⟨by omega, hq'⟩
      exact Set.mem_iUnion₂.mpr ⟨q.den, ⟨q.pos, hd⟩, ⟨rfl, hq'⟩⟩
    refine Set.Finite.subset ?_ hsub
    refine Set.Finite.biUnion (Set.finite_Icc 1 Q) ?_
    intro d hdIcc
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hdIcc.1
    have hd0 : (0 : ℝ) < d := by linarith
    have hdne : (d : ℝ) ≠ 0 := ne_of_gt hd0
    have hfib : {q : ℚ | q.den = d ∧ |α - q| < 1 / (q.den : ℝ) ^ 2} ⊆
        (fun n : ℤ => (n : ℚ) / (d : ℚ)) '' {n : ℤ | |α * (d : ℝ) - (n : ℝ)| < 1} := by
      intro q hq
      obtain ⟨hden, hq2⟩ := hq
      have happ : |α - q| < 1 / (d : ℝ) ^ 2 := by rwa [hden] at hq2
      have hqc : (q : ℝ) = (q.num : ℝ) / (d : ℝ) := by
        rw [← hden]
        exact Rat.cast_def q
      rw [hqc] at happ
      refine ⟨q.num, ?_, ?_⟩
      · show |α * (d : ℝ) - (q.num : ℝ)| < 1
        have hEq : (α - (q.num : ℝ) / (d : ℝ)) * (d : ℝ) =
            α * (d : ℝ) - (q.num : ℝ) := by
          rw [sub_mul, div_mul_cancel₀ (q.num : ℝ) hdne]
        rw [← hEq, abs_mul, abs_of_pos hd0]
        have h1 : (d : ℝ) * |α - (q.num : ℝ) / (d : ℝ)| <
            (d : ℝ) * (1 / (d : ℝ) ^ 2) :=
          mul_lt_mul_of_pos_left happ hd0
        have h2 : (d : ℝ) * (1 / (d : ℝ) ^ 2) = 1 / (d : ℝ) := by
          field_simp
        rw [h2] at h1
        have h3 : 1 / (d : ℝ) ≤ 1 := by
          rw [div_le_iff₀ hd0]
          linarith
        linarith
      · rw [← hden]
        exact Rat.num_div_den q
    refine Set.Finite.subset (Set.Finite.image _ ?_) hfib
    have hint : {n : ℤ | |α * (d : ℝ) - (n : ℝ)| < 1} ⊆
        Set.Icc (Int.floor (α * (d : ℝ))) (Int.floor (α * (d : ℝ)) + 1) := by
      intro n hn
      have hn' : |α * (d : ℝ) - (n : ℝ)| < 1 := hn
      rw [abs_lt] at hn'
      have hn1 : Int.floor (α * (d : ℝ)) ≤ n := by
        have h1 : (Int.floor (α * (d : ℝ)) : ℝ) < (n : ℝ) + 1 := by
          have hf := Int.floor_le (α * (d : ℝ))
          linarith
        have h2 : (Int.floor (α * (d : ℝ)) : ℤ) < n + 1 := by exact_mod_cast h1
        exact Int.lt_add_one_iff.mp h2
      have hn2 : n ≤ Int.floor (α * (d : ℝ)) + 1 := by
        have h1 : (n : ℝ) < (Int.floor (α * (d : ℝ)) : ℝ) + 2 := by
          have hf := Int.lt_floor_add_one (α * (d : ℝ))
          linarith
        have h2 : n < Int.floor (α * (d : ℝ)) + 2 := by exact_mod_cast h1
        omega
      exact ⟨hn1, hn2⟩
    exact Set.Finite.subset (Set.finite_Icc _ _) hint
  exact hSinf hSfin

/-- **辐角回归定理 (无条件)**: 对任意角 θ 与 ε > 0, 存在任意大的 n
    使 `cos(nθ) ≥ 1 - ε`.

    这是 BL 反向论证的辐角回归核心:
    * 有理情形 θ/(2π) ∈ ℚ: 分母倍数下标精确命中 cos = 1;
    * 无理情形: Dirichlet 大分母逼近 (上一引理) 配合
      `cos x ≥ 1 - x²/2` 给出回归.

    两种情形合并为对**任意** θ 的无条件陈述. -/
theorem exists_ge_cos_ge {θ : ℝ} {ε : ℝ} (hε : 0 < ε) (Q : ℕ) :
    ∃ n : ℕ, Q ≤ n ∧ 1 - ε ≤ Real.cos ((n : ℝ) * θ) := by
  by_cases hrat : Irrational (θ / (2 * Real.pi))
  case pos =>
    -- 无理情形: Dirichlet 大分母逼近 + 余弦下方界
    obtain ⟨N₁, hN₁⟩ := exists_nat_gt (Real.pi * Real.sqrt (2 / ε))
    have hN₁pos : 0 < N₁ := by
      have h0 : (0 : ℝ) < Real.pi * Real.sqrt (2 / ε) :=
        mul_pos Real.pi_pos (Real.sqrt_pos.mpr (div_pos two_pos hε))
      exact_mod_cast h0.trans hN₁
    have hkey : ∀ n : ℕ, N₁ ≤ n → 2 * Real.pi ^ 2 / (n : ℝ) ^ 2 < ε := by
      intro n hn
      have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (hN₁pos.trans_le hn)
      have hn2 : (N₁ : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by exact_mod_cast hN₁pos.le) (by exact_mod_cast hn) 2
      have hcore : 2 * Real.pi ^ 2 < ε * (N₁ : ℝ) ^ 2 := by
        have hsq : (Real.pi * Real.sqrt (2 / ε)) ^ 2 < (N₁ : ℝ) ^ 2 :=
          pow_lt_pow_left₀ hN₁ (by positivity) (by norm_num)
        have hsqeq : (Real.pi * Real.sqrt (2 / ε)) ^ 2 = Real.pi ^ 2 * (2 / ε) := by
          rw [mul_pow, Real.sq_sqrt (by positivity)]
        have hineq : Real.pi ^ 2 * (2 / ε) < (N₁ : ℝ) ^ 2 := by rwa [hsqeq] at hsq
        have hmul : Real.pi ^ 2 * (2 / ε) * ε = 2 * Real.pi ^ 2 := by
          rw [mul_assoc, div_mul_cancel₀ _ (ne_of_gt hε)]
          ring
        nlinarith [hineq, hε]
      rw [div_lt_iff₀ (pow_pos hn' 2)]
      nlinarith [hcore, hn2]
    obtain ⟨q, hden, happ⟩ := exists_large_den_approx hrat (max N₁ (Q + 1))
    refine ⟨q.den, by omega, ?_⟩
    have hnpos : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.pos
    have hdne : ((q.den : ℕ) : ℝ) ≠ 0 := by exact_mod_cast q.pos.ne'
    have hqc : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := Rat.cast_def q
    have hstep : (q.den : ℝ) * |θ / (2 * Real.pi) - q| =
        |(q.den : ℝ) * (θ / (2 * Real.pi)) - (q.num : ℝ)| := by
      rw [hqc]
      have hEq : (q.den : ℝ) * (θ / (2 * Real.pi) - (q.num : ℝ) / (q.den : ℝ)) =
          (q.den : ℝ) * (θ / (2 * Real.pi)) - (q.num : ℝ) := by
        rw [mul_sub, mul_div_cancel₀ (q.num : ℝ) hdne]
      calc (q.den : ℝ) * |θ / (2 * Real.pi) - (q.num : ℝ) / (q.den : ℝ)| =
          |(q.den : ℝ) * (θ / (2 * Real.pi) - (q.num : ℝ) / (q.den : ℝ))| := by
            rw [abs_mul, abs_of_pos hnpos]
        _ = |(q.den : ℝ) * (θ / (2 * Real.pi)) - (q.num : ℝ)| := by rw [hEq]
    have hlt : |(q.den : ℝ) * (θ / (2 * Real.pi)) - (q.num : ℝ)| <
        1 / (q.den : ℝ) := by
      rw [← hstep]
      have h1 : (q.den : ℝ) * |θ / (2 * Real.pi) - q| <
          (q.den : ℝ) * (1 / (q.den : ℝ) ^ 2) :=
        mul_lt_mul_of_pos_left happ hnpos
      have h2 : (q.den : ℝ) * (1 / (q.den : ℝ) ^ 2) = 1 / (q.den : ℝ) := by
        field_simp
      rw [h2] at h1
      exact h1
    have hnθ : (q.den : ℝ) * θ = 2 * Real.pi *
        ((q.den : ℝ) * (θ / (2 * Real.pi)) - (q.num : ℝ)) + (q.num : ℝ) * (2 * Real.pi) := by
      have hEq : (q.den : ℝ) * (θ / (2 * Real.pi)) = ((q.den : ℝ) * θ) / (2 * Real.pi) :=
        mul_div_assoc' _ _ _
      rw [hEq, mul_sub, mul_div_cancel₀ _ (by positivity : (2 : ℝ) * Real.pi ≠ 0)]
      ring
    have hper : Real.cos (2 * Real.pi *
        ((q.den : ℝ) * (θ / (2 * Real.pi)) - (q.num : ℝ)) + (q.num : ℝ) * (2 * Real.pi)) =
        Real.cos (2 * Real.pi *
        ((q.den : ℝ) * (θ / (2 * Real.pi)) - (q.num : ℝ))) :=
      Real.cos_periodic.int_mul (q.num : ℤ)
        (2 * Real.pi * ((q.den : ℝ) * (θ / (2 * Real.pi)) - (q.num : ℝ)))
    rw [hnθ, hper]
    have hpd : 0 < 2 * Real.pi / (q.den : ℝ) := div_pos (by positivity) hnpos
    have habs1 : |2 * Real.pi * ((q.den : ℝ) * (θ / (2 * Real.pi)) - (q.num : ℝ))| =
        2 * Real.pi * |(q.den : ℝ) * (θ / (2 * Real.pi)) - (q.num : ℝ)| := by
      rw [abs_mul, abs_of_pos (by positivity)]
    have habsZ : 2 * Real.pi * |(q.den : ℝ) * (θ / (2 * Real.pi)) - (q.num : ℝ)| ≤
        2 * Real.pi / (q.den : ℝ) := by
      have h2 : 2 * Real.pi * (1 / (q.den : ℝ)) = 2 * Real.pi / (q.den : ℝ) := by ring
      rw [← h2]
      exact mul_le_mul_of_nonneg_left (le_of_lt hlt) (by positivity)
    have hbound : 1 - (2 * Real.pi / (q.den : ℝ)) ^ 2 / 2 ≤
        Real.cos (2 * Real.pi * ((q.den : ℝ) * (θ / (2 * Real.pi)) - (q.num : ℝ))) := by
      have h1 := cos_ge_one_sub_half_sq
        (2 * Real.pi * ((q.den : ℝ) * (θ / (2 * Real.pi)) - (q.num : ℝ)))
      have h2 : (2 * Real.pi * ((q.den : ℝ) * (θ / (2 * Real.pi)) - (q.num : ℝ))) ^ 2 ≤
          (2 * Real.pi / (q.den : ℝ)) ^ 2 := by
        refine (sq_le_sq).mpr ?_
        rw [habs1, abs_of_pos hpd]
        exact habsZ
      linarith
    have hconv : (2 * Real.pi / (q.den : ℝ)) ^ 2 / 2 = 2 * Real.pi ^ 2 / (q.den : ℝ) ^ 2 := by
      ring
    rw [hconv] at hbound
    have hn1 : 2 * Real.pi ^ 2 / (q.den : ℝ) ^ 2 < ε := by
      refine hkey q.den ?_
      exact le_trans (le_max_left _ _) (le_of_lt hden)
    linarith
  case neg =>
    -- 有理情形: 分母倍数下标精确命中 cos = 1
    obtain ⟨q, hq⟩ := exists_rat_of_not_irrational hrat
    have hdne : ((q.den : ℕ) : ℝ) ≠ 0 := by exact_mod_cast q.pos.ne'
    have hqc : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := Rat.cast_def q
    refine ⟨q.den * (Q + 1), ?_, ?_⟩
    · exact ((Nat.lt_succ_self Q).trans_le (Nat.le_mul_of_pos_left (Q + 1) q.pos)).le
    · have hθ : θ = 2 * Real.pi * (q : ℝ) := by
        have h1 := (div_eq_iff (by positivity : (2 : ℝ) * Real.pi ≠ 0)).mp hq
        linarith
      have hdθ : ((q.den : ℕ) : ℝ) * θ = 2 * Real.pi * (q.num : ℝ) := by
        rw [hθ, hqc]
        field_simp
      have hval : ((q.den * (Q + 1) : ℕ) : ℝ) * θ =
          (((Q + 1) * q.num : ℤ) : ℝ) * (2 * Real.pi) := by
        rw [Nat.cast_mul, mul_right_comm, hdθ]
        push_cast
        ring
      rw [hval, Real.cos_int_mul_two_pi]
      linarith

-- ============================================================
-- 4b. 多维同时辐角回归 (鸽笼 Dirichlet + 倍增)
-- ============================================================

/-- 鸽笼格子引理: `⌊N·fract x⌋` 落入 `[0, N)` 内. -/
private lemma floor_mul_fract_lt {N : ℕ} (hN : 0 < N) (x : ℝ) :
    (Int.floor ((N : ℝ) * Int.fract x)).toNat < N := by
  have hnn : 0 ≤ (N : ℝ) * Int.fract x :=
    mul_nonneg (by positivity) (Int.fract_nonneg x)
  have h1 : 0 ≤ Int.floor ((N : ℝ) * Int.fract x) := Int.floor_nonneg.mpr hnn
  have h2 : Int.floor ((N : ℝ) * Int.fract x) < (N : ℤ) := by
    rw [Int.floor_lt]
    have hfr1 : Int.fract x < 1 := Int.fract_lt_one x
    have hlt : (N : ℝ) * Int.fract x < (N : ℝ) := by
      have hc : (N : ℝ) * Int.fract x < (N : ℝ) * 1 :=
        mul_lt_mul_of_pos_left hfr1 (by exact_mod_cast hN)
      linarith
    exact_mod_cast hlt
  exact (Int.toNat_lt h1).mpr h2

/-- **多维同时辐角回归 (鸽笼 Dirichlet + 倍增)**: 对任意有限角族 `θ : ι → ℝ`,
    任意 `ε > 0` 与任意下界 `Q`, 存在 `n ≥ Q` 使所有
    `cos (n·θ j) ≥ 1 - ε`.

    这是单零点辐角回归 `exists_ge_cos_ge` 到**共振类**的推广, BL 反向
    论证处理多零点同模共振的核心. 机制:
    * 鸽笼: `N^m + 1` 个点 `({k·α j} mod 1)_{j}` (`k ≤ N^m`) 落入
      `N^m` 个边长 `1/N` 的格子, 碰撞给出 `0 < n₀` 使所有
      `n₀·α j` 距整数 `< 1/N`;
    * 倍增: `n = (Q+1)·n₀` 把误差放大至多 `(Q+1)/N < δ`
      (N 由 `exists_nat_gt` 取得);
    * `cos ≥ 1 - x²/2` 与 `δ² = ε/(2π²)` 完成组装. -/
theorem exists_simultaneous_cos_ge {ι : Type*} [Fintype ι] (θ : ι → ℝ)
    {ε : ℝ} (hε : 0 < ε) (Q : ℕ) :
    ∃ n : ℕ, Q ≤ n ∧ ∀ j, 1 - ε ≤ Real.cos ((n : ℝ) * θ j) := by
  classical
  set δ : ℝ := Real.sqrt (ε / (2 * Real.pi ^ 2)) with hδdef
  have hδpos : 0 < δ := Real.sqrt_pos.mpr (by positivity)
  set m := Fintype.card ι with hm
  obtain ⟨N, hNbig⟩ : ∃ N : ℕ, ((Q : ℝ) + 1) / δ < (N : ℝ) := exists_nat_gt _
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_le_of_lt (by positivity) hNbig
  have hNnat : 0 < N := by exact_mod_cast hNpos
  have hQN : ((Q : ℝ) + 1) / (N : ℝ) < δ := by
    rw [div_lt_iff₀ hNpos]
    have h1 : ((Q : ℝ) + 1) < (N : ℝ) * δ := (div_lt_iff₀ hδpos).mp hNbig
    linarith [mul_comm ((N : ℝ)) δ]
  -- 鸽笼映射: k ↦ (j ↦ ⌊N·{k·α j}⌋)
  set α : ι → ℝ := fun j => θ j / (2 * Real.pi) with hαdef
  set f : Fin (N ^ m + 1) → (ι → Fin N) :=
    fun k j => ⟨(Int.floor ((N : ℝ) * Int.fract ((k : ℝ) * α j))).toNat,
      floor_mul_fract_lt (by omega) ((k : ℝ) * α j)⟩ with hfdef
  have hcard : Fintype.card (ι → Fin N) < Fintype.card (Fin (N ^ m + 1)) := by
    rw [Fintype.card_pi, Fintype.card_fin, Fintype.card_fin]
    have h1 : ∏ _i : ι, N = N ^ m := by simp [← hm]
    rw [h1]
    exact Nat.lt_succ_self _
  obtain ⟨k₁, k₂, hne, hfe⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  -- 碰撞给出: 同格子 ⟹ floor 值相等
  have hfloor_eq : ∀ j, Int.floor ((N : ℝ) * Int.fract ((k₁ : ℝ) * α j)) =
      Int.floor ((N : ℝ) * Int.fract ((k₂ : ℝ) * α j)) := by
    intro j
    have hfj : f k₁ j = f k₂ j := congrFun hfe j
    have h2 : (Int.floor ((N : ℝ) * Int.fract ((k₁ : ℝ) * α j))).toNat =
        (Int.floor ((N : ℝ) * Int.fract ((k₂ : ℝ) * α j))).toNat := congrArg Fin.val hfj
    have h3 : 0 ≤ Int.floor ((N : ℝ) * Int.fract ((k₁ : ℝ) * α j)) :=
      Int.floor_nonneg.mpr (mul_nonneg (by positivity) (Int.fract_nonneg _))
    have h4 : 0 ≤ Int.floor ((N : ℝ) * Int.fract ((k₂ : ℝ) * α j)) :=
      Int.floor_nonneg.mpr (mul_nonneg (by positivity) (Int.fract_nonneg _))
    rw [← Int.toNat_of_nonneg h3, ← Int.toNat_of_nonneg h4]
    exact_mod_cast h2
  -- 同格子 ⟹ fract 差 < 1/N
  have hfrlt : ∀ j, |Int.fract ((k₁ : ℝ) * α j) - Int.fract ((k₂ : ℝ) * α j)| < 1 / (N : ℝ) := by
    intro j
    have hp := hfloor_eq j
    set x₁ : ℝ := (N : ℝ) * Int.fract ((k₁ : ℝ) * α j) with hx₁def
    set x₂ : ℝ := (N : ℝ) * Int.fract ((k₂ : ℝ) * α j) with hx₂def
    have h1 : ((Int.floor x₁ : ℤ) : ℝ) ≤ x₁ := Int.floor_le x₁
    have h2 : ((Int.floor x₂ : ℤ) : ℝ) ≤ x₂ := Int.floor_le x₂
    have h3 : x₁ < ((Int.floor x₁ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one x₁
    have h4 : x₂ < ((Int.floor x₂ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one x₂
    rw [← hp] at h2 h4
    have habs : |x₁ - x₂| < 1 := by
      rw [abs_sub_lt_iff]
      constructor <;> linarith
    have hmul : x₁ - x₂ = (N : ℝ) *
        (Int.fract ((k₁ : ℝ) * α j) - Int.fract ((k₂ : ℝ) * α j)) := by
      rw [hx₁def, hx₂def]; ring
    have habs2 : |x₁ - x₂| = (N : ℝ) *
        |Int.fract ((k₁ : ℝ) * α j) - Int.fract ((k₂ : ℝ) * α j)| := by
      rw [hmul, abs_mul, abs_of_pos hNpos]
    have hkey : |x₁ - x₂| / (N : ℝ) =
        |Int.fract ((k₁ : ℝ) * α j) - Int.fract ((k₂ : ℝ) * α j)| := by
      rw [habs2, mul_div_cancel_left₀ _ hNpos.ne']
    rw [← hkey]
    exact div_lt_div_of_pos_right habs hNpos
  -- 倍增基: n₀ 与整数部分 z (两个顺序分支对称)
  have hpigeon : ∃ n₀ : ℕ, 0 < n₀ ∧ ∃ z : ι → ℤ,
      ∀ j, |(n₀ : ℝ) * α j - ((z j : ℝ))| < 1 / (N : ℝ) := by
    rcases Nat.lt_or_ge k₁.val k₂.val with hlt | hge
    · refine ⟨k₂.val - k₁.val, by omega,
        fun j => ⌊(k₂ : ℝ) * α j⌋ - ⌊(k₁ : ℝ) * α j⌋, fun j => ?_⟩
      have h1 := hfrlt j
      rw [abs_sub_comm] at h1
      have hEq : ((k₂ : ℝ) - (k₁ : ℝ)) * α j -
          (((⌊(k₂ : ℝ) * α j⌋ - ⌊(k₁ : ℝ) * α j⌋ : ℤ) : ℝ)) =
          Int.fract ((k₂ : ℝ) * α j) - Int.fract ((k₁ : ℝ) * α j) := by
        rw [← Int.self_sub_floor, ← Int.self_sub_floor]
        push_cast
        ring
      rw [Nat.cast_sub hlt.le, hEq]
      exact h1
    · have hlt' : k₂.val < k₁.val :=
        Nat.lt_of_le_of_ne hge (fun h => hne ((Fin.val_eq_val _ _).mp h).symm)
      refine ⟨k₁.val - k₂.val, by omega,
        fun j => ⌊(k₁ : ℝ) * α j⌋ - ⌊(k₂ : ℝ) * α j⌋, fun j => ?_⟩
      have h1 := hfrlt j
      have hEq : ((k₁ : ℝ) - (k₂ : ℝ)) * α j -
          (((⌊(k₁ : ℝ) * α j⌋ - ⌊(k₂ : ℝ) * α j⌋ : ℤ) : ℝ)) =
          Int.fract ((k₁ : ℝ) * α j) - Int.fract ((k₂ : ℝ) * α j) := by
        rw [← Int.self_sub_floor, ← Int.self_sub_floor]
        push_cast
        ring
      rw [Nat.cast_sub hlt'.le, hEq]
      exact h1
  obtain ⟨n₀, hn₀pos, z, hz⟩ := hpigeon
  -- 倍增: n = (Q+1)·n₀
  have hkn₀ : Q + 1 ≤ (Q + 1) * n₀ := Nat.le_mul_of_pos_right _ hn₀pos
  have herr : ∀ j, |((((Q + 1) * n₀ : ℕ) : ℝ) * α j - ((((Q + 1) * z j : ℤ) : ℝ)))| < δ := by
    intro j
    have hzj := hz j
    have hcalc : ((((Q + 1) * n₀ : ℕ) : ℝ) * α j - ((((Q + 1) * z j : ℤ) : ℝ))) =
        ((Q + 1 : ℕ) : ℝ) * ((n₀ : ℝ) * α j - ((z j : ℝ))) := by
      push_cast
      ring
    rw [hcalc, abs_mul, abs_of_nonneg (by positivity)]
    have h1 : ((Q + 1 : ℕ) : ℝ) * |(n₀ : ℝ) * α j - ((z j : ℝ))| <
        ((Q + 1 : ℕ) : ℝ) * (1 / (N : ℝ)) :=
      mul_lt_mul_of_pos_left hzj (by positivity)
    have h2 : ((Q + 1 : ℕ) : ℝ) * (1 / (N : ℝ)) = ((Q : ℝ) + 1) / (N : ℝ) := by
      push_cast
      rw [mul_one_div]
    rw [h2] at h1
    exact lt_trans h1 hQN
  refine ⟨(Q + 1) * n₀, Nat.le_of_succ_le hkn₀, fun j => ?_⟩
  have hθα : (((Q + 1) * n₀ : ℕ) : ℝ) * θ j =
      2 * Real.pi * ((((Q + 1) * n₀ : ℕ) : ℝ) * α j) := by
    rw [hαdef]
    field_simp
  have hsplit : (((Q + 1) * n₀ : ℕ) : ℝ) * θ j =
      (2 * Real.pi * ((((Q + 1) * n₀ : ℕ) : ℝ) * α j - ((((Q + 1) * z j : ℤ) : ℝ)))) +
      ((((Q + 1) * z j : ℤ) : ℝ)) * (2 * Real.pi) := by
    rw [hθα]
    ring
  rw [hsplit, Real.cos_add_int_mul_two_pi]
  have heabs := herr j
  have hcosb := cos_ge_one_sub_half_sq
    (2 * Real.pi * ((((Q + 1) * n₀ : ℕ) : ℝ) * α j - ((((Q + 1) * z j : ℤ) : ℝ))))
  have hsq : (2 * Real.pi * ((((Q + 1) * n₀ : ℕ) : ℝ) * α j - ((((Q + 1) * z j : ℤ) : ℝ)))) ^ 2 ≤
      (2 * Real.pi * δ) ^ 2 := by
    refine sq_le_sq.mpr ?_
    have hL : |2 * Real.pi * ((((Q + 1) * n₀ : ℕ) : ℝ) * α j - ((((Q + 1) * z j : ℤ) : ℝ)))| =
        2 * Real.pi * |((((Q + 1) * n₀ : ℕ) : ℝ) * α j - ((((Q + 1) * z j : ℤ) : ℝ)))| := by
      rw [abs_mul, abs_of_pos (by positivity)]
    have hR : |2 * Real.pi * δ| = 2 * Real.pi * δ := by
      rw [abs_mul, abs_of_pos (by positivity), abs_of_pos hδpos]
    rw [hL, hR]
    exact mul_le_mul_of_nonneg_left heabs.le (by positivity)
  have hdelta : (2 * Real.pi * δ) ^ 2 / 2 = ε := by
    have h1 : δ ^ 2 = ε / (2 * Real.pi ^ 2) := by
      rw [hδdef]
      exact Real.sq_sqrt (by positivity)
    have h2 : (2 * Real.pi * δ) ^ 2 = 4 * Real.pi ^ 2 * δ ^ 2 := by ring
    rw [h2, h1]
    field_simp
    norm_num
  linarith [hcosb, hsq, hdelta]

-- ============================================================
-- 5. 主导支配定理: 模长最大偏线零点使截断 Li 和变负
-- ============================================================

/-- 极坐标实部公式: `Re[uⁿ] = |u|ⁿ · cos(n·arg u)`. -/
lemma re_pow_eq_norm_pow_mul_cos {u : ℂ} (n : ℕ) :
    (u ^ n).re = (‖u‖ : ℝ) ^ n * Real.cos ((n : ℝ) * Complex.arg u) := by
  have hpolar : u = ‖u‖ * Complex.exp (Complex.arg u * I) :=
    (Complex.norm_mul_exp_arg_mul_I u).symm
  have hnp : u ^ n = (‖u‖ * Complex.exp (Complex.arg u * I)) ^ n :=
    congrArg (fun z => z ^ n) hpolar
  rw [hnp, mul_pow, ← Complex.exp_nat_mul]
  have hcast : (n : ℕ) * (Complex.arg u * I) =
      Complex.ofReal ((n : ℝ) * Complex.arg u) * I := by
    push_cast
    ring
  rw [hcast, Complex.mul_re, Complex.exp_ofReal_mul_I_re, ← Complex.ofReal_pow,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **主导支配定理 (同时回归版)**: 若有限零点集中存在某元素 ρ₀ 使
    `|u(ρ₀)| > 1` (无需最大性或唯一性假设), 则某阶截断 Li 和严格为负.

    证明机制:
    * 多维同时辐角回归 (`exists_simultaneous_cos_ge`) 对全体 ρ ∈ S
      同时给出 Re[u(ρ)ⁿ] ≥ (1/2)|u(ρ)|ⁿ — 同模共振类被统一处理,
      无需主导唯一性, 亦无需其余项模长受限;
    * 总和 = |S| - Σ Re[u(ρ)ⁿ] ≤ |S| - (1/2)|u(ρ₀)|ⁿ;
    * 指数增长支配常数项 |S|, 总和 < 0. -/
theorem li_dominance {S : Finset ℂ} {ρ₀ : ℂ}
    (h₀ : ρ₀ ∈ S)
    (hM : 1 < ‖(1 : ℂ) - ρ₀⁻¹‖) :
    ∃ n : ℕ, (∑ ρ ∈ S, liTerm ρ n) < 0 := by
  classical
  set M : ℝ := ‖(1 : ℂ) - ρ₀⁻¹‖
  have hM1 : 1 < M := hM
  set N := S.card with hN
  have hNge1 : 1 ≤ N := Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨ρ₀, h₀⟩)
  -- 步骤 A: 主导幂下界
  obtain ⟨Q₂, hQ₂⟩ := exists_pow_ge_const_of_one_lt hM1 (2 * ((N : ℝ) + 1))
  -- 步骤 B: 同时辐角回归 (共振类全体 S, ε = 1/2)
  obtain ⟨n, hnQ, hcos⟩ := exists_simultaneous_cos_ge
    (fun j : ↥S => Complex.arg (1 - ((j : ℂ)⁻¹))) (ε := 1 / 2) (by norm_num) Q₂
  -- 步骤 C: 每项实部下界 — 共振类全体同时回归, 无需区分是否严格主导
  have hre : ∀ ρ ∈ S, (1 / 2 : ℝ) * ‖(1 : ℂ) - ρ⁻¹‖ ^ n ≤ (((1 : ℂ) - ρ⁻¹) ^ n).re := by
    intro ρ hρ
    have hc := hcos ⟨ρ, hρ⟩
    rw [re_pow_eq_norm_pow_mul_cos n]
    have hhalf : (1 / 2 : ℝ) * ‖(1 : ℂ) - ρ⁻¹‖ ^ n =
        ‖(1 : ℂ) - ρ⁻¹‖ ^ n * (1 - 1 / 2) := by
      have h52 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
      rw [h52]
      ring
    rw [hhalf]
    exact mul_le_mul_of_nonneg_left hc (pow_nonneg (norm_nonneg _) n)
  -- 步骤 D: 总和上界
  have htotal : ∑ ρ ∈ S, liTerm ρ n ≤ ((N : ℝ)) - (1 / 2) * M ^ n := by
    have h1 : ∑ ρ ∈ S, liTerm ρ n = ((N : ℝ)) - ∑ ρ ∈ S, (((1 : ℂ) - ρ⁻¹) ^ n).re := by
      simp only [liTerm, Complex.sub_re, Complex.one_re]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.smul_one_eq_cast]
    have h2 : (1 / 2) * M ^ n ≤ ∑ ρ ∈ S, (((1 : ℂ) - ρ⁻¹) ^ n).re := by
      have hnn : ∀ ρ ∈ S, (0 : ℝ) ≤ (((1 : ℂ) - ρ⁻¹) ^ n).re := by
        intro ρ hρ
        exact le_trans (by positivity) (hre ρ hρ)
      exact le_trans (hre ρ₀ h₀) (Finset.single_le_sum hnn h₀)
    rw [h1]
    linarith
  -- 步骤 E: 指数支配常数项
  have hMpow : 2 * ((N : ℝ) + 1) ≤ M ^ n := hQ₂ n hnQ
  refine ⟨n, ?_⟩
  have hcalc : ((N : ℝ)) - (1 / 2) * M ^ n < 0 := by
    have hhalf : (N : ℝ) + 1 ≤ (1 / 2) * M ^ n := by
      calc (N : ℝ) + 1 = (1 / 2) * (2 * ((N : ℝ) + 1)) := by ring
        _ ≤ (1 / 2) * M ^ n := mul_le_mul_of_nonneg_left hMpow (by norm_num)
    linarith
  calc ∑ ρ ∈ S, liTerm ρ n ≤ ((N : ℝ)) - (1 / 2) * M ^ n := htotal
    _ < 0 := hcalc

-- ============================================================
-- 6. BL 条件框架与反向节点 (节点 9)
-- ============================================================

/-- 函数方程反射下的偏线零点左移: 若 RH 失败, 由对称性 (函数方程
    s ↦ 1 - s 反射) 可取到 Re < 1/2 的非平凡零点.

    BL 1994 反向论证第一步: 偏线零点总可移到临界线左侧, 使其 Li
    相位因子 `1 - 1/ρ` 落在单位圆外. -/
theorem exists_left_offline_zero
    (hsym : ∀ ρ ∈ nontrivialZeros, (1 - ρ) ∈ nontrivialZeros) :
    ¬riemannHypothesis → ∃ ρ₀ : ℂ, ρ₀ ∈ nontrivialZeros ∧ ρ₀.re < 1 / 2 := by
  intro hRH
  have hne : offLineZeros ≠ ∅ := fun h => hRH (rh_iff_offLine_empty.mpr h)
  obtain ⟨ρ₁, hρ₁⟩ := (Set.nonempty_iff_ne_empty.mpr hne)
  have hρ₁nt : ρ₁ ∈ nontrivialZeros := hρ₁.1
  have hρ₁re : ρ₁.re ≠ 1 / 2 := fun h => hρ₁.2 h
  rcases lt_or_gt_of_ne hρ₁re with h | h
  · exact ⟨ρ₁, hρ₁nt, h⟩
  · refine ⟨1 - ρ₁, hsym ρ₁ hρ₁nt, ?_⟩
    have hsub : (1 - ρ₁).re = 1 - ρ₁.re := by simp [Complex.sub_re]
    rw [hsub]
    linarith

/-- **节点 9 (反向)**: BL 条件框架下截断 Li 系数非负 ⟹ RH.

    BL 骨架假设 (对应 BL 1994 定理 1 条件的结构化拆分):
    * `hcoeff`: 所有截断 Li 系数非负 (Li 判据结论侧);
    * `hsym`: 函数方程反射对称 (零点集关于 s ↦ 1 - s 封闭).

    机制: 反证. 偏线零点左移得 Re ρ₀ < 1/2, 取大 R 使 ρ₀ 进入截断集;
    截断集内取模长最大者 ρ* (其模 > 1), `li_dominance` 以多维同时
    辐角回归处理全体共振类 (无需主导唯一性) 给出某阶截断 Li 和
    严格为负, 与 `hcoeff` 矛盾. -/
theorem liCoeffTrunc_nonneg_imp_rh
    (hcoeff : ∀ n : ℕ, ∀ R : ℝ, 0 ≤ liCoeffTrunc n R)
    (hsym : ∀ ρ ∈ nontrivialZeros, (1 - ρ) ∈ nontrivialZeros) :
    riemannHypothesis := by
  by_contra hRH
  obtain ⟨ρ₀, hρ₀mem, hρ₀lt⟩ := exists_left_offline_zero hsym hRH
  have hρ₀ne : ρ₀ ≠ 0 := nontrivial_zero_ne_zero hρ₀mem
  have hρ₀trunc : ρ₀ ∈ truncatedZeros (‖ρ₀‖ + 1) := by
    refine ⟨hρ₀mem, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ρ₀ ∈ truncatedZeros R := ⟨‖ρ₀‖ + 1, hρ₀trunc⟩
  have hρ₀S : ρ₀ ∈ (truncatedZeros_finite R).toFinset :=
    (truncatedZeros_finite R).mem_toFinset.mpr hR
  obtain ⟨ρd, hρdmem, hρdmax⟩ := Finset.exists_max_image
    (truncatedZeros_finite R).toFinset (fun ρ : ℂ => ‖(1 : ℂ) - ρ⁻¹‖) ⟨ρ₀, hρ₀S⟩
  have hgt : 1 < ‖(1 : ℂ) - ρd⁻¹‖ :=
    lt_of_lt_of_le (norm_one_sub_inv_gt_one hρ₀lt hρ₀ne) (hρdmax ρ₀ hρ₀S)
  obtain ⟨n, hn⟩ := li_dominance hρdmem hgt
  have hpos : (0 : ℝ) ≤ ∑ ρ ∈ (truncatedZeros_finite R).toFinset, liTerm ρ n :=
    hcoeff n R
  exact absurd hn (not_lt.mpr hpos)

/-- **Li 判据等价 (BL 骨架, 模块主定理)**: BL 条件框架下

        RH  ⟺  ∀ n R, λₙ(R) ≥ 0.

    正向 (节点 8, `rh_imp_liCoeffTrunc_nonneg`) 无条件成立;
    反向 (节点 9) 需要 BL 骨架假设 (对称性; 多零点同模共振由多维
    同时辐角回归统一处理, 无主导唯一假设).

    **[K4 语义标注, 2026-09-08] 桥定理 (equivalence bridge), 非 RH
    或 Li 正性任何一侧的证明**:
    (1) `hsym` = 函数方程零点对称 (零点集对 `ρ ↦ 1 - ρ` 封闭),
        **可证成分** — 已由 `RH_ExplicitFormula.zero_symmetry`
        (节点 10, 从 completed ζ 函数方程无条件证明) 消解,
        无条件等价版本见 `liCoeffTrunc_iff_rh_of_dominance`;
        BL 骨架中不存在其余未证对称性假设 (主导唯一性 `huniq`
        已于 2026-08-30 被多维同时辐角回归消除);
    (2) 本定理证明的是两侧**等价**: 既未证明 RH, 也未证明任何
        λₙ(R) ≥ 0 — 等价网络的全部输出是互推关系. -/
theorem liCoeffTrunc_iff_rh
    (hsym : ∀ ρ ∈ nontrivialZeros, (1 - ρ) ∈ nontrivialZeros) :
    riemannHypothesis ↔ ∀ n : ℕ, ∀ R : ℝ, 0 ≤ liCoeffTrunc n R :=
  ⟨fun hRH n R => rh_imp_liCoeffTrunc_nonneg hRH n R,
    fun hcoeff => liCoeffTrunc_nonneg_imp_rh hcoeff hsym⟩

end RHLiCriterion

end