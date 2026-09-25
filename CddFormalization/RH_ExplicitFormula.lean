import CddFormalization.RH_LiCriterion
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.MellinTransform

noncomputable section

/-! # Riemann Hypothesis: 显式公式与 Li 系数 Mellin 表示 (阶段 2b, 节点 10-11)

    本模块将 RH 等价网络扩展到显式公式维度, 补全 Li 判据的解析机制:

        节点 10: 零点对称 (无条件) + ψ 的 Abel-Mellin 表示 + von Koch 骨架
        节点 11: -ζ'/ζ 的 Mellin 变换刻画 + Li 系数的 BL 骨架

    ## 无条件零点对称 (节点 10 的解析基础)

    Mathlib 的 `completedRiemannZeta` (Λ 函数) 满足**无条件**函数方程
    `Λ(1 - s) = Λ(s)`. 在临界带 `0 < Re s < 1` 内 `Gammaℝ s ≠ 0`
    (`Gammaℝ_ne_zero_of_re_pos`), 故

        Λ(s) = Γℝ(s) · ζ(s)     (0 < Re s < 1)

    且零点在 `s ↦ 1 - s` 反射下封闭. 这把 `RH_LiCriterion` 中 BL 骨架的
    对称性假设 `hsym` 转化为无条件定理 —— BL 反向论证的函数方程支柱
    不再需要显式假设.

    ## ψ 的 Abel-Mellin 表示 (节点 10 主体)

    von Mangoldt 函数的 Dirichlet 级数即 ζ 的负对数导数 (Mathlib:
    `ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div`):

        -ζ'(s)/ζ(s) = Σ_Λ(n) n^{-s}      (Re s > 1).

    Mathlib 的 `LSeries_eq_mul_integral_of_nonneg` (内部经 Abel 求和
    `sum_mul_eq_sub_integral_mul₀'` 与极限形式) 把 Dirichlet 级数改写为
    部分和的加权积分; 取 `f = Λ`, 部分和恰为 Chebyshev ψ 函数
    (`psi_eq_sum_Icc`), 且 ψ(x) ≤ (log 4 + 4)x (`psi_le_const_mul_self`)
    满足 O(t) 增长条件, 于是得到**显式公式的 Mellin 形式**:

        -ζ'(s)/ζ(s) = s ∫₁^∞ ψ(t) t^{-s-1} dt = s · 𝓜[ψ](-s)   (Re s > 1).

    这是 von Koch 显式公式的"温和形式": 素数分布 (左端 ψ) 与 ζ 零点
    (右端对数导数的奇点) 通过 Mellin 变换逐点挂钩. 可积性
    (`integrableOn_psi_tmul`) 由 O(t) 上界与 σ = Re s > 1 时的
    `t^{-σ}` 可积性 (`integrableAtFilter_rpow_atTop_iff`) 联合保证.

    ## Mellin 桥接 (节点 11 完成)

    Mathlib 的 `mellin` 定义为 `𝓜[f](s) = ∫₀^∞ t^{s-1} • f(t) dt`
    (`Mathlib.Analysis.MellinTransform`). 由 ψ 在 (0,1] 上恒零
    (`psi_eq_zero_of_le_one`), Mellin 积分域收缩到 (1,∞):

        𝓜[ψ](-s) = ∫₁^∞ ψ(t) t^{-s-1} dt,

    收敛性由 `MellinConvergent` (`mellinConvergent_psi`) 无条件保证,
    于是显式公式取得标准 Mellin 形式:

        -ζ'(s)/ζ(s) = s · 𝓜[ψ](-s)     (`neg_logDeriv_eq_mul_mellin`).

    这为后续垂直带全纯性分析 (`mellin_differentiableAt_of_isBigO_rpow`)
    与零点谱反演提供了 Mathlib 原生接口.

    ## 骨架边界

    完整 von Koch 公式 (ψ(x) = x - Σ_ρ x^ρ/ρ - 常数项) 需要 -ζ'/ζ 的
    部分分式展开 (Hadamard 乘积), Mathlib 尚无; BL 的 λₙ 收敛性分析
    需要零点计数密度. 本模块以 Mellin 表示为无条件核心, 把上述内容
    定位为骨架 (显式假设).

    References:
    - von Koch (1901) Sur la distribution des nombres premiers
    - Bombieri & Lagarias (1994) Complements to Li's criterion
    - Davenport (2000) Multiplicative Number Theory, ch. 17-18
    - RH_MeasureTheory.lean (非平凡零点与临界带基础设施)
    - RH_LiCriterion.lean (Li 判据与 BL 骨架, 节点 8-9)
-/

namespace RHExplicitFormula

open RHMeasureTheory RHLiCriterion ArithmeticFunction Chebyshev MeasureTheory LSeries
open Filter Asymptotics Finset Complex Real Set
open scoped Chebyshev Topology

-- ============================================================
-- 1. 完成 ζ 与临界带: 无条件零点对称 (节点 10 解析基础)
-- ============================================================

/-- 临界带内 Λ 函数分解为 Γℝ 因子乘 ζ.

    `riemannZeta_def_of_ne_zero` 给出 ζ = Λ / Γℝ (s ≠ 0);
    临界带内 Γℝ 无零点, 故可反解. -/
theorem completedZeta_apply {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
  have hsne : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
  rw [riemannZeta_def_of_ne_zero hsne, mul_div_cancel₀ _ (Gammaℝ_ne_zero_of_re_pos hs)]

/-- **无条件零点对称 (节点 10)**: 非平凡零点在函数方程反射 `s ↦ 1 - s` 下封闭.

    证明机制: ρ ∈ 临界带 ⟹ Λ(ρ) = Γℝ(ρ)·ζ(ρ) = 0; 由函数方程
    `Λ(1-ρ) = Λ(ρ)` 与 `1-ρ` 仍在临界带 (Γℝ(1-ρ) ≠ 0) 反解出
    ζ(1-ρ) = 0.

    这一定理消解了 `RH_LiCriterion.liCoeffTrunc_iff_rh` 中
    BL 骨架的对称性假设 `hsym` (见 §3). -/
theorem zero_symmetry {ρ : ℂ} (hρ : ρ ∈ nontrivialZeros) : 1 - ρ ∈ nontrivialZeros := by
  obtain ⟨hzero, hpos, hlt⟩ := hρ
  have hΛ : completedRiemannZeta ρ = 0 := by
    rw [completedZeta_apply hpos, mul_eq_zero]
    exact Or.inr hzero
  have hre : 0 < (1 - ρ).re ∧ (1 - ρ).re < 1 := by
    simp only [Complex.sub_re, Complex.one_re]
    constructor <;> linarith
  have hΛ' : completedRiemannZeta (1 - ρ) = 0 := by
    rw [completedRiemannZeta_one_sub]
    exact hΛ
  have hζ' : riemannZeta (1 - ρ) = 0 := by
    have hfac : completedRiemannZeta (1 - ρ) = Gammaℝ (1 - ρ) * riemannZeta (1 - ρ) :=
      completedZeta_apply hre.1
    rw [hΛ'] at hfac
    exact (mul_eq_zero.mp hfac.symm).resolve_left (Gammaℝ_ne_zero_of_re_pos hre.1)
  exact ⟨hζ', hre.1, hre.2⟩

-- ============================================================
-- 2. 偏线对称与 RH 的左右偏线刻画
-- ============================================================

/-- 偏线零点集在函数方程反射下封闭. -/
theorem offLine_symmetry {ρ : ℂ} (hρ : ρ ∈ offLineZeros) : 1 - ρ ∈ offLineZeros := by
  have hmem : 1 - ρ ∈ nontrivialZeros := zero_symmetry hρ.1
  have hoff : 1 - ρ ∉ criticalLine := by
    intro h
    have hc : (1 - ρ).re = 1 / 2 := h
    rw [Complex.sub_re, Complex.one_re] at hc
    have hre : ρ.re = 1 / 2 := by linarith
    exact hρ.2 hre
  exact ⟨hmem, hoff⟩

/-- RH ⟺ 无左偏线 (Re < 1/2) 非平凡零点.

    正向: RH ⟹ 偏线集空 ⟹ 左偏线集空; 反向: 偏线零点若在右半带,
    经 §1 对称性反射为左偏线零点, 仍与空集矛盾.
    [K3 语义标注, 2026-09-08] **等价重述 (definitional + 已证函数方程
    对称 `zero_symmetry`), 非 RH 证明** — 本网络证明 RH 的各等价形式
    互推, 尚未证明 (也未否定) RH 本身. -/
theorem rh_iff_no_left_offLine :
    riemannHypothesis ↔ nontrivialZeros ∩ {s : ℂ | s.re < 1 / 2} = ∅ := by
  constructor
  · intro hRH
    have hempty : offLineZeros = ∅ := rh_iff_offLine_empty.mp hRH
    refine Set.eq_empty_iff_forall_notMem.mpr fun z hz => ?_
    exact Set.eq_empty_iff_forall_notMem.mp hempty z
      ⟨hz.1, fun hc => absurd hc (ne_of_lt hz.2)⟩
  · intro hempty
    refine rh_iff_offLine_empty.mpr (Set.eq_empty_iff_forall_notMem.mpr fun ρ hρ => ?_)
    have h1 : ρ ∈ nontrivialZeros := hρ.1
    rcases lt_or_gt_of_ne (fun he => hρ.2 he) with hlt | hgt
    · exact Set.eq_empty_iff_forall_notMem.mp hempty ρ ⟨h1, hlt⟩
    · have h1' : 1 - ρ ∈ nontrivialZeros := zero_symmetry h1
      have h2' : (1 - ρ).re < 1 / 2 := by
        rw [Complex.sub_re, Complex.one_re]
        linarith
      exact Set.eq_empty_iff_forall_notMem.mp hempty (1 - ρ) ⟨h1', h2'⟩

-- ============================================================
-- 3. BL 骨架对称性假设的消解 (节点 10 → 节点 9 桥)
-- ============================================================

/-- **BL 骨架精化 (节点 9 桥)**: 节点 10 的无条件零点对称消解了
    `liCoeffTrunc_iff_rh` 的 `hsym` 假设. 2026-08-30 `RH_LiCriterion`
    修订后 BL 反向链条**完全无条件**: 多零点同模共振由多维同时辐角
    回归 (`exists_simultaneous_cos_ge`, 鸽笼 Dirichlet + 倍增) 统一
    处理, 主导唯一性假设 `huniq` 已被消除. 本定理现为无条件等价:

        RH  ⟺  ∀ n R, λₙ(R) ≥ 0.

    [K4 语义标注, 2026-09-08] **桥定理 (equivalence bridge), 非任何
    一侧的证明**: 本定理证明的是 RH 与 Li 正性判据的**等价** (且已
    无条件) — 既未证明 RH, 也未证明任何 λₙ(R) ≥ 0; 等价网络的全部
    输出是互推关系, 尚未证明 (也未否定) 其中任何一侧. -/
theorem liCoeffTrunc_iff_rh_of_dominance :
    riemannHypothesis ↔ ∀ n : ℕ, ∀ R : ℝ, 0 ≤ liCoeffTrunc n R :=
  liCoeffTrunc_iff_rh (fun _ hρ => zero_symmetry hρ)

-- ============================================================
-- 4. ψ 的部分和结构与增长估计 (节点 10 主体, Mathlib Abel 求和接口)
-- ============================================================

/-- ψ 在自然数处的部分和展开: `ψ(n) = ∑_{k=1}^n Λ(k)`.

    `psi_eq_sum_Icc` 给出 `ψ(t) = ∑_{k ∈ Icc 0 ⌊t⌋₊} Λ(k)`, 而 `Λ 0 = 0`
    (0 非素数幂), 去掉 `k = 0` 项即得. -/
private theorem psi_eq_sum_Icc_one (n : ℕ) : ψ (n : ℝ) = ∑ k ∈ Icc 1 n, Λ k := by
  rw [psi_eq_sum_Icc (n : ℝ), Nat.floor_natCast,
    ← Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le n), Finset.sum_insert (by aesop),
    vonMangoldt_apply, if_neg not_isPrimePow_zero, zero_add]
  rfl

/-- ψ 的复化部分和展开 (floor 形式): `ψ(t) = ∑_{k=1}^{⌊t⌋} Λ(k)`. -/
private theorem psi_cplx_eq_sum_Icc (t : ℝ) :
    ((ψ t : ℝ) : ℂ) = ∑ k ∈ Icc 1 ⌊t⌋₊, ((Λ k : ℝ) : ℂ) := by
  rw [psi_eq_sum_Icc t, Complex.ofReal_sum,
    ← Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le _), Finset.sum_insert (by aesop),
    vonMangoldt_apply, if_neg not_isPrimePow_zero, Complex.ofReal_zero, zero_add]
  rfl

/-- ψ 部和的实值 O(n) 上界 (Chebyshev): `∑_{k≤n} Λ(k) ≤ (log 4 + 4) n`. -/
private theorem sum_vonMangoldt_real_isBigO :
    (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, Λ k) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ) := by
  refine IsBigO.of_bound (Real.log 4 + 4) (eventually_atTop.mpr ⟨1, fun n _ ↦ ?_⟩)
  rw [← psi_eq_sum_Icc_one, Real.norm_of_nonneg (psi_nonneg (n : ℝ)), Real.norm_eq_abs,
    Real.rpow_one, abs_of_nonneg (Nat.cast_nonneg n)]
  exact psi_le_const_mul_self (Nat.cast_nonneg n)

/-- ψ 部和的复值 O(n) 上界. -/
private theorem sum_vonMangoldt_cplx_isBigO :
    (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, ((Λ k : ℝ) : ℂ)) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ) := by
  refine IsBigO.of_bound (Real.log 4 + 4) (eventually_atTop.mpr ⟨1, fun n _ ↦ ?_⟩)
  rw [← Complex.ofReal_sum, ← psi_eq_sum_Icc_one, Complex.norm_real,
    Real.norm_of_nonneg (psi_nonneg (n : ℝ)), Real.norm_eq_abs, Real.rpow_one,
    abs_of_nonneg (Nat.cast_nonneg n)]
  exact psi_le_const_mul_self (Nat.cast_nonneg n)

/-- 复化 ψ(t) (floor 部分) 的 O(t) 上界: `∑_{k≤⌊t⌋} Λ(k) = O(t)`. -/
private theorem sum_vonMangoldt_cplx_floor_isBigO :
    (fun t : ℝ ↦ ∑ k ∈ Icc 1 ⌊t⌋₊, ((Λ k : ℝ) : ℂ)) =O[atTop] fun t ↦ t ^ (1 : ℝ) :=
  (sum_vonMangoldt_cplx_isBigO.comp_tendsto tendsto_nat_floor_atTop).trans <|
    isEquivalent_nat_floor.isBigO.rpow zero_le_one (eventually_ge_atTop 0)

-- ============================================================
-- 5. 主定理: -ζ'/ζ(s) = s ∫₁^∞ ψ(t) t^{-s-1} dt (节点 11)
-- ============================================================

/-- **ψ 加权幂积分的可积性** (Re s > 1, 节点 11 基础).

    证明: 局部可积性由 `locallyIntegrableOn_mul_sum_Icc` (阶梯部分和
    × 连续核) 给出; 尾部由复化 ψ 的 O(t) 上界与
    `‖t^{-s-1}‖ = t^{-(σ+1)}` (σ = Re s) 联合控制, 乘积为
    O(t^{-σ}), σ > 1 时于 [1,∞) 可积 (`integrableAtFilter_rpow_atTop_iff`). -/
theorem integrableOn_psi_tmul {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ ↦ ((ψ t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)) (Set.Ioi 1) := by
  rw [← integrableOn_Ici_iff_integrableOn_Ioi]
  have hf : (fun t : ℝ ↦ ((ψ t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1))
      = fun t : ℝ ↦ (∑ k ∈ Icc 1 ⌊t⌋₊, ((Λ k : ℝ) : ℂ)) * (t : ℂ) ^ (-s - 1) := by
    funext t
    rw [psi_cplx_eq_sum_Icc]
  rw [hf]
  have h₁ : LocallyIntegrableOn
      (fun t : ℝ ↦ (∑ k ∈ Icc 1 ⌊t⌋₊, ((Λ k : ℝ) : ℂ)) * (t : ℂ) ^ (-s - 1)) (Set.Ici 1) := by
    simp_rw [mul_comm]
    refine locallyIntegrableOn_mul_sum_Icc (c := fun k : ℕ ↦ ((Λ k : ℝ) : ℂ)) zero_le_one ?_
    refine ContinuousOn.locallyIntegrableOn (fun t ht ↦ ?_) measurableSet_Ici
    exact (Complex.continuousAt_ofReal_cpow_const _ _
      (Or.inr (zero_lt_one.trans_le ht).ne')).continuousWithinAt
  refine h₁.integrableOn_of_isBigO_atTop (g := fun t ↦ t ^ (-s.re)) ?_ ?_
  · refine IsBigO.mul_atTop_rpow_of_isBigO_rpow 1 (-s - 1).re _ sum_vonMangoldt_cplx_floor_isBigO
      ?_ (by simp)
    exact (norm_ofReal_cpow_eventually_eq_atTop (-s - 1)).isBigO.of_norm_left
  · rw [integrableAtFilter_rpow_atTop_iff]
    linarith

/-- **显式公式的 Mellin 形式 (主定理, 节点 11)**: Re s > 1 时

        -ζ'(s)/ζ(s) = s ∫₁^∞ ψ(t) t^{-s-1} dt.

    证明链: (i) von Mangoldt 的 L-级数恒等于 ζ 的负对数导数
    (`LSeries_vonMangoldt_eq_deriv_riemannZeta_div`);
    (ii) `LSeries_eq_mul_integral_of_nonneg` 把非负系数 L-级数
    (O(n) 部和) 改写为部阶梯函数 × `t^{-s-1}` 的加权积分;
    (iii) 部分阶梯函数即复化 ψ (`psi_cplx_eq_sum_Icc`).

    这是素数分布与 ζ 零点谱的第一座无条件桥梁: 右端 ψ 的分布信息
    (素数定理) 通过积分核完全编码于左端的对数导数奇点结构. -/
theorem neg_logDeriv_riemannZeta_eq_mul_integral (s : ℂ) (hs : 1 < s.re) :
    -deriv riemannZeta s / riemannZeta s =
      s * ∫ t in Set.Ioi (1 : ℝ), ((ψ t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs,
    LSeries_eq_mul_integral_of_nonneg (fun n : ℕ ↦ Λ n) zero_le_one hs
      sum_vonMangoldt_real_isBigO (fun n ↦ vonMangoldt_nonneg)]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
  rw [psi_cplx_eq_sum_Icc]

-- ============================================================
-- 6. Mellin 桥接: 显式公式接入 Mathlib Mellin 变换框架 (节点 11 完成)
-- ============================================================

/-- 区间分解: `Ioi 0 = Ioc 0 1 ∪ Ioi 1` (Mellin 积分域拆分). -/
private theorem ioi_zero_split : Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) := by
  ext x
  simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
  constructor
  · intro hx
    by_cases h : x ≤ 1
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr (not_le.mp h)
  · rintro (⟨hx, _⟩ | h)
    · exact hx
    · exact lt_trans zero_lt_one h

/-- 区间不交性: `(0,1] ∩ (1,∞) = ∅`. -/
private theorem ioc_disjoint_ioi : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioi (1 : ℝ)) := by
  rw [Set.disjoint_left]
  intro x hx
  exact not_lt.2 (Set.mem_Ioc.mp hx).2

/-- (0,1] 上 Mellin 被积函数的可积性: ψ = 0 (`psi_eq_zero_of_le_one`) 使被积函数恒零. -/
private theorem integrableOn_Ioc_smul_psi {s : ℂ} :
    IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (-s - 1) • ((ψ t : ℝ) : ℂ)) (Set.Ioc (0 : ℝ) 1) := by
  refine IntegrableOn.congr_fun (f := fun _ : ℝ ↦ (0 : ℂ)) integrableOn_zero ?_ measurableSet_Ioc
  intro t ht
  show (0 : ℂ) = (t : ℂ) ^ (-s - 1) • ((ψ t : ℝ) : ℂ)
  rw [psi_eq_zero_of_le_one ht.2, Complex.ofReal_zero, smul_zero]

/-- (1,∞) 上 Mellin 被积函数的可积性: 由 `integrableOn_psi_tmul` 转换 smul 形式. -/
private theorem integrableOn_Ioi_smul_psi {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (-s - 1) • ((ψ t : ℝ) : ℂ)) (Set.Ioi (1 : ℝ)) := by
  refine IntegrableOn.congr_fun
    (f := fun t : ℝ ↦ ((ψ t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)) (integrableOn_psi_tmul hs) ?_
    measurableSet_Ioi
  intro t _
  show ((ψ t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1) = (t : ℂ) ^ (-s - 1) • ((ψ t : ℝ) : ℂ)
  rw [smul_eq_mul]
  ring

/-- **ψ 的 Mellin 变换收敛性 (节点 11)**: Re s > 1 时 `MellinConvergent ψ (-s)`.

    Mellin 积分域 `Ioi 0` 拆分为 `(0,1] ∪ (1,∞)`:
    前者 ψ = 0 被积函数恒零, 后者即 §5 的 `integrableOn_psi_tmul`
    (smul 形式). -/
theorem mellinConvergent_psi {s : ℂ} (hs : 1 < s.re) :
    MellinConvergent (fun t : ℝ ↦ ((ψ t : ℝ) : ℂ)) (-s) := by
  show IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (-s - 1) • ((ψ t : ℝ) : ℂ)) (Set.Ioi 0)
  rw [ioi_zero_split, integrableOn_union]
  exact ⟨integrableOn_Ioc_smul_psi, integrableOn_Ioi_smul_psi hs⟩

/-- **ψ 的 Mellin 变换支集收缩 (节点 11)**: Re s > 1 时

        𝓜[ψ](-s) = ∫₀^∞ ψ(t) t^{-s-1} dt = ∫₁^∞ ψ(t) t^{-s-1} dt.

    证明: `Ioi 0 = (0,1] ∪ (1,∞)` 不交拆分; (0,1] 上 ψ = 0
    (`psi_eq_zero_of_le_one`) 积分贡献为零, 剩余 (1,∞) 上的
    积分经 `smul`-`mul` 与指数形式 `-s-1 = -(s+1)` 转换即主定理
    的积分. -/
theorem mellin_psi_eq {s : ℂ} (hs : 1 < s.re) :
    mellin (fun t : ℝ ↦ ((ψ t : ℝ) : ℂ)) (-s) =
      ∫ t in Set.Ioi (1 : ℝ), ((ψ t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  have hz : ∫ t in Set.Ioc (0 : ℝ) 1, (t : ℂ) ^ (-s - 1) • ((ψ t : ℝ) : ℂ) = 0 := by
    have h : ∫ t in Set.Ioc (0 : ℝ) 1, (t : ℂ) ^ (-s - 1) • ((ψ t : ℝ) : ℂ)
        = ∫ t in Set.Ioc (0 : ℝ) 1, (0 : ℂ) :=
      setIntegral_congr_fun measurableSet_Ioc fun t ht => by
        show (t : ℂ) ^ (-s - 1) • ((ψ t : ℝ) : ℂ) = (0 : ℂ)
        rw [psi_eq_zero_of_le_one ht.2, Complex.ofReal_zero, smul_zero]
    rw [h, setIntegral_const (0 : ℂ), smul_zero]
  have hconv : ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s - 1) • ((ψ t : ℝ) : ℂ)
      = ∫ t in Set.Ioi (1 : ℝ), ((ψ t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    show (t : ℂ) ^ (-s - 1) • ((ψ t : ℝ) : ℂ) = ((ψ t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))
    have hexp : (-s - 1 : ℂ) = -(s + 1) := by ring
    rw [smul_eq_mul, hexp]
    ring
  show ∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ (-s - 1) • ((ψ t : ℝ) : ℂ)
      = ∫ t in Set.Ioi (1 : ℝ), ((ψ t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))
  rw [ioi_zero_split, setIntegral_union ioc_disjoint_ioi measurableSet_Ioi
    integrableOn_Ioc_smul_psi (integrableOn_Ioi_smul_psi hs), hz, hconv, zero_add]

/-- **显式公式的 Mellin 变换形式 (节点 11 完成)**: Re s > 1 时

        -ζ'(s)/ζ(s) = s · 𝓜[ψ](-s),

    其中 `𝓜[ψ](-s) = ∫₀^∞ ψ(t) t^{-s-1} dt` 是 Mathlib `mellin` 定义.

    这把主定理 (§5) 的积分表示直接接入 Mathlib 的 Mellin 变换框架
    (`Mathlib.Analysis.MellinTransform`), 为后续解析延拓
    (`mellin_differentiableAt_of_isBigO_rpow`) 与垂直带上的全纯性
    分析提供标准接口. -/
theorem neg_logDeriv_eq_mul_mellin (s : ℂ) (hs : 1 < s.re) :
    -deriv riemannZeta s / riemannZeta s = s * mellin (fun t : ℝ ↦ ((ψ t : ℝ) : ℂ)) (-s) := by
  rw [mellin_psi_eq hs]
  exact neg_logDeriv_riemannZeta_eq_mul_integral s hs

end RHExplicitFormula

end
