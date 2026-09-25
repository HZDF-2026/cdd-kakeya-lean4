import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.AbelSummation

open ArithmeticFunction Chebyshev MeasureTheory LSeries Filter Asymptotics Finset Complex Real
open scoped Chebyshev LSeries.notation

-- A. ψ 部分和换算: 复化 von Mangoldt 部分和 = ψ
example (t : ℝ) : ((ψ t : ℝ) : ℂ) = ∑ k ∈ Icc 1 ⌊t⌋₊, ((Λ k : ℝ) : ℂ) := by
  rw [psi_eq_sum_Icc t, Complex.ofReal_sum,
    ← Finset.insert_Icc_add_one_left_eq_Icc Nat.zero_le,
    Finset.sum_insert (by simp), ArithmeticFunction.zero_apply, zero_add]

-- B. 实数复化的范数
example (t : ℝ) (h : 0 ≤ t) : ‖((ψ t : ℝ) : ℂ)‖ = ψ t := by
  rw [Complex.norm_real, Real.norm_of_nonneg h]

-- C. ℕ 索引部分和的 O(n) 界
private theorem sum_vonMangoldt_nat_isBigO :
    (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, ((Λ k : ℝ) : ℂ)) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ) := by
  refine IsBigO.of_bound (Real.log 4 + 4) (eventually_atTop.mpr ⟨1, fun n _ => ?_⟩)
  have key : ((ψ (n : ℝ) : ℝ) : ℂ) = ∑ k ∈ Icc 1 n, ((Λ k : ℝ) : ℂ) := by
    have h := psi_eq_sum_Icc (n : ℝ)
    rw [Nat.floor_natCast] at h
    rw [h, Complex.ofReal_sum, ← Finset.insert_Icc_add_one_left_eq_Icc Nat.zero_le,
      Finset.sum_insert (by simp), ArithmeticFunction.zero_apply, zero_add]
  rw [← key, Complex.norm_real, Real.norm_of_nonneg (psi_nonneg (n : ℝ)), Real.rpow_one,
    Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) 1)]
  exact psi_le_const_mul_self (Nat.cast_nonneg n)

-- D. ℝ 索引 (floor) 部分和的 O(t) 界
example : (fun t : ℝ ↦ ∑ k ∈ Icc 1 ⌊t⌋₊, ((Λ k : ℝ) : ℂ)) =O[atTop]
    fun t : ℝ ↦ t ^ (1 : ℝ) := by
  refine (sum_vonMangoldt_nat_isBigO.comp_tendsto tendsto_nat_floor_atTop).trans ?_
  exact isEquivalent_nat_floor.isBigO.rpow le_rfl (eventually_ge_atTop 0)

-- E. t^{-s-1} 在 Ici 1 上连续
example (s : ℂ) : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-s - 1)) (Set.Ici 1) := by
  refine ContinuousOn.cpow_const (f := fun t : ℝ => (t : ℂ))
    Complex.continuous_ofReal.continuousOn ?_
  intro t ht
  exact ofReal_mem_slitPlane.mpr (lt_of_le_of_lt ht (by norm_num))

-- F. 部分和 × 连续函数的局部可积性
example (s : ℂ) : LocallyIntegrableOn
    (fun t : ℝ => (t : ℂ) ^ (-s - 1) * ∑ k ∈ Icc 1 ⌊t⌋₊, ((Λ k : ℝ) : ℂ)) (Set.Ici 1) := by
  refine locallyIntegrableOn_mul_sum_Icc
    (c := fun k : ℕ => ((Λ k : ℝ) : ℂ)) le_rfl ?_
  exact (ContinuousOn.locallyIntegrableOn (g := fun t : ℝ => (t : ℂ) ^ (-s - 1)) ?_
    measurableSet_Ici)
  exact ContinuousOn.cpow_const (f := fun t : ℝ => (t : ℂ))
    Complex.continuous_ofReal.continuousOn fun t ht =>
    ofReal_mem_slitPlane.mpr (lt_of_le_of_lt ht (by norm_num))

-- G. 可积性主引理
example (s : ℂ) (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => ((ψ t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)) (Set.Ioi 1) := by
  rw [← integrableOn_Ici_iff_integrableOn_Ioi]
  have hloc : LocallyIntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (-s - 1) * ∑ k ∈ Icc 1 ⌊t⌋₊, ((Λ k : ℝ) : ℂ)) (Set.Ici 1) := by
    refine locallyIntegrableOn_mul_sum_Icc
      (c := fun k : ℕ => ((Λ k : ℝ) : ℂ)) le_rfl ?_
    exact ContinuousOn.locallyIntegrableOn
      (ContinuousOn.cpow_const (f := fun t : ℝ => (t : ℂ))
        Complex.continuous_ofReal.continuousOn fun t ht =>
        ofReal_mem_slitPlane.mpr (lt_of_le_of_lt ht (by norm_num))) measurableSet_Ici
  have hψ : (fun t : ℝ => ((ψ t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1))
      = fun t : ℝ => (t : ℂ) ^ (-s - 1) * ∑ k ∈ Icc 1 ⌊t⌋₊, ((Λ k : ℝ) : ℂ) := by
    funext t
    rw [psi_eq_sum_Icc t, Complex.ofReal_sum,
      ← Finset.insert_Icc_add_one_left_eq_Icc Nat.zero_le,
      Finset.sum_insert (by simp), ArithmeticFunction.zero_apply, zero_add, mul_comm]
  rw [hψ]
  refine hloc.integrableOn_of_isBigO_atTop (g := fun t : ℝ => t ^ (-(s.re))) ?_ ?_
  · refine IsBigO.mul_atTop_rpow_of_isBigO_rpow 1 (-(s.re) - 1) _ ?_ ?_ ?_
    · exact (sum_vonMangoldt_nat_isBigO.comp_tendsto tendsto_nat_floor_atTop).trans
        (isEquivalent_nat_floor.isBigO.rpow le_rfl (eventually_ge_atTop 0))
    · exact (Complex.norm_ofReal_cpow_eventually_eq_atTop _).isBigO.of_norm_left
    · linarith
  · rw [integrableAtFilter_rpow_atTop_iff]
    linarith

-- H. 主定理
example (s : ℂ) (hs : 1 < s.re) :
    -deriv riemannZeta s / riemannZeta s =
      s * ∫ t in Set.Ioi (1 : ℝ), ((ψ t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  have hint := LSeries_eq_mul_integral (f := fun n : ℕ ↦ (Λ n : ℂ)) (r := 1)
    zero_le_one hs (ArithmeticFunction.LSeriesSummable_vonMangoldt hs)
    sum_vonMangoldt_nat_isBigO
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, hint]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [psi_eq_sum_Icc t, Complex.ofReal_sum,
    ← Finset.insert_Icc_add_one_left_eq_Icc Nat.zero_le,
    Finset.sum_insert (by simp), ArithmeticFunction.zero_apply, zero_add, mul_comm]
