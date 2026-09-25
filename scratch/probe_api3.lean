import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open ArithmeticFunction Chebyshev MeasureTheory LSeries Filter Asymptotics Finset Complex Real
open scoped Chebyshev LSeries.notation

-- 1. Λ 0 = 0
example : Λ 0 = 0 := by
  rw [vonMangoldt_apply, if_neg not_isPrimePow_zero]

-- 2. ψ 部分和 (实)
private theorem psi_eq_sum_Icc_one (n : ℕ) : ψ (n : ℝ) = ∑ k ∈ Icc 1 n, Λ k := by
  rw [psi_eq_sum_Icc (n : ℝ), Nat.floor_natCast,
    ← Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le n), Finset.sum_insert (by aesop),
    vonMangoldt_apply, if_neg not_isPrimePow_zero, zero_add]
  rfl

-- 3. ψ 部分和 (复, floor)
example (t : ℝ) : ((ψ t : ℝ) : ℂ) = ∑ k ∈ Icc 1 ⌊t⌋₊, ((Λ k : ℝ) : ℂ) := by
  rw [psi_eq_sum_Icc t, Complex.ofReal_sum,
    ← Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le _), Finset.sum_insert (by aesop),
    vonMangoldt_apply, if_neg not_isPrimePow_zero, Complex.ofReal_zero, zero_add]
  rfl

-- 4. 实 O(n)
private theorem sum_vonMangoldt_real_isBigO :
    (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, Λ k) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ) := by
  refine IsBigO.of_bound (Real.log 4 + 4) (eventually_atTop.mpr ⟨1, fun n _ ↦ ?_⟩)
  rw [← psi_eq_sum_Icc_one, Real.norm_of_nonneg (psi_nonneg (n : ℝ)), Real.norm_eq_abs,
    Real.rpow_one, abs_of_nonneg (Nat.cast_nonneg n)]
  exact psi_le_const_mul_self (Nat.cast_nonneg n)

-- 5. 复 O(n)
private theorem sum_vonMangoldt_cplx_isBigO :
    (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, ((Λ k : ℝ) : ℂ)) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ) := by
  refine IsBigO.of_bound (Real.log 4 + 4) (eventually_atTop.mpr ⟨1, fun n _ ↦ ?_⟩)
  rw [← Complex.ofReal_sum, ← psi_eq_sum_Icc_one, Complex.norm_real,
    Real.norm_of_nonneg (psi_nonneg (n : ℝ)), Real.norm_eq_abs, Real.rpow_one,
    abs_of_nonneg (Nat.cast_nonneg n)]
  exact psi_le_const_mul_self (Nat.cast_nonneg n)

-- 6. floor 复 O(t)
private theorem sum_vonMangoldt_cplx_floor_isBigO :
    (fun t : ℝ ↦ ∑ k ∈ Icc 1 ⌊t⌋₊, ((Λ k : ℝ) : ℂ)) =O[atTop] fun t ↦ t ^ (1 : ℝ) :=
  (sum_vonMangoldt_cplx_isBigO.comp_tendsto tendsto_nat_floor_atTop).trans <|
    isEquivalent_nat_floor.isBigO.rpow zero_le_one (eventually_ge_atTop 0)

-- 7. 可积性主引理
example (s : ℂ) (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ ↦ ((ψ t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)) (Set.Ioi 1) := by
  rw [← integrableOn_Ici_iff_integrableOn_Ioi]
  have hf : (fun t : ℝ ↦ ((ψ t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1))
      = fun t : ℝ ↦ (∑ k ∈ Icc 1 ⌊t⌋₊, ((Λ k : ℝ) : ℂ)) * (t : ℂ) ^ (-s - 1) := by
    funext t
    rw [psi_eq_sum_Icc t, Complex.ofReal_sum,
      ← Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le _), Finset.sum_insert (by aesop),
      vonMangoldt_apply, if_neg not_isPrimePow_zero, Complex.ofReal_zero, zero_add]
    rfl
  rw [hf]
  have h₁ : LocallyIntegrableOn
      (fun t : ℝ ↦ (∑ k ∈ Icc 1 ⌊t⌋₊, ((Λ k : ℝ) : ℂ)) * (t : ℂ) ^ (-s - 1)) (Set.Ici 1) := by
    simp_rw [mul_comm]
    refine locallyIntegrableOn_mul_sum_Icc (c := fun k : ℕ ↦ ((Λ k : ℝ) : ℂ)) zero_le_one ?_
    refine ContinuousOn.locallyIntegrableOn (fun t ht ↦ ?_) measurableSet_Ici
    exact (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (zero_lt_one.trans_le ht).ne')).continuousWithinAt
  refine h₁.integrableOn_of_isBigO_atTop (g := fun t ↦ t ^ (-s.re)) ?_ ?_
  · refine IsBigO.mul_atTop_rpow_of_isBigO_rpow 1 (-s - 1).re _ sum_vonMangoldt_cplx_floor_isBigO
      ?_ (by simp)
    exact (norm_ofReal_cpow_eventually_eq_atTop (-s - 1)).isBigO.of_norm_left
  · rw [integrableAtFilter_rpow_atTop_iff]
    linarith

-- 8. 主定理
example (s : ℂ) (hs : 1 < s.re) :
    -deriv riemannZeta s / riemannZeta s =
      s * ∫ t in Set.Ioi (1 : ℝ), ((ψ t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs,
    LSeries_eq_mul_integral_of_nonneg (fun n : ℕ ↦ Λ n) zero_le_one hs
      sum_vonMangoldt_real_isBigO (fun n ↦ vonMangoldt_nonneg)]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
  rw [psi_eq_sum_Icc t, Complex.ofReal_sum,
    ← Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le _), Finset.sum_insert (by aesop),
    vonMangoldt_apply, if_neg not_isPrimePow_zero, Complex.ofReal_zero, zero_add]
  rfl
