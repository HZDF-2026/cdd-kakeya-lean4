import CddFormalization.RH_ExplicitFormula
import CddFormalization.RH_SpectralMeasure
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

noncomputable section

namespace WeilProbe18

open RHMeasureTheory RHExplicitFormula RHSpectralMeasure Chebyshev ArithmeticFunction
open MeasureTheory LSeries Set Complex Filter
open scoped Chebyshev Topology ENNReal LSeries.notation

private lemma key_floor (u : ℝ) (n : ℕ) (h : ⌊Real.exp u⌋₊ < n) : Real.exp u < (n : ℝ) := by
  have h1 : Real.exp u < ((⌊Real.exp u⌋₊ : ℝ) + 1) := Nat.lt_floor_add_one (Real.exp u)
  have h2 : ((⌊Real.exp u⌋₊ : ℝ) + 1) ≤ (n : ℝ) := by
    have : ⌊Real.exp u⌋₊ + 1 ≤ n := by omega
    exact_mod_cast this
  linarith

def logPrimeMeasure : Measure ℝ :=
  Measure.sum fun n : ℕ =>
    (ENNReal.ofReal (Λ n)) • Measure.dirac (Real.log (n : ℝ))

-- T1: singleton atomic mass
example (m : ℕ) (hm : 2 ≤ m) :
    logPrimeMeasure ({Real.log (m : ℝ)} : Set ℝ) = ENNReal.ofReal (Λ m) := by
  classical
  have hlogm : (0 : ℝ) < Real.log (m : ℝ) := by
    apply Real.log_pos
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  rw [logPrimeMeasure, Measure.sum_apply _ (measurableSet_singleton _)]
  simp only [Measure.smul_apply, Measure.dirac_apply, Set.indicator_apply, Pi.one_apply,
    Set.mem_singleton_iff, smul_eq_mul, mul_ite_zero, mul_one, mul_zero]
  have hlog_inj : ∀ n : ℕ, n ≠ m → Real.log (n : ℝ) ≠ Real.log (m : ℝ) := by
    intro n hne
    by_cases hn2 : 2 ≤ n
    · have hposn : (0 : ℝ) < (n : ℝ) := by
        have : 0 < n := by omega
        exact_mod_cast this
      have hposm : (0 : ℝ) < (m : ℝ) := by
        have : 0 < m := by omega
        exact_mod_cast this
      intro h
      have h2 : Real.exp (Real.log (n : ℝ)) = Real.exp (Real.log (m : ℝ)) := by rw [h]
      rw [Real.exp_log hposn, Real.exp_log hposm] at h2
      exact hne (by exact_mod_cast h2)
    · have hn01 : n = 0 ∨ n = 1 := by omega
      rcases hn01 with rfl | rfl
      · rw [show Real.log ((0 : ℕ) : ℝ) = 0 by simp]
        exact (ne_of_gt hlogm).symm
      · rw [show Real.log ((1 : ℕ) : ℝ) = 0 by simp]
        exact (ne_of_gt hlogm).symm
  have hkey : ∀ n : ℕ,
      (if Real.log (n : ℝ) = Real.log (m : ℝ) then ENNReal.ofReal (Λ n) else 0)
        = if n = m then ENNReal.ofReal (Λ n) else 0 := by
    intro n
    by_cases hn : n = m
    · subst hn
      simp
    · rw [if_neg (hlog_inj n hn), if_neg hn]
  rw [tsum_congr hkey]
  rw [tsum_eq_sum (s := ({m} : Finset ℕ)) (fun n hn => by
    rw [Finset.mem_singleton] at hn
    rw [if_neg hn])]
  simp

-- T2: CDF characterization
example (u : ℝ) :
    logPrimeMeasure (Set.Iic u) = ENNReal.ofReal (ψ (Real.exp u)) := by
  classical
  set N := ⌊Real.exp u⌋₊ with hN
  have hpsi : ψ (Real.exp u) = ∑ n ∈ Finset.Icc 0 N, Λ n := by
    rw [Chebyshev.psi_eq_sum_Icc (Real.exp u), hN]
  rw [logPrimeMeasure, Measure.sum_apply _ measurableSet_Iic]
  simp only [Measure.smul_apply, Measure.dirac_apply, Set.indicator_apply, Pi.one_apply,
    Set.mem_Iic, smul_eq_mul, mul_ite_zero, mul_one, mul_zero]
  have hkey : ∀ n : ℕ,
      (if Real.log (n : ℝ) ≤ u then ENNReal.ofReal (Λ n) else 0)
        = if n ≤ N then ENNReal.ofReal (Λ n) else 0 := by
    intro n
    by_cases hn0 : n = 0
    · subst hn0
      simp [vonMangoldt_eq_zero_iff.mpr not_isPrimePow_zero]
    · have hpos : (0 : ℝ) < (n : ℝ) := by
        have : 0 < n := Nat.pos_of_ne_zero hn0
        exact_mod_cast this
      by_cases hn : n ≤ N
      · rw [if_pos hn]
        have hnle : (n : ℝ) ≤ Real.exp u := by
          have h1 : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn
          exact h1.trans (Nat.floor_le (Real.exp_nonneg u))
        rw [if_pos ((Real.log_le_log hpos hnle).trans_eq (Real.log_exp u))]
      · rw [if_neg hn]
        have hnotlog : ¬ (Real.log (n : ℝ) ≤ u) := by
          intro hle
          have hnle : (n : ℝ) ≤ Real.exp u := by
            rw [← Real.exp_log hpos]
            exact Real.exp_le_exp.mpr hle
          have hgt : Real.exp u < (n : ℝ) := key_floor u n (by omega)
          exact absurd hgt (not_lt.mpr hnle)
        rw [if_neg hnotlog]
  rw [tsum_congr hkey]
  rw [tsum_eq_sum (s := Finset.Icc 0 N) (fun n hn => by
    have h : ¬ (n ≤ N) := by
      intro hc
      exact hn (Finset.mem_Icc.mpr ⟨Nat.zero_le n, hc⟩)
    exact if_neg h)]
  rw [Finset.sum_congr rfl (fun n hn => if_pos (Finset.mem_Icc.mp hn).2)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => vonMangoldt_nonneg (n := n)), ← hpsi]

-- T3: Laplace-L-series dictionary
theorem integral_exp_logPrimeMeasure_eq_neg_logDeriv (s : ℂ) (hs : 1 < s.re) :
    ∫ u : ℝ, Complex.exp (-s * u) ∂logPrimeMeasure
      = -deriv riemannZeta s / riemannZeta s := by
  classical
  have hcpow : ∀ n : ℕ, n ≠ 0 → Complex.exp (-s * Real.log (n : ℝ)) = ((n : ℂ) ^ (-s)) := by
    intro n hn
    have hne : ((n : ℂ)) ≠ 0 := by exact_mod_cast hn
    rw [Complex.cpow_def_of_ne_zero hne, Complex.ofReal_log (Nat.cast_nonneg (α := ℝ) n)]
    rw [mul_comm]
    rfl
  have hpt : ∀ n : ℕ,
      (ENNReal.ofReal (Λ n)).toReal • Complex.exp (-s * Real.log (n : ℝ))
        = LSeries.term (fun k => (Λ k : ℂ)) s n := by
    intro n
    rw [ENNReal.toReal_ofReal (vonMangoldt_nonneg (n := n))]
    by_cases hn : n = 0
    · subst hn
      simp [vonMangoldt_eq_zero_iff.mpr not_isPrimePow_zero]
    · rw [LSeries.term_def₀ (f := fun k => (Λ k : ℂ))
        (by simp [vonMangoldt_eq_zero_iff.mpr not_isPrimePow_zero]) s n, hcpow n hn]
      rfl
  have hsumm : Summable fun n : ℕ =>
      (ENNReal.ofReal (Λ n)).toReal * ‖Complex.exp (-s * Real.log (n : ℝ))‖ := by
    have h' : Summable fun n : ℕ => LSeries.term (fun k => (Λ k : ℂ)) s n :=
      LSeriesSummable_vonMangoldt hs
    have h2 : Summable fun n : ℕ =>
        (ENNReal.ofReal (Λ n)).toReal • Complex.exp (-s * Real.log (n : ℝ)) :=
      h'.congr (fun n => (hpt n).symm)
    refine h2.norm.congr (fun n => ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  rw [logPrimeMeasure]
  rw [integral_sum_dirac_eq_tsum (c := fun n : ℕ => ENNReal.ofReal (Λ n))
      (x := fun n : ℕ => Real.log (n : ℝ)) (f := fun u : ℝ => Complex.exp (-s * u))
      (fun n => ENNReal.ofReal_ne_top) hsumm]
  rw [tsum_congr hpt]
  rw [(LSeriesSummable_vonMangoldt hs).LSeriesHasSum.tsum_eq]
  rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]

end WeilProbe18

end
