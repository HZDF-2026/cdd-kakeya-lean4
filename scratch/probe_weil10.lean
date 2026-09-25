import CddFormalization.RH_ExplicitFormula
import CddFormalization.RH_SpectralMeasure
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Analysis.Analytic.Order

open RHMeasureTheory RHExplicitFormula RHSpectralMeasure Chebyshev ArithmeticFunction
open MeasureTheory LSeries Set Complex Filter Metric
open scoped Chebyshev Topology ENNReal Real

#check @Finset.sum_sub_distrib
#check @Finset.sum_div
#check @Nat.smul_one_eq_cast

example (s : Finset ℂ) (hinv : ∀ ρ ∈ s, 1 - ρ ∈ s) :
    ∑ ρ ∈ s, ρ.re = ∑ ρ ∈ s, (1 - ρ).re :=
  Finset.sum_nbij' (fun ρ : ℂ => 1 - ρ) (fun ρ : ℂ => 1 - ρ) hinv hinv
    (fun ρ _ => sub_sub_cancel 1 ρ) (fun ρ _ => sub_sub_cancel 1 ρ)
    (fun ρ _ => by simp)

example (T : ℝ) (h : 1 - T = 5) : T = -4 := by linarith

example (T : ℝ) : |(1 : ℂ - (0 : ℂ)).im| = |(0 : ℂ).im| := by
  simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]

example (s : Finset ℂ) : ∑ ρ ∈ s, (1 : ℝ) = (s.card : ℝ) := by
  rw [Finset.sum_const, Nat.smul_one_eq_cast]

example (s : Finset ℂ) : ∑ ρ ∈ s, (1 / 2 : ℝ) = (s.card : ℝ) / 2 := by
  rw [Finset.sum_div, Finset.sum_const, Nat.smul_one_eq_cast]

example (s : Finset ℂ) :
    ∑ ρ ∈ s, (1 - ρ.re) = (∑ ρ ∈ s, 1) - ∑ ρ ∈ s, ρ.re := by
  exact Finset.sum_sub_distrib _ _
