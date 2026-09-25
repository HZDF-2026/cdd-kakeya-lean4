import CddFormalization.RH_ExplicitFormula
import CddFormalization.RH_SpectralMeasure
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Order

open scoped Real Topology
open Complex Filter Set Metric

-- T1: identity theorem usage: zeta not locally zero
example (ρ : ℂ) (hρ : ∀ᶠ s in 𝓝 ρ, riemannZeta s = 0) : riemannZeta 2 = 0 := by
  rcases eq_or_ne ρ 1 with rfl | hρ1
  · have hboth : ∀ᶠ s in 𝓝 1, riemannZeta s = 0 ∧ riemannZeta s ≠ 0 :=
      hρ.and riemannZeta_eventually_ne_zero_nhds_one
    exact absurd (hboth.self_of_nhds).1 (hboth.self_of_nhds).2
  · have h1 : ρ ∈ ({1} : Set ℂ)ᶜ := by simp [hρ1]
    have h2 : (2 : ℂ) ∈ ({1} : Set ℂ)ᶜ := by simp
    exact analyticOn_riemannZeta.eqOn_of_preconnected_of_eventuallyEq
      (analyticOnNhd_const (v := (0 : ℂ)))
      (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected h1
      (hρ.mono fun s hs => hs) h2

-- T2: circle integral basic: ∮ (z - c)⁻¹ = 2πi
example (c : ℂ) (r : ℝ) (hr : r ≠ 0) : (∮ z in C(c, r), (z - c)⁻¹) = 2 * π * I := by
  exact circleIntegral.integral_sub_center_inv c hr

-- T3: Cauchy-Goursat for differentiable-on-ball functions
example (c : ℂ) (r : ℝ) (f : ℂ → ℂ) (hf : DiffContOnCl ℂ f (ball c r)) (hr : 0 ≤ r) :
    (∮ z in C(c, r), f z) = 0 := by
  exact hf.circleIntegral_eq_zero hr

-- T4: quotient differentiability (g'/g where g ≠ 0)
example (g : ℂ → ℂ) (hg : Differentiable ℂ g) (hg0 : ∀ z, g z ≠ 0) :
    Differentiable ℂ (fun z => deriv g z / g z) := by
  exact fun z => (hg.deriv z).div (hg z) (hg0 z)

-- T5: order extraction shape
example (ρ : ℂ) (hρ : riemannZeta ρ = 0) (hρ1 : ρ ≠ 1)
    (hfin : analyticOrderAt riemannZeta ρ ≠ ⊤) :
    ∃ (m : ℕ) (g : ℂ → ℂ), AnalyticAt ℂ g ρ ∧ g ρ ≠ 0 ∧
      ∀ᶠ s in 𝓝 ρ, riemannZeta s = (s - ρ) ^ m * g s := by
  have hA : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ (by simp [hρ1])
  obtain ⟨g, hg, hg0, heq⟩ :=
    (hA.analyticOrderAt_eq_natCast (n := analyticOrderNatAt riemannZeta ρ)).mp
      (Nat.cast_analyticOrderNatAt hfin).symm
  refine ⟨analyticOrderNatAt riemannZeta ρ, g, hg, hg0, ?_⟩
  filter_upwards [heq] with s hs
  rw [hs, smul_eq_mul]
