import CddFormalization.RH_ExplicitFormula
import CddFormalization.RH_SpectralMeasure
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

open MeasureTheory ArithmeticFunction Chebyshev LSeries Filter Complex
open scoped Chebyshev ENNReal

-- ============ P1: 测度和 × Dirac 积分公式 ============
#check @integral_sum_dirac_eq_tsum
#check @integrable_sum_dirac
#check @lintegral_sum_measure
#check @Measure.sum_apply
#check @Measure.dirac_apply
#check @Measure.smul_apply
#check @Measure.sum

-- ============ P2: cpow / exp / log 字典 ============
#check @Complex.exp
#check @Complex.cpow_def
#check @Complex.ofReal_log
#check @Complex.norm_ofReal
#check @Complex.real_smul
#check @Real.log_zero
#check @Real.log_pos

-- ============ P3: LSeries von Mangoldt ============
#check @LSeries.term_def₀
#check @ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
#check @ArithmeticFunction.LSeriesSummable_vonMangoldt
#check @vonMangoldt_apply
#check @vonMangoldt_nonneg

-- ============ P4: 解析阶数 ============
#check @analyticOrderNatAt
#check @AnalyticAt.analyticOrderAt_eq_natCast
#check @analyticOrderAt_eq_top
#check @AnalyticAt.analyticOrderAt_ne_top
#check @DifferentiableAt.analyticAt
#check @riemannZeta_two
#check @isConnected_compl_singleton_of_one_lt_rank

-- ============ P5: s=1 残差字典 ============
#check @log_deriv_riemannZeta_add_inv_sub_sub_isLittleO
#check @log_deriv_riemannZeta_eq_neg_inv_sub_add
#check @riemannZeta_residue_one

-- ============ P6: Chebyshev ψ ============
#check @psi_eq_sum_Icc
#check @psi_le_const_mul_self
#check @psi_nonneg
#check @psi_eq_zero_of_le_one

-- ============ P7: 既有接口 ============
#check @RHExplicitFormula.neg_logDeriv_eq_mul_mellin
#check @RHSpectralMeasure.stripZeros_finite
#check @RHMeasureTheory.nontrivialZeros

-- ============ P8: 倾向性工具 ============
#check @Filter.Tendsto.mul
#check @IsLittleO
#check @Asymptotics.isLittleO_iff_tendsto'
#check @tendsto_norm_zero_iff
#check @Filter.EventuallyEq.deriv_eq
#check @summable_norm_iff

-- ============ P9: 测试性小实例 ============
noncomputable def probeMeasure : Measure ℝ :=
  Measure.sum (fun n : ℕ => (ENNReal.ofReal (vonMangoldt n)) • Measure.dirac (Real.log n))

example (T : ℝ) : probeMeasure (Set.Iic T) < ∞ := by
  sorry

example (s : ℂ) (hs : 1 < s.re) :
    ∫ x : ℝ, Complex.exp (-s * x) ∂probeMeasure
      = ∑' n : ℕ, (vonMangoldt n : ℝ) • Complex.exp (-s * Real.log n) := by
  sorry

example (n : ℕ) (s : ℂ) : (n : ℂ) ^ (-s) = Complex.exp (-s * (Real.log n : ℂ)) := by
  sorry

example (ρ : ℂ) (hρ : ρ ≠ 1) : AnalyticAt ℂ riemannZeta ρ :=
  (differentiableAt_riemannZeta hρ).analyticAt

example : IsPreconnected ({(1 : ℂ)}ᶜ : Set ℂ) :=
  (isConnected_compl_singleton_of_one_lt_rank (by simp)).isPreconnected

example (ρ : ℂ) (hρ : ρ ∈ nontrivialZeros) : ¬ ∀ᶠ z in 𝓝 ρ, riemannZeta z = 0 := by
  sorry
