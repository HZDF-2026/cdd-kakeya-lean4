import CddFormalization.RH_ExplicitFormula
import CddFormalization.RH_SpectralMeasure
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Analysis.Analytic.Order
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

open RHMeasureTheory RHExplicitFormula RHSpectralMeasure Chebyshev ArithmeticFunction
open MeasureTheory LSeries Set Complex Filter
open scoped Chebyshev Topology LSeries.notation

-- ============ 节点 18: 素数侧字典 ============

#check @Complex.norm_exp
#check @Complex.ofReal_log
#check @Complex.cpow_def_of_ne_zero
#check @Real.rpow_def_of_pos
#check @Real.exp_log
#check @Real.log_exp
#check @Real.log_pos

#check @Chebyshev.psi_eq_sum_Icc
#check @vonMangoldt_nonneg
#check @ArithmeticFunction.LSeriesSummable_vonMangoldt
#check @ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
#check @LSeries.term_def₀
#check @LSeries.norm_term_eq
#check @LSeriesSummable

#check @MeasureTheory.integral_sum_dirac_eq_tsum
#check @MeasureTheory.Measure.sum_apply
#check @ENNReal.ofReal_ne_top

-- cpow 对数恒等式: (n : ℂ) ^ (-s) = exp (-s * log n) for n ≥ 1
example (n : ℕ) (hn : 0 < n) (s : ℂ) :
    ((n : ℂ)) ^ (-s) = Complex.exp (-s * (Real.log (n : ℝ) : ℂ)) := by
  have hne : ((n : ℂ)) ≠ 0 := by positivity
  rw [Complex.cpow_def_of_ne_zero hne]
  rw [Complex.ofReal_log (Nat.cast_nonneg (α := ℝ) n)]
  rw [mul_comm]
  rfl

-- norm 恒等式: ‖exp (-s * log n)‖ = n ^ (-s.re)
example (n : ℕ) (s : ℂ) :
    ‖Complex.exp (-s * (Real.log (n : ℝ) : ℂ))‖ = (n : ℝ) ^ (-(s.re)) := by
  rw [Complex.norm_exp]
  have hre : (-s * (Real.log (n : ℝ) : ℂ)).re = -s.re * Real.log (n : ℝ) := by
    simp [Complex.mul_re]
  rw [hre]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [← Real.rpow_def_of_pos (by exact_mod_cast hn) (-s.re)]
    rw [Real.exp_log (by exact_mod_cast hn)]

-- ============ 节点 19: 残差字典 ============

#check @riemannZeta_eq_inv_sub_mul
#check @riemannZeta₁
#check @riemannZeta₀
#check @riemannZeta_one_ne_zero
#check @ZetaAsymp.riemannZeta_eq_inv_sub_add
#check @ZetaAsymp.log_deriv_riemannZeta_add_inv_sub_sub_isLittleO

-- 解析延拓: 两个函数在挖点集上相等则导数相等
#check @Filter.EventuallyEq.deriv_eq
#check @isOpen_compl_singleton
#check @isConnected_compl_singleton_of_one_lt_rank

-- 零点阶数分解
#check @AnalyticAt.orderAt
#check @analyticOrderAt
#check @AnalyticAt.exists_eventuallyEq_pow_smul_nonzero

-- 围道积分
#check @MeasureTheory.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
#check @CircleIntegral.integral_eq_zero_of_differentiable_on

-- ============ 节点 20: 截断零点集 ============

#check @Set.Finite.toFinset
#check @Finset.mem_toFinset
#check @Finset.sum_nbij
#check @RHExplicitFormula.zero_symmetry
#check @RHSpectralMeasure.stripZeros_finite
#check @RHMeasureTheory.nontrivialZeros
#check @measurableSet_nontrivialZeros

-- ============ 节点 21: Mellin 反演 ============

#check @MeasureTheory.mellin
#check @MeasureTheory.mellinInv
#check @MeasureTheory.MellinConvergent
#check @MeasureTheory.VerticalIntegrable
#check @MeasureTheory.mellinInv_mellin_eq

-- 区间积分 / 反常积分
#check @intervalIntegral.integral_eq_sub_of_hasDerivAt
#check @MeasureTheory.integral_Ici_eq_integral_Ioi
#check @MeasureTheory.integrableOn_Ici_iff_integrableOn_Ioi
