import CddFormalization.RH_ExplicitFormula
import CddFormalization.RH_SpectralMeasure
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Analysis.Analytic.Order
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.ZetaZeros

open RHMeasureTheory RHExplicitFormula RHSpectralMeasure Chebyshev ArithmeticFunction
open MeasureTheory LSeries Set Complex Filter
open scoped Chebyshev Topology LSeries.notation

-- mellin 命名空间
#check @mellin
#check @mellinInv
#check @MellinConvergent
#check @VerticalIntegrable
#check @mellinInv_mellin_eq
#check @RHExplicitFormula.mellinConvergent_psi
#check @RHExplicitFormula.mellin_psi_eq

-- Mathlib ζ 零点集
#check @riemannZetaZeros
#check @IsCompact.inter_riemannZetaZeros_finite
#check @Set.Countable riemannZetaZeros

-- 解析性桥接
#check @analyticAt_iff_eventually_differentiableAt
#check @DifferentiableOn.analyticOnNhd
#check @differentiableOn_riemannZeta

-- 阶数 API
#check @analyticOrderAt
#check @AnalyticAt.analyticOrderAt_eq_natCast
#check @AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff
#check @analyticOrderAt_eq_top

-- ζ 残差字典
#check @riemannZeta_eq_inv_sub_mul
#check @deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add
#check @differentiable_riemannZeta₁
#check @riemannZeta₁_one
#check @riemannZeta_two_eq_pow_pi_div_six

-- 围道积分
#check @Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
#check @Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
#check @Complex.circleIntegral_div_sub_of_differentiable_on_off_countable
#check @circleIntegral.integral_sub_center_inv
#check @circleIntegral.integral_congr

-- Finset 求和双射
#check @Set.Finite.toFinset
#check @Set.mem_toFinset
#check @Finset.sum_nbij

-- 集合积分
#check @MeasureTheory.integral_Ici_eq_integral_Ioi
#check @MeasureTheory.integral_Ioi_eq_integral_Ici
#check @MeasureTheory.integrableOn_Ici_iff_integrableOn_Ioi
#check @intervalIntegral.integral_eq_sub_of_hasDerivAt

-- cpow 恒等式验证 (n ≥ 1)
example (n : ℕ) (hn : 0 < n) (s : ℂ) :
    ((n : ℂ)) ^ (-s) = Complex.exp (-s * (Real.log (n : ℝ) : ℂ)) := by
  have hne : ((n : ℂ)) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Complex.cpow_def_of_ne_zero hne, Complex.ofReal_log (Nat.cast_nonneg (α := ℝ) n)]
  rw [mul_comm]
  rfl

-- LSeries 项与原子质量换算
example (n : ℕ) (s : ℂ) (hn : 0 < n) :
    ‖Complex.exp (-s * (Real.log (n : ℝ) : ℂ))‖ = (n : ℝ) ^ (-(s.re)) := by
  rw [Complex.norm_exp]
  have hre : (-s * (Real.log (n : ℝ) : ℂ)).re = -s.re * Real.log (n : ℝ) := by
    simp [Complex.mul_re]
  rw [hre, ← Real.rpow_def_of_pos (by exact_mod_cast hn) (-s.re), Real.exp_log (by exact_mod_cast hn)]

-- ζ₁ 残差代数恒等式 (节点 19 核心)
example (s : ℂ) (hs1 : s ≠ 1) (hsz : riemannZeta₁ s ≠ 0) :
    deriv riemannZeta s / riemannZeta s
      = -((s - 1)⁻¹) + deriv riemannZeta₁ s / riemannZeta₁ s := by
  rw [deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hs1, riemannZeta_eq_inv_sub_mul hs1]
  field_simp
  ring
