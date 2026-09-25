import CddFormalization.RH_ExplicitFormula
import CddFormalization.RH_SpectralMeasure
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

open MeasureTheory ArithmeticFunction Chebyshev LSeries Filter Complex
open scoped Chebyshev ENNReal

-- ============ P1: 解析性桥接 (节点 19) ============
#check @AnalyticAt.differentiableAt
#check @AnalyticAt.continuousAt
#check @AnalyticAt.deriv
#check @AnalyticAt.exists_ball_analyticOnNhd
#check @analyticOn_riemannZeta

-- ============ P2: 阶数 API (节点 19) ============
#check @AnalyticAt.analyticOrderAt_eq_natCast
#check @Nat.cast_analyticOrderNatAt
#check @analyticOrderAt_ne_zero
#check @analyticOrderAt_eq_top

-- ============ P3: 导数计算 (节点 19) ============
#check @Filter.EventuallyEq.deriv_eq
#check @HasDerivAt.pow
#check @HasDerivAt.mul
#check @HasDerivAt.sub_const
#check @hasDerivAt_id

-- ============ P4: 残差渐近 (节点 19) ============
#check @isLittleO_iff_tendsto'
#check @log_deriv_riemannZeta_add_inv_sub_sub_isLittleO

-- ============ P5: ENNReal 字典 (节点 18) ============
#check @ENNReal.ofReal_ne_top
#check @ENNReal.toReal_ofReal
#check @ENNReal.ofReal_sum
#check @ENNReal.ofReal_mul

-- ============ P6: LSeries / tsum (节点 18) ============
#check @LSeries_eq_tsum
#check @Summable.congr
#check @Summable.norm
#check @tsum_congr

-- ============ P7: 复分析字典 (节点 18/21) ============
#check @Complex.norm_exp
#check @Complex.norm_real
#check @Complex.cpow_def
#check @ofReal_log
#check @Complex.real_smul
#check @Complex.mul_re
#check @Complex.exp_injective

-- ============ P8: 实渐近 (节点 21) ============
#check @Real.rpow_def
#check @Real.tendsto_rpow_atTop
#check @Real.rpow_sub
#check @Real.rpow_neg
#check @Real.exp_log
#check @Real.log_exp

-- ============ P9: 拓扑/测度 (节点 18/20) ============
#check @Measure.sum_apply
#check @Set.indicator_apply
#check @isDiscrete_riemannZetaZeros
#check @IsDiscrete
#check @Measure.dirac_apply
#check @Measure.smul_apply

-- ============ P10: ψ 接口 ============
#check @psi_eq_sum_Icc
#check @psi_eq_zero_of_le_one
#check @riemannZeta_conj
#check @zero_symmetry
#check @RHSpectralMeasure.stripZeros_finite
