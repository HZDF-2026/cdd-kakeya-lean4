import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.MellinTransform
import Mathlib.Order.Interval.Finset.Nat

open ArithmeticFunction Chebyshev MeasureTheory LSeries Filter Asymptotics
open scoped Chebyshev LSeries.notation

#check @Finset.range_succ_eq_Icc_zero
#check @MeasureTheory.setIntegral_congr_fun
#check @MeasureTheory.setIntegral_zero
#check @MeasureTheory.setIntegral_union
#check @MeasureTheory.setIntegral_indicator
#check @mellin
#check @not_isPrimePow_zero
#check @tendsto_add_atTop_nat
#check @HasDerivAt.deriv
#check @vonMangoldt_apply
#check @Summable.hasSum
#check @Integrable.integrableOn
#check @MeasureTheory.IntegrableOn
#check @psi_eq_sum_Icc
#check @Complex.norm_cpow_eq_rpow_re_of_pos
#check @measurable_of_continuousOn_compl_singleton
#check @Chebyshev.psi_mono
#check @Monotone.measurable
#check @Complex.measurable_ofReal
#check @Measurable.aestronglyMeasurable
#check @MeasureTheory.Integrable.mono'
#check @integral_congr_ae
#check @integral_const_mul
#check @Asymptotics.IsBigO.trans_tendsto
#check @tendsto_rpow_neg_atTop
#check @tendsto_natCast_atTop_atTop
#check @tendsto_nhds_unique
#check @MeasureTheory.integrableAtFilter_rpow_atTop_iff
#check @IsBigO.integrableAtFilter
#check @hasDerivAt_ofReal_cpow_const
#check @Filter.Tendsto.congr'
#check @term_def₀
#check @LSeries_vonMangoldt_eq_deriv_riemannZeta_div
#check @HasSum.tendsto_sum_nat
example : (0:ℝ) < 1 := by norm_num
#check @Set.Ioc_union_Ioi
#check @psi_le_const_mul_self
#check @Complex.ofReal_mem_slitPlane
#check @ContinuousOn.cpow_const
#check @MeasurableSet.Ioi
example : (1:ℝ) ≤ 1 := le_rfl
#check @Complex.ofReal_sum
#check @Nat.floor_natCast
#check @ContinuousOn.locallyIntegrableOn
#check @LocallyIntegrableOn
#check @DifferentiableAt
#check @MeasureTheory.LocallyIntegrableOn.integrableOn_of_isBigO_atTop
