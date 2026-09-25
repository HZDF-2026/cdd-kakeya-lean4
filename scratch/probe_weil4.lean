import CddFormalization.RH_ExplicitFormula
import CddFormalization.RH_SpectralMeasure
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

open RHMeasureTheory RHExplicitFormula RHSpectralMeasure Chebyshev ArithmeticFunction MeasureTheory LSeries
open Filter Complex Real Set

-- ============ 确认级 ============
#check @AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
#check @isConnected_compl_singleton_of_one_lt_rank
#check @AnalyticAt.eventually_analyticAt
#check @ContinuousAt.eventually_ne
#check @AnalyticAt.analyticOrderNatAt_eq_iff
#check @Filter.EventuallyEq.deriv_eq
#check @HasDerivAt.pow
#check @HasDerivAt.mul
#check @Metric.eventually_nhds_iff_ball
#check @ContinuousAt.div
#check @tendsto_nhds_unique
#check @Finset.sum_erase
#check @integral_congr
#check @riemannZeta_ne_zero_of_one_le_re
#check @log_deriv_riemannZeta_add_inv_sub_sub_isLittleO
#check @mellinInv
#check @VerticalIntegrable
#check @mellinInv_mellin_eq
#check @mellinConvergent_psi

-- ============ 候选级 (可能不存在) ============
#check @Filter.Tendsto.congr'
#check @AnalyticAt.deriv
#check @continuousAt_finset_sum
#check @Filter.Tendsto.finset_sum
#check @ContinuousAt.sum
