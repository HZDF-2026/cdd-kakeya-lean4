import CddFormalization.RH_WeakConvergence
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open scoped ENNReal
open MeasureTheory Set RHMeasureTheory RHWeakConvergence Complex Filter

-- probe 1: measure_univ on probability coercion
example (ν : ProbabilityMeasure ℝ) : (ν : Measure ℝ) univ = 1 := measure_univ

-- probe 2: mul_le_mul_left'
example (a b c : ℝ≥0∞) (h : b ≤ c) : a * b ≤ a * c := mul_le_mul_left' h a

-- probe 3: ENNReal.mul_pos
example (a b : ℝ≥0∞) (ha : a ≠ 0) (hb : b ≠ 0) : 0 < a * b := ENNReal.mul_pos ha hb

-- probe 4/5: inv_pos / inv_ne_zero
example (a : ℝ≥0∞) (h : a ≠ ∞) : 0 < a⁻¹ := ENNReal.inv_pos.2 h
example (a : ℝ≥0∞) (h : a ≠ ∞) : a⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 h

-- probe 6: coe_inv
example (r : ℝ≥0) (h : r ≠ 0) : (r⁻¹ : ℝ≥0∞) = (r : ℝ≥0∞)⁻¹ := ENNReal.coe_inv h

-- probe 7: normalize Measure-level application chain
example (μ : FiniteMeasure ℝ) (h : μ ≠ 0) (s : Set ℝ) :
    ((μ.normalize : Measure ℝ) s) = ((μ.mass⁻¹ : ℝ≥0∞) * (μ : Measure ℝ) s) := by
  rw [μ.toMeasure_normalize_eq_of_nonzero h]
  exact Measure.coe_nnreal_smul_apply _ _ _

-- probe 8: FiniteMeasure.ennreal_mass
example (μ : FiniteMeasure ℝ) : (μ.mass : ℝ≥0∞) = (μ : Measure ℝ) univ := μ.ennreal_mass

-- probe 9: dirac on complement of singleton
example (a : ℝ) : (Measure.dirac a) ({a}ᶜ) = 0 := by
  rw [Measure.dirac_apply]
  exact Set.indicator_of_notMem (by simp) _

-- probe 10: le_div_iff_mul_le
example (a b c : ℝ≥0∞) (h0 : b ≠ 0) (ht : b ≠ ∞) (h : a * b ≤ c) : a ≤ c / b :=
  (ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl ht)).mpr h

-- probe 11: inv_mul_cancel
example (a : ℝ≥0∞) (h0 : a ≠ 0) (h1 : a ≠ ∞) : a⁻¹ * a = 1 := ENNReal.inv_mul_cancel h0 h1

-- probe 12: div_eq_inv_mul
example (a b : ℝ≥0∞) : a / b = b⁻¹ * a := ENNReal.div_eq_inv_mul

-- probe 13: pos_iff_ne_zero
example (a : ℝ≥0∞) : 0 < a ↔ a ≠ 0 := pos_iff_ne_zero

-- probe 14: tendsto const
example : Tendsto (fun _ : ℝ => (0 : ℝ≥0∞)) atTop (𝓝 0) := tendsto_const_nhds

-- probe 15: diracProba coercion rfl
example : ((diracProba (1 / 2 : ℝ)) : Measure ℝ) = Measure.dirac (1 / 2 : ℝ) := rfl

-- probe 16: rw probability equality under coercion
example (R : ℝ) (hne : (truncatedZeros R).Nonempty) :
    (truncatedProjectedMeasure R : Measure ℝ) = ((truncatedReFM R).normalize : Measure ℝ) := by
  rw [truncatedProjectedMeasure_of_nonempty hne]

-- probe 17: count lemmas
example (s : Set ℂ) (h : s = ∅) : Measure.count s = 0 := Measure.count_eq_zero_iff.mpr h
example (z : ℂ) : Measure.count ({z} : Set ℂ) = 1 := Measure.count_singleton z

-- probe 18: mass relation to zeroCount via truncatedReMeasure_apply
example (R : ℝ) : ((truncatedReFM R).mass : ℝ≥0∞) = zeroCount R := by
  rw [FiniteMeasure.ennreal_mass, truncatedReMeasure_apply R MeasurableSet.univ, zeroCount]
  simp

-- probe 19: coe_eq_zero
example (r : ℝ≥0) : (r : ℝ≥0∞) = 0 ↔ r = 0 := ENNReal.coe_eq_zero
