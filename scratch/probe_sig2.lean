import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Finset.Max

noncomputable section

#check @mul_div_cancel₀
#check @mul_div_cancel_left₀
#check @mul_div_assoc'
#check @div_lt_iff₀
#check @div_le_div_iff
#check @Set.mem_iUnion₂
#check @pow_pos
#check @Real.pi_pos
#check @Rat.pos
#check @div_mul_cancel_left₀
#check @abs_of_pos
#check @sq_pos_of_pos
#check @Nat.cast_pos
#check @two_pos
example (n : ℕ) (h : 0 < n) : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h
example (d : ℕ) (h : 0 < d) : (d : ℝ) ≠ 0 := by exact_mod_cast h.ne'
