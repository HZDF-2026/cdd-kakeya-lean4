import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

-- test 9: Finset.sum_sub_distrib
example (s : Finset Nat) (f g : Nat → Real) :
    ∑ i ∈ s, (f i - g i) = (∑ i ∈ s, f i) - ∑ i ∈ s, g i := Finset.sum_sub_distrib

-- test 10: sum_const to card cast
example (s : Finset Nat) : ∑ i ∈ s, (1 : Real) = (s.card : Real) := by
  rw [Finset.sum_const, Nat.smul_one_eq_cast]

-- test 11: sum_congr as rw
example (s : Finset Nat) (f g : Nat → Real) (h : ∀ i ∈ s, f i = g i) :
    ∑ i ∈ s, f i = ∑ i ∈ s, g i := Finset.sum_congr rfl (fun i hi => h i hi)

-- test 12: subtype coercion to Complex in arg
example (S : Finset Complex) (n : Nat)
    (hcos : ∀ j : S, 1 - 1 / 4 ≤ Real.cos ((n : Real) * Complex.arg (1 - (j : Complex)⁻¹)))
    (ρ : Complex) (hρ : ρ ∈ S) :
    (3 / 4 : Real) ≤ Real.cos ((n : Real) * Complex.arg (1 - ρ⁻¹)) := by
  have h0 := hcos ⟨ρ, hρ⟩
  have h34 : (1 : Real) - 1 / 4 = 3 / 4 := by norm_num
  rw [h34] at h0
  exact h0

-- test 13: field_simp for (3/4)*(4/3)*x = x
example (x : Real) : (3 / 4 : Real) * ((4 / 3) * (x + 1)) = x + 1 := by
  field_simp
  ring
