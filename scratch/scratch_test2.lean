import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

-- branch 1 mechanism: beta-redex matching through rw, cast_sub, self_sub_floor
example (n : Nat) (α : Nat → Real) (k₁ k₂ : Fin n) (j : Nat)
    (hlt : (k₁ : Nat) < (k₂ : Nat))
    (h1 : |Int.fract ((k₂ : Real) * α j) - Int.fract ((k₁ : Real) * α j)| < (1 : Real)) :
    |(((k₂ : Nat) - (k₁ : Nat) : Nat) : Real) * α j -
      (((fun j => ⌊(k₂ : Real) * α j⌋ - ⌊(k₁ : Real) * α j⌋) j : Int) : Real)| < 1 := by
  have hEq : ((k₂ : Real) - (k₁ : Real)) * α j -
      (((⌊(k₂ : Real) * α j⌋ - ⌊(k₁ : Real) * α j⌋ : Int) : Real)) =
      Int.fract ((k₂ : Real) * α j) - Int.fract ((k₁ : Real) * α j) := by
    rw [← Int.self_sub_floor, ← Int.self_sub_floor]
    push_cast
    ring
  rw [Nat.cast_sub hlt.le, hEq]
  exact h1

-- branch 2: Fin.val_eq_val for strictness
example (n : Nat) (k₁ k₂ : Fin n) (hne : k₁ ≠ k₂) (hge : (k₁ : Nat) ≥ (k₂ : Nat)) :
    (k₂ : Nat) < (k₁ : Nat) :=
  Nat.lt_of_le_of_ne hge (fun h => hne ((Fin.val_eq_val _ _).mp h).symm)

-- lt_div_iff₀ form
example (a c : Real) (hc : 0 < c) (h : a * c < 1) : a < 1 / c := (lt_div_iff₀ hc).mpr h

-- hθα field_simp alone
example (n : Nat) (θ : Nat → Real) (j n' : Nat)
    (hαdef : (fun j => θ j / (2 * Real.pi)) = (fun j => θ j / (2 * Real.pi))) :
    ((n' : Real)) * θ j = 2 * Real.pi * (((n' : Real)) * ((fun j => θ j / (2 * Real.pi)) j)) := by
  rw [show ((fun j => θ j / (2 * Real.pi)) j) = θ j / (2 * Real.pi) from rfl]
  field_simp
