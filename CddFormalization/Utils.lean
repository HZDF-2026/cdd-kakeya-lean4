/-! # CDD Formalization Shared Utilities

    Shared helper lemmas for Int arithmetic used across multiple modules.
    Extracted from T1_SCCO.lean and T2_ReactiveFluid.lean to eliminate duplication.

    Mathlib-free: uses only `omega` and core Lean4 tactics.
-/

/-- If a > 0 and b ≥ c, then a * b ≥ a * c. -/
theorem mul_pos_le {a b c : Int} (ha : a > 0) (hbc : b ≥ c) :
    a * b ≥ a * c := by
  have h_diff : b - c ≥ 0 := by omega
  have h_prod : a * (b - c) ≥ 0 := by
    by_cases hz : b - c = 0
    · rw [hz, Int.mul_zero]; omega
    · have h_pos : b - c > 0 := by omega
      have := Int.mul_pos ha h_pos
      omega
  rw [Int.mul_sub] at h_prod
  omega

/-- If a > 0 and b > c, then a * b > a * c (strict version). -/
theorem mul_pos_lt {a b c : Int} (ha : a > 0) (hbc : b > c) :
    a * b > a * c := by
  have h_diff : b - c > 0 := by omega
  have h_prod : a * (b - c) > 0 := Int.mul_pos ha h_diff
  rw [Int.mul_sub] at h_prod
  omega