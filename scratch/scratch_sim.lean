import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Finset.Max

noncomputable section

namespace ScratchSim

open Complex Real Finset

/-- 余弦下方界: `cos x ≥ 1 - x²/2`. -/
lemma cos_ge_one_sub_half_sq (x : ℝ) : 1 - x ^ 2 / 2 ≤ Real.cos x :=
  Real.one_sub_sq_div_two_le_cos

/-- 鸽笼格子引理: `⌊N·fract x⌋` 落入 `[0, N)` 内. -/
private lemma floor_mul_fract_lt {N : ℕ} (hN : 0 < N) (x : ℝ) :
    (Int.floor ((N : ℝ) * Int.fract x)).toNat < N := by
  have hnn : 0 ≤ (N : ℝ) * Int.fract x :=
    mul_nonneg (by positivity) (Int.fract_nonneg x)
  have h1 : 0 ≤ Int.floor ((N : ℝ) * Int.fract x) := Int.floor_nonneg.mpr hnn
  have h2 : Int.floor ((N : ℝ) * Int.fract x) < (N : ℤ) := by
    rw [Int.floor_lt]
    have hfr0 : 0 ≤ Int.fract x := Int.fract_nonneg x
    have hfr1 : Int.fract x < 1 := Int.fract_lt_one x
    have hlt : (N : ℝ) * Int.fract x < (N : ℝ) := by
      have hc : (N : ℝ) * Int.fract x < (N : ℝ) * 1 :=
        mul_lt_mul_of_pos_left hfr1 (by exact_mod_cast hN)
      linarith
    exact_mod_cast hlt
  exact (Int.toNat_lt h1).mpr h2

theorem exists_simultaneous_cos_ge {ι : Type*} [Fintype ι] (θ : ι → ℝ)
    {ε : ℝ} (hε : 0 < ε) (Q : ℕ) :
    ∃ n : ℕ, Q ≤ n ∧ ∀ j, 1 - ε ≤ Real.cos ((n : ℝ) * θ j) := by
  classical
  set δ : ℝ := Real.sqrt (ε / (2 * Real.pi ^ 2)) with hδdef
  have hδpos : 0 < δ := Real.sqrt_pos.mpr (by positivity)
  set m := Fintype.card ι with hm
  obtain ⟨N, hNbig⟩ : ∃ N : ℕ, ((Q : ℝ) + 1) / δ < (N : ℝ) := exists_nat_gt _
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_le_of_lt (by positivity) hNbig
  have hNnat : 0 < N := by exact_mod_cast hNpos
  have hQN : ((Q : ℝ) + 1) / (N : ℝ) < δ := by
    rw [div_lt_iff₀ hNpos]
    have h1 : ((Q : ℝ) + 1) < (N : ℝ) * δ := (div_lt_iff₀ hδpos).mp hNbig
    linarith [mul_comm ((N : ℝ)) δ]
  -- 鸽笼映射: k ↦ (j ↦ ⌊N·{k·α j}⌋)
  set α : ι → ℝ := fun j => θ j / (2 * Real.pi) with hαdef
  set f : Fin (N ^ m + 1) → (ι → Fin N) :=
    fun k j => ⟨(Int.floor ((N : ℝ) * Int.fract ((k : ℝ) * α j))).toNat,
      floor_mul_fract_lt (by omega) ((k : ℝ) * α j)⟩ with hfdef
  have hcard : Fintype.card (ι → Fin N) < Fintype.card (Fin (N ^ m + 1)) := by
    rw [Fintype.card_pi, Fintype.card_fin, Fintype.card_fin]
    have h1 : ∏ _i : ι, N = N ^ m := by simp [← hm]
    rw [h1]
    exact Nat.lt_succ_self _
  obtain ⟨k₁, k₂, hne, hfe⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  -- 碰撞给出: 同格子 ⟹ floor 值相等
  have hfloor_eq : ∀ j, Int.floor ((N : ℝ) * Int.fract ((k₁ : ℝ) * α j)) =
      Int.floor ((N : ℝ) * Int.fract ((k₂ : ℝ) * α j)) := by
    intro j
    have hfj : f k₁ j = f k₂ j := congrFun hfe j
    have h1 : (Int.floor ((N : ℝ) * Int.fract ((k₁ : ℝ) * α j))).toNat =
        (Int.floor ((N : ℝ) * Int.fract ((k₂ : ℝ) * α j))).toNat := congrArg Fin.val hfj
    have h3 : 0 ≤ Int.floor ((N : ℝ) * Int.fract ((k₁ : ℝ) * α j)) :=
      Int.floor_nonneg.mpr (mul_nonneg (by positivity) (Int.fract_nonneg _))
    have h4 : 0 ≤ Int.floor ((N : ℝ) * Int.fract ((k₂ : ℝ) * α j)) :=
      Int.floor_nonneg.mpr (mul_nonneg (by positivity) (Int.fract_nonneg _))
    rw [← Int.toNat_of_nonneg h3, ← Int.toNat_of_nonneg h4]
    exact_mod_cast h1
  -- 同格子 ⟹ fract 差 < 1/N
  have hfrlt : ∀ j, |Int.fract ((k₁ : ℝ) * α j) - Int.fract ((k₂ : ℝ) * α j)| < 1 / (N : ℝ) := by
    intro j
    have hp := hfloor_eq j
    set x₁ : ℝ := (N : ℝ) * Int.fract ((k₁ : ℝ) * α j) with hx₁def
    set x₂ : ℝ := (N : ℝ) * Int.fract ((k₂ : ℝ) * α j) with hx₂def
    have h1 : ((Int.floor x₁ : ℤ) : ℝ) ≤ x₁ := Int.floor_le x₁
    have h2 : ((Int.floor x₂ : ℤ) : ℝ) ≤ x₂ := Int.floor_le x₂
    have h3 : x₁ < ((Int.floor x₁ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one x₁
    have h4 : x₂ < ((Int.floor x₂ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one x₂
    rw [← hp] at h2 h4
    have habs : |x₁ - x₂| < 1 := by
      rw [abs_sub_lt_iff]
      constructor <;> linarith
    have hmul : x₁ - x₂ = (N : ℝ) *
        (Int.fract ((k₁ : ℝ) * α j) - Int.fract ((k₂ : ℝ) * α j)) := by
      rw [hx₁def, hx₂def]; ring
    have habs2 : |x₁ - x₂| = (N : ℝ) *
        |Int.fract ((k₁ : ℝ) * α j) - Int.fract ((k₂ : ℝ) * α j)| := by
      rw [hmul, abs_mul, abs_of_pos hNpos]
    have hkey : |x₁ - x₂| / (N : ℝ) =
        |Int.fract ((k₁ : ℝ) * α j) - Int.fract ((k₂ : ℝ) * α j)| := by
      rw [habs2, mul_div_cancel_left₀ _ hNpos.ne']
    rw [← hkey]
    exact div_lt_div_of_pos_right habs hNpos
  -- 倍增基: n₀ 与整数部分 z (两个顺序分支对称)
  have hpigeon : ∃ n₀ : ℕ, 0 < n₀ ∧ ∃ z : ι → ℤ,
      ∀ j, |(n₀ : ℝ) * α j - ((z j : ℝ))| < 1 / (N : ℝ) := by
    rcases Nat.lt_or_ge k₁.val k₂.val with hlt | hge
    · refine ⟨k₂.val - k₁.val, by omega,
        fun j => ⌊(k₂ : ℝ) * α j⌋ - ⌊(k₁ : ℝ) * α j⌋, fun j => ?_⟩
      have h1 := hfrlt j
      rw [abs_sub_comm] at h1
      have hEq : ((k₂ : ℝ) - (k₁ : ℝ)) * α j -
          (((⌊(k₂ : ℝ) * α j⌋ - ⌊(k₁ : ℝ) * α j⌋ : ℤ) : ℝ)) =
          Int.fract ((k₂ : ℝ) * α j) - Int.fract ((k₁ : ℝ) * α j) := by
        rw [← Int.self_sub_floor, ← Int.self_sub_floor]
        push_cast
        ring
      rw [Nat.cast_sub hlt.le, hEq]
      exact h1
    · have hlt' : k₂.val < k₁.val :=
        Nat.lt_of_le_of_ne hge (fun h => hne ((Fin.val_eq_val _ _).mp h).symm)
      refine ⟨k₁.val - k₂.val, by omega,
        fun j => ⌊(k₁ : ℝ) * α j⌋ - ⌊(k₂ : ℝ) * α j⌋, fun j => ?_⟩
      have h1 := hfrlt j
      have hEq : ((k₁ : ℝ) - (k₂ : ℝ)) * α j -
          (((⌊(k₁ : ℝ) * α j⌋ - ⌊(k₂ : ℝ) * α j⌋ : ℤ) : ℝ)) =
          Int.fract ((k₁ : ℝ) * α j) - Int.fract ((k₂ : ℝ) * α j) := by
        rw [← Int.self_sub_floor, ← Int.self_sub_floor]
        push_cast
        ring
      rw [Nat.cast_sub hlt'.le, hEq]
      exact h1
  obtain ⟨n₀, hn₀pos, z, hz⟩ := hpigeon
  -- 倍增: n = (Q+1)·n₀
  have hkn₀ : Q + 1 ≤ (Q + 1) * n₀ := Nat.le_mul_of_pos_right _ hn₀pos
  have herr : ∀ j, |((((Q + 1) * n₀ : ℕ) : ℝ) * α j - ((((Q + 1) * z j : ℤ) : ℝ)))| < δ := by
    intro j
    have hzj := hz j
    have hcalc : ((((Q + 1) * n₀ : ℕ) : ℝ) * α j - ((((Q + 1) * z j : ℤ) : ℝ))) =
        ((Q + 1 : ℕ) : ℝ) * ((n₀ : ℝ) * α j - ((z j : ℝ))) := by
      push_cast
      ring
    rw [hcalc, abs_mul, abs_of_nonneg (by positivity)]
    have h1 : ((Q + 1 : ℕ) : ℝ) * |(n₀ : ℝ) * α j - ((z j : ℝ))| <
        ((Q + 1 : ℕ) : ℝ) * (1 / (N : ℝ)) :=
      mul_lt_mul_of_pos_left hzj (by positivity)
    have h2 : ((Q + 1 : ℕ) : ℝ) * (1 / (N : ℝ)) = ((Q : ℝ) + 1) / (N : ℝ) := by
      push_cast
      rw [mul_one_div]
    rw [h2] at h1
    exact lt_trans h1 hQN
  refine ⟨(Q + 1) * n₀, Nat.le_of_succ_le hkn₀, fun j => ?_⟩
  have hθα : (((Q + 1) * n₀ : ℕ) : ℝ) * θ j =
      2 * Real.pi * ((((Q + 1) * n₀ : ℕ) : ℝ) * α j) := by
    rw [hαdef]
    field_simp
  have hsplit : (((Q + 1) * n₀ : ℕ) : ℝ) * θ j =
      (2 * Real.pi * ((((Q + 1) * n₀ : ℕ) : ℝ) * α j - ((((Q + 1) * z j : ℤ) : ℝ)))) +
      ((((Q + 1) * z j : ℤ) : ℝ)) * (2 * Real.pi) := by
    rw [hθα]
    ring
  rw [hsplit, Real.cos_add_int_mul_two_pi]
  have heabs := herr j
  have hcosb := cos_ge_one_sub_half_sq
    (2 * Real.pi * ((((Q + 1) * n₀ : ℕ) : ℝ) * α j - ((((Q + 1) * z j : ℤ) : ℝ))))
  have hsq : (2 * Real.pi * ((((Q + 1) * n₀ : ℕ) : ℝ) * α j - ((((Q + 1) * z j : ℤ) : ℝ)))) ^ 2 ≤
      (2 * Real.pi * δ) ^ 2 := by
    refine sq_le_sq.mpr ?_
    have hL : |2 * Real.pi * ((((Q + 1) * n₀ : ℕ) : ℝ) * α j - ((((Q + 1) * z j : ℤ) : ℝ)))| =
        2 * Real.pi * |((((Q + 1) * n₀ : ℕ) : ℝ) * α j - ((((Q + 1) * z j : ℤ) : ℝ)))| := by
      rw [abs_mul, abs_of_pos (by positivity)]
    have hR : |2 * Real.pi * δ| = 2 * Real.pi * δ := by
      rw [abs_mul, abs_of_pos (by positivity), abs_of_pos hδpos]
    rw [hL, hR]
    exact mul_le_mul_of_nonneg_left heabs.le (by positivity)
  have hdelta : (2 * Real.pi * δ) ^ 2 / 2 = ε := by
    have h1 : δ ^ 2 = ε / (2 * Real.pi ^ 2) := by
      rw [hδdef]
      exact Real.sq_sqrt (by positivity)
    have h2 : (2 * Real.pi * δ) ^ 2 = 4 * Real.pi ^ 2 * δ ^ 2 := by ring
    rw [h2, h1]
    field_simp
    norm_num
  linarith [hcosb, hsq, hdelta]

end ScratchSim

end
