import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Finset.Max

noncomputable section

namespace RHLiCriterion

/-! ## 第 4 节: 三个辅助引理 (修复版) -/

/-- 余弦下方界: `cos x ≥ 1 - x²/2`. -/
lemma cos_ge_one_sub_half_sq (x : ℝ) : 1 - x ^ 2 / 2 ≤ Real.cos x :=
  Real.one_sub_sq_div_two_le_cos

/-- 无理数的 Dirichlet 逼近具有任意大分母.

    由逼近集无限 (`Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational`)
    反证: 若分母有界, 则逼近被 absorbed 到有限个分母纤维, 每个纤维
    落在有界整数区间故有限. -/
theorem exists_large_den_approx {α : ℝ} (hα : Irrational α) (Q : ℕ) :
    ∃ q : ℚ, Q < q.den ∧ |α - q| < 1 / (q.den : ℝ) ^ 2 := by
  by_contra hcon
  rw [not_exists] at hcon
  have hSinf : {q : ℚ | |α - q| < 1 / (q.den : ℝ) ^ 2}.Infinite :=
    Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hα
  have hSfin : {q : ℚ | |α - q| < 1 / (q.den : ℝ) ^ 2}.Finite := by
    have hsub : {q : ℚ | |α - q| < 1 / (q.den : ℝ) ^ 2} ⊆
        ⋃ d ∈ Set.Icc (1 : ℕ) Q, {q : ℚ | q.den = d ∧ |α - q| < 1 / (q.den : ℝ) ^ 2} := by
      intro q hq
      have hq' : |α - q| < 1 / (q.den : ℝ) ^ 2 := hq
      have hd : q.den ≤ Q := by
        by_contra hd'
        exact hcon q ⟨by omega, hq'⟩
      exact Set.mem_iUnion₂.mpr ⟨q.den, ⟨q.pos, hd⟩, ⟨rfl, hq'⟩⟩
    refine Set.Finite.subset ?_ hsub
    refine Set.Finite.biUnion (Set.finite_Icc 1 Q) ?_
    intro d hdIcc
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hdIcc.1
    have hd0 : (0 : ℝ) < d := by linarith
    have hdne : (d : ℝ) ≠ 0 := ne_of_gt hd0
    have hfib : {q : ℚ | q.den = d ∧ |α - q| < 1 / (q.den : ℝ) ^ 2} ⊆
        (fun n : ℤ => (n : ℚ) / (d : ℚ)) '' {n : ℤ | |α * (d : ℝ) - (n : ℝ)| < 1} := by
      intro q hq
      obtain ⟨hden, hq2⟩ := hq
      have happ : |α - q| < 1 / (d : ℝ) ^ 2 := by rwa [hden] at hq2
      have hqc : (q : ℝ) = (q.num : ℝ) / (d : ℝ) := by
        rw [← hden]
        exact Rat.cast_def q
      rw [hqc] at happ
      refine ⟨q.num, ?_, ?_⟩
      · show |α * (d : ℝ) - (q.num : ℝ)| < 1
        have hEq : (α - (q.num : ℝ) / (d : ℝ)) * (d : ℝ) =
            α * (d : ℝ) - (q.num : ℝ) := by
          rw [sub_mul, div_mul_cancel₀ (q.num : ℝ) hdne]
        rw [← hEq, abs_mul, abs_of_pos hd0]
        have h1 : (d : ℝ) * |α - (q.num : ℝ) / (d : ℝ)| <
            (d : ℝ) * (1 / (d : ℝ) ^ 2) :=
          mul_lt_mul_of_pos_left happ hd0
        have h2 : (d : ℝ) * (1 / (d : ℝ) ^ 2) = 1 / (d : ℝ) := by
          field_simp
        rw [h2] at h1
        have h3 : 1 / (d : ℝ) ≤ 1 := by
          rw [div_le_iff₀ hd0]
          linarith
        linarith
      · rw [← hden]
        exact Rat.num_div_den q
    refine Set.Finite.subset (Set.Finite.image _ ?_) hfib
    have hint : {n : ℤ | |α * (d : ℝ) - (n : ℝ)| < 1} ⊆
        Set.Icc (Int.floor (α * (d : ℝ))) (Int.floor (α * (d : ℝ)) + 1) := by
      intro n hn
      have hn' : |α * (d : ℝ) - (n : ℝ)| < 1 := hn
      rw [abs_lt] at hn'
      have hn1 : Int.floor (α * (d : ℝ)) ≤ n := by
        have h1 : (Int.floor (α * (d : ℝ)) : ℝ) < (n : ℝ) + 1 := by
          have hf := Int.floor_le (α * (d : ℝ))
          linarith
        have h2 : (Int.floor (α * (d : ℝ)) : ℤ) < n + 1 := by exact_mod_cast h1
        exact Int.lt_add_one_iff.mp h2
      have hn2 : n ≤ Int.floor (α * (d : ℝ)) + 1 := by
        have h1 : (n : ℝ) < (Int.floor (α * (d : ℝ)) : ℝ) + 2 := by
          have hf := Int.lt_floor_add_one (α * (d : ℝ))
          linarith
        have h2 : n < Int.floor (α * (d : ℝ)) + 2 := by exact_mod_cast h1
        omega
      exact ⟨hn1, hn2⟩
    exact Set.Finite.subset (Set.finite_Icc _ _) hint
  exact hSinf hSfin

/-- **辐角回归定理 (无条件)**: 对任意角 θ 与 ε > 0, 存在任意大的 n
    使 `cos(nθ) ≥ 1 - ε`.

    这是 BL 反向论证的辐角回归核心:
    * 有理情形 θ/(2π) ∈ ℚ: 分母倍数下标精确命中 cos = 1;
    * 无理情形: Dirichlet 大分母逼近 (上一引理) 配合
      `cos x ≥ 1 - x²/2` 给出回归.

    两种情形合并为对**任意** θ 的无条件陈述. -/
theorem exists_ge_cos_ge {θ : ℝ} {ε : ℝ} (hε : 0 < ε) (Q : ℕ) :
    ∃ n : ℕ, Q ≤ n ∧ 1 - ε ≤ Real.cos ((n : ℝ) * θ) := by
  by_cases hrat : Irrational (θ / (2 * Real.pi))
  case pos =>
    -- 无理情形: Dirichlet 大分母逼近 + 余弦下方界
    obtain ⟨N₁, hN₁⟩ := exists_nat_gt (Real.pi * Real.sqrt (2 / ε))
    have hN₁pos : 0 < N₁ := by
      have h0 : (0 : ℝ) < Real.pi * Real.sqrt (2 / ε) :=
        mul_pos Real.pi_pos (Real.sqrt_pos.mpr (div_pos two_pos hε))
      exact_mod_cast h0.trans hN₁
    have hkey : ∀ n : ℕ, N₁ ≤ n → 2 * Real.pi ^ 2 / (n : ℝ) ^ 2 < ε := by
      intro n hn
      have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (hN₁pos.trans_le hn)
      have hn2 : (N₁ : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by exact_mod_cast hN₁pos.le) (by exact_mod_cast hn) 2
      have hcore : 2 * Real.pi ^ 2 < ε * (N₁ : ℝ) ^ 2 := by
        have hsq : (Real.pi * Real.sqrt (2 / ε)) ^ 2 < (N₁ : ℝ) ^ 2 :=
          pow_lt_pow_left₀ hN₁ (by positivity) (by norm_num)
        have hsqeq : (Real.pi * Real.sqrt (2 / ε)) ^ 2 = Real.pi ^ 2 * (2 / ε) := by
          rw [mul_pow, Real.sq_sqrt (by positivity)]
        have hineq : Real.pi ^ 2 * (2 / ε) < (N₁ : ℝ) ^ 2 := by rwa [hsqeq] at hsq
        have hmul : Real.pi ^ 2 * (2 / ε) * ε = 2 * Real.pi ^ 2 := by
          rw [mul_assoc, div_mul_cancel₀ _ (ne_of_gt hε)]
          ring
        nlinarith [hineq, hε]
      rw [div_lt_iff₀ (pow_pos hn' 2)]
      nlinarith [hcore, hn2]
    obtain ⟨q, hden, happ⟩ := exists_large_den_approx hrat (max N₁ (Q + 1))
    refine ⟨q.den, by omega, ?_⟩
    have hnpos : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.pos
    have hdne : ((q.den : ℕ) : ℝ) ≠ 0 := by exact_mod_cast q.pos.ne'
    have hqc : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := Rat.cast_def q
    have hstep : (q.den : ℝ) * |θ / (2 * Real.pi) - q| =
        |(q.den : ℝ) * (θ / (2 * Real.pi)) - (q.num : ℝ)| := by
      rw [hqc]
      have hEq : (q.den : ℝ) * (θ / (2 * Real.pi) - (q.num : ℝ) / (q.den : ℝ)) =
          (q.den : ℝ) * (θ / (2 * Real.pi)) - (q.num : ℝ) := by
        rw [mul_sub, mul_div_cancel₀ (q.num : ℝ) hdne]
      calc (q.den : ℝ) * |θ / (2 * Real.pi) - (q.num : ℝ) / (q.den : ℝ)| =
          |(q.den : ℝ) * (θ / (2 * Real.pi) - (q.num : ℝ) / (q.den : ℝ))| := by
            rw [abs_mul, abs_of_pos hnpos]
        _ = |(q.den : ℝ) * (θ / (2 * Real.pi)) - (q.num : ℝ)| := by rw [hEq]
    have hlt : |(q.den : ℝ) * (θ / (2 * Real.pi)) - (q.num : ℝ)| <
        1 / (q.den : ℝ) := by
      rw [← hstep]
      have h1 : (q.den : ℝ) * |θ / (2 * Real.pi) - q| <
          (q.den : ℝ) * (1 / (q.den : ℝ) ^ 2) :=
        mul_lt_mul_of_pos_left happ hnpos
      have h2 : (q.den : ℝ) * (1 / (q.den : ℝ) ^ 2) = 1 / (q.den : ℝ) := by
        field_simp
      rw [h2] at h1
      exact h1
    have hnθ : (q.den : ℝ) * θ = 2 * Real.pi *
        ((q.den : ℝ) * (θ / (2 * Real.pi)) - (q.num : ℝ)) + (q.num : ℝ) * (2 * Real.pi) := by
      have hEq : (q.den : ℝ) * (θ / (2 * Real.pi)) = ((q.den : ℝ) * θ) / (2 * Real.pi) :=
        mul_div_assoc' _ _ _
      rw [hEq, mul_sub, mul_div_cancel₀ _ (by positivity : (2 : ℝ) * Real.pi ≠ 0)]
      ring
    have hper : Real.cos (2 * Real.pi *
        ((q.den : ℝ) * (θ / (2 * Real.pi)) - (q.num : ℝ)) + (q.num : ℝ) * (2 * Real.pi)) =
        Real.cos (2 * Real.pi *
        ((q.den : ℝ) * (θ / (2 * Real.pi)) - (q.num : ℝ))) :=
      Real.cos_periodic.int_mul (q.num : ℤ)
        (2 * Real.pi * ((q.den : ℝ) * (θ / (2 * Real.pi)) - (q.num : ℝ)))
    rw [hnθ, hper]
    have hpd : 0 < 2 * Real.pi / (q.den : ℝ) := div_pos (by positivity) hnpos
    have habs1 : |2 * Real.pi * ((q.den : ℝ) * (θ / (2 * Real.pi)) - (q.num : ℝ))| =
        2 * Real.pi * |(q.den : ℝ) * (θ / (2 * Real.pi)) - (q.num : ℝ)| := by
      rw [abs_mul, abs_of_pos (by positivity)]
    have habsZ : 2 * Real.pi * |(q.den : ℝ) * (θ / (2 * Real.pi)) - (q.num : ℝ)| ≤
        2 * Real.pi / (q.den : ℝ) := by
      have h2 : 2 * Real.pi * (1 / (q.den : ℝ)) = 2 * Real.pi / (q.den : ℝ) := by ring
      rw [← h2]
      exact mul_le_mul_of_nonneg_left (le_of_lt hlt) (by positivity)
    have hbound : 1 - (2 * Real.pi / (q.den : ℝ)) ^ 2 / 2 ≤
        Real.cos (2 * Real.pi * ((q.den : ℝ) * (θ / (2 * Real.pi)) - (q.num : ℝ))) := by
      have h1 := cos_ge_one_sub_half_sq
        (2 * Real.pi * ((q.den : ℝ) * (θ / (2 * Real.pi)) - (q.num : ℝ)))
      have h2 : (2 * Real.pi * ((q.den : ℝ) * (θ / (2 * Real.pi)) - (q.num : ℝ))) ^ 2 ≤
          (2 * Real.pi / (q.den : ℝ)) ^ 2 := by
        refine (sq_le_sq).mpr ?_
        rw [habs1, abs_of_pos hpd]
        exact habsZ
      linarith
    have hconv : (2 * Real.pi / (q.den : ℝ)) ^ 2 / 2 = 2 * Real.pi ^ 2 / (q.den : ℝ) ^ 2 := by
      ring
    rw [hconv] at hbound
    have hn1 : 2 * Real.pi ^ 2 / (q.den : ℝ) ^ 2 < ε := by
      refine hkey q.den ?_
      exact le_trans (le_max_left _ _) (le_of_lt hden)
    linarith
  case neg =>
    -- 有理情形: 分母倍数下标精确命中 cos = 1
    obtain ⟨q, hq⟩ := exists_rat_of_not_irrational hrat
    have hdne : ((q.den : ℕ) : ℝ) ≠ 0 := by exact_mod_cast q.pos.ne'
    have hqc : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := Rat.cast_def q
    refine ⟨q.den * (Q + 1), ?_, ?_⟩
    · exact ((Nat.lt_succ_self Q).trans_le (Nat.le_mul_of_pos_left (Q + 1) q.pos)).le
    · have hθ : θ = 2 * Real.pi * (q : ℝ) := by
        have h1 := (div_eq_iff (by positivity : (2 : ℝ) * Real.pi ≠ 0)).mp hq
        linarith
      have hdθ : ((q.den : ℕ) : ℝ) * θ = 2 * Real.pi * (q.num : ℝ) := by
        rw [hθ, hqc]
        field_simp
      have hval : ((q.den * (Q + 1) : ℕ) : ℝ) * θ =
          (((Q + 1) * q.num : ℤ) : ℝ) * (2 * Real.pi) := by
        rw [Nat.cast_mul, mul_right_comm, hdθ]
        push_cast
        ring
      rw [hval, Real.cos_int_mul_two_pi]
      linarith

end RHLiCriterion
