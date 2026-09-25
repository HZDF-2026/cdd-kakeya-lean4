import CddFormalization.RH_MeasureTheory
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

open RHMeasureTheory Complex Real Set Finset

-- ============================================================
-- 1. 幂增长与幂衰减的初等引理 (照抄主文件第 1 节, 已可编译)
-- ============================================================

/-- 幂增长: 底大于 1 的幂序列无界支配任意实数. -/
theorem exists_pow_gt_of_one_lt {a : ℝ} (ha : 1 < a) (x : ℝ) :
    ∃ n : ℕ, x < a ^ n := by
  have hpos : 0 < a - 1 := sub_pos.mpr ha
  obtain ⟨n, hn⟩ := exists_nat_gt ((x - 1) / (a - 1))
  refine ⟨n, ?_⟩
  have hbern : 1 + (n : ℝ) * (a - 1) ≤ (1 + (a - 1)) ^ n := by
    simpa using one_add_mul_le_pow (by linarith : -2 ≤ a - 1) n
  have heq : 1 + (a - 1) = a := by ring
  rw [heq] at hbern
  have h2 : x - 1 < (n : ℝ) * (a - 1) := by
    have h3 : (x - 1) / (a - 1) < (n : ℝ) := hn
    rwa [div_lt_iff₀ hpos] at h3
  linarith

/-- 幂衰减: 底在 [0,1) 的幂序列最终小于任意正数. -/
theorem exists_pow_le_delta_of_lt_one {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {δ : ℝ}
    (hδ : 0 < δ) : ∃ Q : ℕ, ∀ n : ℕ, Q ≤ n → a ^ n ≤ δ := by
  rcases eq_or_lt_of_le ha0 with rfl | hpos
  · refine ⟨1, fun n hn => ?_⟩
    rw [zero_pow (by omega : n ≠ 0)]
    exact hδ.le
  · have hinv : 1 < a⁻¹ := (one_lt_inv₀ hpos).mpr ha1
    obtain ⟨Q, hQ⟩ := exists_pow_gt_of_one_lt hinv δ⁻¹
    refine ⟨Q, fun n hn => ?_⟩
    have h1 : a ^ Q < δ := by
      have h2 : δ⁻¹ < (a⁻¹) ^ Q := hQ
      rw [inv_pow] at h2
      have hA : 0 < a ^ Q := pow_pos hpos Q
      exact (inv_lt_inv₀ hδ hA).mp h2
    exact le_of_lt (lt_of_le_of_lt (pow_le_pow_of_le_one hpos.le ha1.le hn) h1)

/-- 幂下界: 底大于 1 的幂序列最终超过任意常数. -/
theorem exists_pow_ge_const_of_one_lt {M : ℝ} (hM : 1 < M) (C : ℝ) :
    ∃ Q : ℕ, ∀ n : ℕ, Q ≤ n → C ≤ M ^ n := by
  obtain ⟨Q, hQ⟩ := exists_pow_gt_of_one_lt hM C
  refine ⟨Q, fun n hn => ?_⟩
  exact (le_of_lt hQ).trans (pow_le_pow_right₀ (le_of_lt hM) hn)

-- ============================================================
-- 3. Li 泛函单项 (照抄主文件)
-- ============================================================

/-- Li 泛函单项: `liTerm ρ n = Re[1 - (1 - 1/ρ)ⁿ]`. -/
def liTerm (ρ : ℂ) (n : ℕ) : ℝ := (1 - (1 - ρ⁻¹) ^ n).re

-- ============================================================
-- 4. 辐角回归定理 stub (另一子代理负责真实证明, 此处同陈述占位)
-- ============================================================

theorem exists_ge_cos_ge {θ : ℝ} {ε : ℝ} (hε : 0 < ε) (Q : ℕ) :
    ∃ n : ℕ, Q ≤ n ∧ 1 - ε ≤ Real.cos ((n : ℝ) * θ) := by
  sorry

-- ============================================================
-- 5. 主导支配定理: 单主导偏线零点使截断 Li 和变负
-- ============================================================

/-- 极坐标实部公式: `Re[uⁿ] = |u|ⁿ · cos(n·arg u)` (u ≠ 0). -/
lemma re_pow_eq_norm_pow_mul_cos {u : ℂ} (hu : u ≠ 0) (n : ℕ) :
    (u ^ n).re = (‖u‖ : ℝ) ^ n * Real.cos ((n : ℝ) * Complex.arg u) := by
  have hpolar : u = ‖u‖ * Complex.exp (Complex.arg u * I) :=
    (Complex.norm_mul_exp_arg_mul_I u).symm
  have hnp : u ^ n = (‖u‖ * Complex.exp (Complex.arg u * I)) ^ n :=
    congrArg (fun z => z ^ n) hpolar
  rw [hnp, mul_pow, ← Complex.exp_nat_mul]
  have hcast : (n : ℕ) * (Complex.arg u * I) =
      Complex.ofReal ((n : ℝ) * Complex.arg u) * I := by
    push_cast
    ring
  rw [hcast, Complex.mul_re, Complex.exp_ofReal_mul_I_re, ← Complex.ofReal_pow,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **主导支配定理**: 若有限零点集中存在模长严格主导的元素 ρ₀
    (`|u(ρ₀)| > 1` 且其余项严格更小), 则某阶截断 Li 和严格为负.

    证明机制:
    * 辐角回归 (`exists_ge_cos_ge`) 给出 Re[u(ρ₀)ⁿ] ≥ (3/4)|u(ρ₀)|ⁿ
      沿无界下标集;
    * 其余项被几何衰减支配 (Σ|u(ρ)|ⁿ ≤ |S|·|u(ρ₀)|ⁿ/4);
    * 指数增长主导常数项, 总和 = |S| - ΣRe[u(ρ)ⁿ] < 0. -/
theorem li_dominance {S : Finset ℂ} {ρ₀ : ℂ}
    (h₀ : ρ₀ ∈ S) (hzero : ∀ ρ ∈ S, ρ ≠ 0)
    (hM : 1 < ‖(1 : ℂ) - ρ₀⁻¹‖)
    (hdom : ∀ ρ ∈ S, ρ ≠ ρ₀ → ‖(1 : ℂ) - ρ⁻¹‖ < ‖(1 : ℂ) - ρ₀⁻¹‖) :
    ∃ n : ℕ, (∑ ρ ∈ S, liTerm ρ n) < 0 := by
  classical
  set M : ℝ := ‖(1 : ℂ) - ρ₀⁻¹‖ with hMdef
  set u₀ : ℂ := 1 - ρ₀⁻¹ with hu₀def
  have hM1 : 1 < M := hM
  have hMpos : 0 < M := lt_trans zero_lt_one hM
  have hu₀ne : u₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hMdef
    linarith
  set N := S.card with hN
  have hNge1 : 1 ≤ N := Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨ρ₀, h₀⟩)
  have hNpos : 0 < (N : ℝ) := by positivity
  -- 步骤 A: 非主导项几何衰减
  have hdecay : ∀ ρ ∈ S.erase ρ₀, ∃ Q : ℕ, ∀ n : ℕ, Q ≤ n →
      ‖(1 : ℂ) - ρ⁻¹‖ ^ n ≤ (1 / (4 * (N : ℝ))) * M ^ n := by
    intro ρ hρ
    have hρmem : ρ ∈ S := (Finset.mem_erase.mp hρ).2
    have hne : ρ ≠ ρ₀ := (Finset.mem_erase.mp hρ).1
    have hlt : ‖(1 : ℂ) - ρ⁻¹‖ < M := hdom ρ hρmem hne
    have hratio : ‖(1 : ℂ) - ρ⁻¹‖ / M < 1 := by
      rw [div_lt_iff₀ hMpos]
      linarith
    obtain ⟨Q, hQ⟩ := exists_pow_le_delta_of_lt_one (a := ‖(1 : ℂ) - ρ⁻¹‖ / M)
      (δ := 1 / (4 * (N : ℝ))) (div_nonneg (norm_nonneg _) hMpos.le) hratio (by positivity)
    refine ⟨Q, fun n hn => ?_⟩
    have h1 : (‖(1 : ℂ) - ρ⁻¹‖ / M) ^ n ≤ 1 / (4 * (N : ℝ)) := hQ n hn
    have h2 : (‖(1 : ℂ) - ρ⁻¹‖ / M) ^ n * M ^ n = ‖(1 : ℂ) - ρ⁻¹‖ ^ n := by
      rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero n hMpos.ne')]
    calc ‖(1 : ℂ) - ρ⁻¹‖ ^ n = (‖(1 : ℂ) - ρ⁻¹‖ / M) ^ n * M ^ n := h2.symm
      _ ≤ (1 / (4 * (N : ℝ))) * M ^ n :=
          mul_le_mul_of_nonneg_right h1 (pow_nonneg hMpos.le n)
  -- 步骤 B: 衰减求和界
  choose Qρ hQρ using hdecay
  obtain ⟨Qsum, hQsum⟩ : ∃ Q : ℕ, ∀ n : ℕ, Q ≤ n →
      ∑ ρ ∈ S.erase ρ₀, ‖(1 : ℂ) - ρ⁻¹‖ ^ n ≤ (1 / 4) * M ^ n := by
    refine ⟨((S.erase ρ₀).attach.sup fun p => Qρ p.1 p.2), fun n hn => ?_⟩
    have hle : ∑ ρ ∈ S.erase ρ₀, ‖(1 : ℂ) - ρ⁻¹‖ ^ n ≤
        ∑ ρ ∈ S.erase ρ₀, (1 / (4 * (N : ℝ))) * M ^ n :=
      Finset.sum_le_sum fun ρ hρ => hQρ ρ hρ n
        (le_trans (Finset.le_sup (f := fun p => Qρ p.1 p.2)
          (Finset.mem_attach (S.erase ρ₀) ⟨ρ, hρ⟩)) hn)
    have hcard : ((S.erase ρ₀).card : ℝ) ≤ N := by
      rw [hN]
      exact_mod_cast Finset.card_erase_le
    have hsum : ∑ ρ ∈ S.erase ρ₀, (1 / (4 * (N : ℝ))) * M ^ n =
        ((S.erase ρ₀).card : ℝ) * (1 / (4 * (N : ℝ))) * M ^ n := by
      rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul (R := ℝ), smul_eq_mul]
      ring
    have hfin : ((S.erase ρ₀).card : ℝ) * (1 / (4 * (N : ℝ))) ≤ 1 / 4 := by
      have hb1 : ((S.erase ρ₀).card : ℝ) * (1 / (4 * (N : ℝ))) ≤
          N * (1 / (4 * (N : ℝ))) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      have hb2 : N * (1 / (4 * (N : ℝ))) = 1 / 4 := by
        field_simp
      linarith
    calc ∑ ρ ∈ S.erase ρ₀, ‖(1 : ℂ) - ρ⁻¹‖ ^ n ≤
        ∑ ρ ∈ S.erase ρ₀, (1 / (4 * (N : ℝ))) * M ^ n := hle
      _ = ((S.erase ρ₀).card : ℝ) * (1 / (4 * (N : ℝ))) * M ^ n := hsum
      _ ≤ (1 / 4) * M ^ n := by
          exact mul_le_mul_of_nonneg_right hfin (pow_nonneg hMpos.le n)
  -- 步骤 C: 主导幂下界
  obtain ⟨Q₂, hQ₂⟩ := exists_pow_ge_const_of_one_lt hM1 (2 * ((N : ℝ) + 1) + 1)
  -- 步骤 D: 辐角回归与组装
  obtain ⟨n, hnQ, hcos⟩ := exists_ge_cos_ge (θ := Complex.arg u₀) (ε := 1 / 4)
    (by norm_num) (max Qsum Q₂)
  have hn1 : Qsum ≤ n := le_trans (le_max_left _ _) hnQ
  have hn2 : Q₂ ≤ n := le_trans (le_max_right _ _) hnQ
  have hreu : (u₀ ^ n).re = M ^ n * Real.cos ((n : ℝ) * Complex.arg u₀) :=
    re_pow_eq_norm_pow_mul_cos hu₀ne n
  have hcos' : (3 / 4) * M ^ n ≤ (u₀ ^ n).re := by
    rw [hreu]
    have h34 : (3 : ℝ) / 4 * M ^ n = M ^ n * (1 - 1 / 4) := by ring
    rw [h34]
    exact mul_le_mul_of_nonneg_left hcos (pow_nonneg hMpos.le n)
  have hsplit : ∑ ρ ∈ S, liTerm ρ n = liTerm ρ₀ n + ∑ ρ ∈ S.erase ρ₀, liTerm ρ n :=
    (Finset.add_sum_erase S (fun x => liTerm x n) (a := ρ₀) h₀).symm
  have ht0 : liTerm ρ₀ n ≤ 1 - (3 / 4) * M ^ n := by
    have hEq : liTerm ρ₀ n = 1 - (u₀ ^ n).re := by
      unfold liTerm
      rw [hu₀def, Complex.sub_re, Complex.one_re]
    rw [hEq]
    linarith
  have hterase : ∑ ρ ∈ S.erase ρ₀, liTerm ρ n ≤ (N : ℝ) + (1 / 4) * M ^ n := by
    have h1 : ∀ ρ ∈ S.erase ρ₀, liTerm ρ n ≤ 1 + ‖(1 : ℂ) - ρ⁻¹‖ ^ n := by
      intro ρ _
      have hEq : liTerm ρ n = 1 - (((1 : ℂ) - ρ⁻¹) ^ n).re := by
        unfold liTerm
        rw [Complex.sub_re, Complex.one_re]
      have habs := Complex.abs_re_le_norm (((1 : ℂ) - ρ⁻¹) ^ n)
      rw [Complex.norm_pow] at habs
      rw [hEq]
      have hneg : -‖(1 : ℂ) - ρ⁻¹‖ ^ n ≤ (((1 : ℂ) - ρ⁻¹) ^ n).re := (abs_le.mp habs).1
      linarith
    have h2 : ∑ ρ ∈ S.erase ρ₀, liTerm ρ n ≤
        ∑ ρ ∈ S.erase ρ₀, (1 + ‖(1 : ℂ) - ρ⁻¹‖ ^ n) := Finset.sum_le_sum h1
    have h3 : ∑ ρ ∈ S.erase ρ₀, (1 + ‖(1 : ℂ) - ρ⁻¹‖ ^ n) =
        ((S.erase ρ₀).card : ℝ) + ∑ ρ ∈ S.erase ρ₀, ‖(1 : ℂ) - ρ⁻¹‖ ^ n := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Nat.smul_one_eq_cast]
    have h4 : ((S.erase ρ₀).card : ℝ) ≤ N := by
      rw [hN]
      exact_mod_cast Finset.card_erase_le
    have h5 := hQsum n hn1
    linarith
  have htotal : ∑ ρ ∈ S, liTerm ρ n ≤ (1 : ℝ) + N - (1 / 2) * M ^ n := by
    rw [hsplit]
    have hsimp : (1 : ℝ) - (3 / 4) * M ^ n + ((N : ℝ) + (1 / 4) * M ^ n) =
        1 + N - (1 / 2) * M ^ n := by ring
    rw [← hsimp]
    linarith [ht0, hterase]
  have hMpow : 2 * ((N : ℝ) + 1) + 1 ≤ M ^ n := hQ₂ n hn2
  refine ⟨n, ?_⟩
  have hcalc : (1 : ℝ) + N - (1 / 2) * M ^ n < 0 := by
    have hhalf : (N : ℝ) + 1 + 1 / 2 ≤ (1 / 2) * M ^ n := by
      calc (N : ℝ) + 1 + 1 / 2 = (1 / 2) * (2 * ((N : ℝ) + 1) + 1) := by ring
        _ ≤ (1 / 2) * M ^ n := mul_le_mul_of_nonneg_left hMpow (by norm_num)
    linarith
  calc ∑ ρ ∈ S, liTerm ρ n ≤ (1 : ℝ) + N - (1 / 2) * M ^ n := htotal
    _ < 0 := hcalc

end RHLiCriterion
