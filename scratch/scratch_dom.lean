import CddFormalization.RH_LiCriterion

-- [H3 fix, 2026-09-04] 根级占位 `axiom exists_simultaneous_cos_ge` 已删除:
-- 定理本体已收编为正式模块定理 `RHLiCriterion.exists_simultaneous_cos_ge`
-- (RH_LiCriterion.lean:478, 鸽笼 Dirichlet + 倍增; AxiomAudit.lean:100 已审计
-- 公理依赖为标准三公理)。本文件下方 `li_dominance` 直接引用正式定理,
-- scratch/ 内不再存在任何自定义 `axiom` 声明。

noncomputable section

namespace ScratchDom

open Complex Real Finset

-- === support lemmas copied from RH_LiCriterion (unchanged) ===

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

theorem exists_pow_ge_const_of_one_lt {M : ℝ} (hM : 1 < M) (C : ℝ) :
    ∃ Q : ℕ, ∀ n : ℕ, Q ≤ n → C ≤ M ^ n := by
  obtain ⟨Q, hQ⟩ := exists_pow_gt_of_one_lt hM C
  refine ⟨Q, fun n hn => ?_⟩
  exact (le_of_lt hQ).trans (pow_le_pow_right₀ (le_of_lt hM) hn)

/-- 极坐标实部公式: `Re[uⁿ] = |u|ⁿ · cos(n·arg u)`. -/
lemma re_pow_eq_norm_pow_mul_cos {u : ℂ} (n : ℕ) :
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

/-- Li 泛函单项: `liTerm ρ n = Re[1 - (1 - 1/ρ)ⁿ]`. -/
def liTerm (ρ : ℂ) (n : ℕ) : ℝ := (1 - (1 - ρ⁻¹) ^ n).re

-- === [H3 fix] was: placeholder axiom, now references formal module ===
-- (theorem body: RHLiCriterion.exists_simultaneous_cos_ge, signature identical)

-- === NEW li_dominance ===

theorem li_dominance {S : Finset ℂ} {ρ₀ : ℂ}
    (h₀ : ρ₀ ∈ S)
    (hM : 1 < ‖(1 : ℂ) - ρ₀⁻¹‖)
    (hmax : ∀ ρ ∈ S, ‖(1 : ℂ) - ρ⁻¹‖ ≤ ‖(1 : ℂ) - ρ₀⁻¹‖) :
    ∃ n : ℕ, (∑ ρ ∈ S, liTerm ρ n) < 0 := by
  classical
  -- 接口保留: 同时回归机制下共振类全体统一处理, hmax 不再参与证明内核
  have _hmaxkept := hmax
  set M : ℝ := ‖(1 : ℂ) - ρ₀⁻¹‖
  have hM1 : 1 < M := hM
  set N := S.card with hN
  have hNge1 : 1 ≤ N := Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨ρ₀, h₀⟩)
  -- 步骤 A: 主导幂下界
  obtain ⟨Q₂, hQ₂⟩ := exists_pow_ge_const_of_one_lt hM1 (2 * ((N : ℝ) + 1))
  -- 步骤 B: 同时辐角回归 (共振类全体 S, ε = 1/2)
  obtain ⟨n, hnQ, hcos⟩ := RHLiCriterion.exists_simultaneous_cos_ge
    (fun j : ↥S => Complex.arg (1 - ((j : ℂ)⁻¹))) (ε := 1 / 2) (by norm_num) Q₂
  -- 步骤 C: 每项实部下界 — 共振类全体同时回归, 无需区分是否严格主导
  have hre : ∀ ρ ∈ S, (1 / 2 : ℝ) * ‖(1 : ℂ) - ρ⁻¹‖ ^ n ≤ (((1 : ℂ) - ρ⁻¹) ^ n).re := by
    intro ρ hρ
    have hc := hcos ⟨ρ, hρ⟩
    rw [re_pow_eq_norm_pow_mul_cos n]
    have hhalf : (1 / 2 : ℝ) * ‖(1 : ℂ) - ρ⁻¹‖ ^ n =
        ‖(1 : ℂ) - ρ⁻¹‖ ^ n * (1 - 1 / 2) := by
      have h52 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
      rw [h52]
      ring
    rw [hhalf]
    exact mul_le_mul_of_nonneg_left hc (pow_nonneg (norm_nonneg _) n)
  -- 步骤 D: 总和上界
  have htotal : ∑ ρ ∈ S, liTerm ρ n ≤ ((N : ℝ)) - (1 / 2) * M ^ n := by
    have h1 : ∑ ρ ∈ S, liTerm ρ n = ((N : ℝ)) - ∑ ρ ∈ S, (((1 : ℂ) - ρ⁻¹) ^ n).re := by
      simp only [liTerm, Complex.sub_re, Complex.one_re]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.smul_one_eq_cast]
    have h2 : (1 / 2) * M ^ n ≤ ∑ ρ ∈ S, (((1 : ℂ) - ρ⁻¹) ^ n).re := by
      have hnn : ∀ ρ ∈ S, (0 : ℝ) ≤ (((1 : ℂ) - ρ⁻¹) ^ n).re := by
        intro ρ hρ
        exact le_trans (by positivity) (hre ρ hρ)
      exact le_trans (hre ρ₀ h₀) (Finset.single_le_sum hnn h₀)
    rw [h1]
    linarith
  -- 步骤 E: 指数支配常数项
  have hMpow : 2 * ((N : ℝ) + 1) ≤ M ^ n := hQ₂ n hnQ
  refine ⟨n, ?_⟩
  have hcalc : ((N : ℝ)) - (1 / 2) * M ^ n < 0 := by
    have hhalf : (N : ℝ) + 1 ≤ (1 / 2) * M ^ n := by
      calc (N : ℝ) + 1 = (1 / 2) * (2 * ((N : ℝ) + 1)) := by ring
        _ ≤ (1 / 2) * M ^ n := mul_le_mul_of_nonneg_left hMpow (by norm_num)
    linarith
  calc ∑ ρ ∈ S, liTerm ρ n ≤ ((N : ℝ)) - (1 / 2) * M ^ n := htotal
    _ < 0 := hcalc

end ScratchDom

end
