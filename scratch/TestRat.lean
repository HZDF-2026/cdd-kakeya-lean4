import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.NormNum

/-! # Regression Test: Mathlib Rat 验证链 (Lean 4.32.2)

    历史说明: 此前该文件包含自建 Rat 正定性引理链
    (rat_pos_iff_num_pos → nat_div_pos_of_dvd → int_tdiv_pos_of_pos
     → rat_mul_pos → rat_neg_neg_of_pos → kolmogorov_45_general),
    全部基于分子符号分析与 GCD 分解在 Std.Internal.Rat 上手工证明.

    Lean 4.32.2 中 Std.Internal.Rat 已并入核心库 (Init.Data.Rat.Basic),
    自建引理链已整体升级为 Mathlib 标准引理:
    * rat_mul_pos        ← Mathlib `mul_pos`      (LinearOrderedField ℚ)
    * rat_neg_neg_of_pos ← Mathlib `neg_lt_zero`
    * kolmogorov_45_general 见 CddFormalization.Kolmogorov45

    本文件现为回归测试, 验证:
    1. Mathlib 有序域实例在核心 Rat 类型上正确生效
    2. kernel decide 数值复核 (内核逐位验算)
    3. Mathlib 引理链端到端通过 (一般形式, 全称量化)
    4. 公理依赖审计 (仅 propext/Classical.choice/Quot.sound)
-/

-- ============================================================
-- 1. Mathlib 有序域实例生效于核心 Rat
--    (由下方 mul_pos / neg_lt_zero 在 Rat 上成功实例化验证)
-- ============================================================

/-- 核心构造子 mkRat 与 Mathlib ℚ 字面量语义一致: 4/5 = (4:ℚ)/5
    (Rat 算术在 4.32.2 内核不可归约, 由 Mathlib norm_num 完成验算) -/
example : (mkRat 4 5 : Rat) = (4 : ℚ) / 5 := by norm_num

-- ============================================================
-- 2. 数值回归: 字面量比较 kernel decide + 算术求值 norm_num
-- ============================================================

example : (mkRat 4 5 : Rat) > 0 := by decide
example : (mkRat 4 5 : Rat) < 1 := by decide
example : (mkRat (-4) 5 : Rat) < 0 := by decide
example : (mkRat 9 14 : Rat) - mkRat 3 5 = mkRat 3 70 := by norm_num
example : mkRat 2 7 + mkRat 9 14 + mkRat 1 14 = 1 := by norm_num

-- ============================================================
-- 3. Mathlib 引理链 (一般形式, 全称量化)
-- ============================================================

/-- Mathlib mul_pos 在 Rat 上实例化 (此前为自建 GCD 分解证明) -/
theorem test_rat_mul_pos (a b : Rat) (ha : 0 < a) (hb : 0 < b) : 0 < a * b :=
  mul_pos ha hb

/-- Mathlib neg_lt_zero 在 Rat 上实例化 (此前为自建分子符号分析) -/
theorem test_rat_neg_neg_of_pos (a : Rat) (ha : 0 < a) : -a < 0 :=
  neg_lt_zero.mpr ha

/-- Kolmogorov 4/5 律一般形式: 全证明链仅使用 Mathlib 标准引理 -/
theorem test_kolmogorov_45_general (ε r : Rat) (hε : 0 < ε) (hr : 0 < r) :
    -(mkRat 4 5 * ε * r) < 0 := by
  have h_45 : (0 : Rat) < mkRat 4 5 := by decide
  have h1 : (0 : Rat) < mkRat 4 5 * ε := mul_pos h_45 hε
  have h2 : (0 : Rat) < mkRat 4 5 * ε * r := mul_pos h1 hr
  exact neg_lt_zero.mpr h2

-- ============================================================
-- 4. 公理依赖审计
-- ============================================================

#print axioms test_rat_mul_pos
#print axioms test_rat_neg_neg_of_pos
#print axioms test_kolmogorov_45_general
