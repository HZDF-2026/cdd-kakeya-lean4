import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! # W2 Measure & EMA: 测量协议形式化 (wave_proto EMA / 相位平均 / λ 标定)

    wave_proto S11-S13 测量协议 (ablation_lrd.py train_lrd 逐字对应) 的
    Lean 4 形式化。协议语义 (Python 源码):

        EMA_BETA = 0.9
        phic_ema = 0
        for it in range(ITERS):
            phic ← 优化器步
            phic_ema = EMA_BETA * phic_ema + (1 - EMA_BETA) * phic
            if (it+1) in CHECKPOINTS:            # {15, 30, 50}
                ema_bc = phic_ema / (1 - EMA_BETA^(it+1))   # 偏差修正
                u_e = eval(ema_bc)

    测量协议 (project_distillation.txt §4 终版处方):
      - 主指标 = 匹配检查点集的 EMA 均值 (最少 {15,30,50});
      - 单检查点 (含 EMA@50) 只作漂移诊断;
      - 相位平均 = 双层凸组合 (EMA 层 × 检查点平均层)。

    ## 本模块证明的定理 (全部 Mathlib 支撑, 零 sorry)

    EMA 递推与展开:
    1. `emaRec`              : 递推定义 e₀=0, e_{t+1}=β·e_t+(1-β)·x_{t+1}
    2. `emaRec_eq_sum`       : 展开式 e_t = Σ_{s<t} (1-β)β^{t-1-s}·x_{s+1}
    3. `ema_weight_sum`      : 权重和 Σ (1-β)β^{t-1-s} = 1-β^t
                                (偏差修正分母的来源)
    偏差修正:
    4. `emaBC` / `emaBC_eq_sum`      : 修正后 = 权重和恰为 1 的加权平均
    5. `emaBC_weight_sum`    : 修正权重 Σ w_s = 1 (凸组合性)
    6. `one_sub_pow_pos`     : β∈[0,1), t≥1 ⇒ 0 < 1-β^t (分母正)
    7. `emaRec_const`        : 常数序列的未修正 EMA = (1-β^t)·c
                                (偏差因子正是 1-β^t —— 修正的必要性)
    8. `emaBC_const`         : 修正后常数序列 = c (不动点)
    凸组合界保持 (测量不越界):
    9. `emaBC_le_max` / `emaBC_ge_min` : 轨迹在 [m,M] 内 ⇒ EMA 在 [m,M] 内
    10. `ema_weight_anti`    : β∈[0,1] ⇒ 权重 β^l ≤ β^k (l≥k) —— 几何遗忘
    相位平均协议 (主指标):
    11. `phaseAvg3_le_max` / `phaseAvg3_ge_min` : 三检查点均值保持界
    12. `phaseAvg_EMA_bounds` : **双层凸组合主定理** —— 轨迹全程在
                                [m,M] 内 ⇒ 检查点 EMA 均值在 [m,M] 内
                                (相位鲁棒性的数学内容: 任何单检查点漂移
                                不可能把主指标推出轨迹包络)
    λ 标定算术 (S12 记录值登记, sweepf_p*.npz):
    13. `calibrate_roundtrip`: RATIO·(λ_ref/RATIO) = λ_ref (标定不变量)
    14. `s12_lam_calibration`: 全部 7 臂 recorded λ_res 与 ratio×λ_unit
                                的偏差 ≤ 4×10⁻¹⁶ (float64 末位舍入级)
    15. `s12_protocol_regs`  : 协议常数登记 (β=9/10, LR 1/20→1/200,
                                RATIO=1/2, λ_res@0.5 = λ_unit/2 精确)

    ## 诚实声明 (形式化范围边界)

    - 形式化的是**测量算子的数学性质** (凸组合性/界保持/标定恒等式),
      非对 Python 数值代码的等价性验证;
    - 记录值 (recorded-stats) 以 ℚ 定点缩放登记, 不在 Lean 内重算
      (S12 npz 为唯一数据源, 与 T3_ECSChannels 登记模式一致);
    - float64 舍入以 |Δ| ≤ 4×10⁻¹⁶ 的 ℚ 不等式诚实登记:
      ratio=0.5 臂为精确恒等 (÷2 二进制精确), 其余臂含末位舍入;
    - 评估函数 eval(·) 本身 (160 episode 均值) 不在此模块 —— 它是
      外部测量设备; 定理 11-12 对任意逐检查点测量值成立。

    CDD Framework v28.4 · wave_proto S11-S13 测量内核
    Date: 2026-08-31
    Toolchain: Lean v4.32.2 + Mathlib (mathlib432 local checkout)
-/

namespace CDD.W2.MeasureEMA

open Finset

-- ============================================================
-- §1 EMA 递推定义 (ablation_lrd.py train_lrd 逐字对应)
-- ============================================================

/-- EMA 递推: e₀ = 0, e_{t+1} = β·e_t + (1-β)·x_{t+1}。
    β = EMA_BETA = 0.9 (wave_proto), x_t = 第 t 步后的参数场。 -/
noncomputable def emaRec (β : ℝ) (x : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => β * emaRec β x t + (1 - β) * x (t + 1)

/-- 偏差修正 EMA: ê_t = e_t / (1 - β^t) (train_lrd 检查点处的 ema_bc)。 -/
noncomputable def emaBC (β : ℝ) (x : ℕ → ℝ) (t : ℕ) : ℝ :=
  emaRec β x t / (1 - β ^ t)

-- ============================================================
-- §2 展开式: e_t = Σ_{s<t} (1-β)·β^{t-1-s}·x_{s+1}
-- ============================================================

/-- **EMA 展开式**: 递推等价于几何加权求和 —— 步骤 s+1 的权重为
    (1-β)·β^{t-1-s} (越早的步骤权重按 β 几何衰减)。 -/
theorem emaRec_eq_sum (β : ℝ) (x : ℕ → ℝ) (t : ℕ) :
    emaRec β x t = ∑ s ∈ range t, (1 - β) * β ^ (t - 1 - s) * x (s + 1) := by
  induction t with
  | zero => simp [emaRec]
  | succ t ih =>
      have key : β * ∑ s ∈ range t, (1 - β) * β ^ (t - 1 - s) * x (s + 1)
          = ∑ s ∈ range t, (1 - β) * β ^ (t - s) * x (s + 1) := by
        rw [mul_sum]
        refine sum_congr rfl fun s hs => ?_
        have hs' : s < t := Finset.mem_range.mp hs
        have hsub : t - s = (t - 1 - s) + 1 := by omega
        rw [hsub, pow_succ]
        ring
      rw [emaRec, ih, sum_range_succ]
      simp only [Nat.add_sub_cancel]
      rw [key]
      have hlast : t - t = 0 := Nat.sub_self t
      rw [hlast, pow_zero, mul_one]

/-- **权重和定理**: Σ_{s<t} (1-β)·β^{t-1-s} = 1 - β^t。
    这正是偏差修正分母的来源: 未修正 EMA 的总权重不足 1,
    差 1-β^t。归纳证明不依赖除法, 对一切 β (含 β=1) 成立。 -/
theorem ema_weight_sum (β : ℝ) (t : ℕ) :
    ∑ s ∈ range t, (1 - β) * β ^ (t - 1 - s) = 1 - β ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
      have key : ∑ s ∈ range t, (1 - β) * β ^ (t - s)
          = β * ∑ s ∈ range t, (1 - β) * β ^ (t - 1 - s) := by
        rw [mul_sum]
        refine sum_congr rfl fun s hs => ?_
        have hs' : s < t := Finset.mem_range.mp hs
        have hsub : t - s = (t - 1 - s) + 1 := by omega
        rw [hsub, pow_succ]
        ring
      rw [sum_range_succ]
      simp only [Nat.add_sub_cancel]
      rw [key, ih]
      have hlast : t - t = 0 := Nat.sub_self t
      rw [hlast, pow_zero, mul_one, pow_succ]
      ring

-- ============================================================
-- §3 偏差修正: 凸组合权重
-- ============================================================

/-- **分母正性**: β ∈ [0,1), t ≥ 1 ⇒ 0 < 1 - β^t。 -/
theorem one_sub_pow_pos (β : ℝ) (h0 : 0 ≤ β) (h1 : β < 1) {t : ℕ} (ht : 1 ≤ t) :
    0 < 1 - β ^ t := by
  have hle : β ^ t ≤ β ^ 1 := pow_le_pow_of_le_one h0 h1.le ht
  have h1' : β ^ 1 = β := pow_one β
  linarith

/-- **偏差修正 EMA = 权重和为 1 的加权平均**: 修正后每个步骤的权重
    w_s = (1-β)β^{t-1-s}/(1-β^t) ≥ 0 且 Σ w_s = 1 —— 凸组合。 -/
theorem emaBC_eq_sum (β : ℝ) (x : ℕ → ℝ) (t : ℕ) :
    emaBC β x t
      = ∑ s ∈ range t, ((1 - β) * β ^ (t - 1 - s) / (1 - β ^ t)) * x (s + 1) := by
  have h : ∀ s ∈ range t,
      ((1 - β) * β ^ (t - 1 - s) / (1 - β ^ t)) * x (s + 1)
        = ((1 - β) * β ^ (t - 1 - s) * x (s + 1)) / (1 - β ^ t) :=
    fun s _ => by ring
  rw [emaBC, emaRec_eq_sum, sum_congr rfl h, Finset.sum_div]

/-- **修正权重和为 1** (凸组合性)。 -/
theorem emaBC_weight_sum (β : ℝ) (t : ℕ) (h : 1 - β ^ t ≠ 0) :
    ∑ s ∈ range t, (1 - β) * β ^ (t - 1 - s) / (1 - β ^ t) = 1 := by
  have key : ∑ s ∈ range t, (1 - β) * β ^ (t - 1 - s) / (1 - β ^ t)
      = (∑ s ∈ range t, (1 - β) * β ^ (t - 1 - s)) / (1 - β ^ t) := by
    simp only [div_eq_mul_inv]
    rw [Finset.sum_mul]
  rw [key, ema_weight_sum, div_self h]

/-- **常数序列的未修正 EMA**: e_t = (1-β^t)·c —— 未修正 EMA 对常数
    序列有系统性低估, 偏差因子恰为 1-β^t (偏差修正的必要性)。 -/
theorem emaRec_const (β : ℝ) (c : ℝ) (t : ℕ) :
    emaRec β (fun _ => c) t = (1 - β ^ t) * c := by
  induction t with
  | zero => simp [emaRec]
  | succ t ih => rw [emaRec, ih, pow_succ]; ring

/-- **常数序列不动点**: 修正后 EMA 恢复常数 c。 -/
theorem emaBC_const (β : ℝ) (h0 : 0 ≤ β) (h1 : β < 1) (c : ℝ) {t : ℕ} (ht : 1 ≤ t) :
    emaBC β (fun _ => c) t = c := by
  have hd : 1 - β ^ t ≠ 0 :=
    ne_of_gt (one_sub_pow_pos β h0 h1 ht)
  rw [emaBC, emaRec_const, mul_div_cancel_left₀ _ hd]

-- ============================================================
-- §4 凸组合界保持 (测量不越界)
-- ============================================================

/-- **EMA 上界保持**: 轨迹前 t 步全部 ≤ M ⇒ 修正 EMA ≤ M
    (β ∈ [0,1), t ≥ 1)。凸组合不可能超出被平均值的包络。 -/
theorem emaBC_le_max (β : ℝ) (h0 : 0 ≤ β) (h1 : β < 1) (x : ℕ → ℝ)
    {t : ℕ} (ht : 1 ≤ t) (M : ℝ) (hM : ∀ s, s < t → x (s + 1) ≤ M) :
    emaBC β x t ≤ M := by
  have hd : 0 < 1 - β ^ t := one_sub_pow_pos β h0 h1 ht
  have hpos : ∀ s ∈ range t, 0 ≤ (1 - β) * β ^ (t - 1 - s) / (1 - β ^ t) := by
    intro s _
    exact div_nonneg (mul_nonneg (by linarith) (pow_nonneg h0 _)) hd.le
  have hsum : ∑ s ∈ range t, ((1 - β) * β ^ (t - 1 - s) / (1 - β ^ t)) * x (s + 1)
      ≤ ∑ s ∈ range t, ((1 - β) * β ^ (t - 1 - s) / (1 - β ^ t)) * M :=
    sum_le_sum fun s hs =>
      mul_le_mul_of_nonneg_left (hM s (Finset.mem_range.mp hs)) (hpos s hs)
  have htot : ∑ s ∈ range t, ((1 - β) * β ^ (t - 1 - s) / (1 - β ^ t)) * M = M := by
    rw [← Finset.sum_mul, emaBC_weight_sum β t (ne_of_gt hd), one_mul]
  rw [emaBC_eq_sum]
  exact hsum.trans_eq htot

/-- **EMA 下界保持**: 轨迹前 t 步全部 ≥ m ⇒ 修正 EMA ≥ m。 -/
theorem emaBC_ge_min (β : ℝ) (h0 : 0 ≤ β) (h1 : β < 1) (x : ℕ → ℝ)
    {t : ℕ} (ht : 1 ≤ t) (m : ℝ) (hm : ∀ s, s < t → m ≤ x (s + 1)) :
    m ≤ emaBC β x t := by
  have hd : 0 < 1 - β ^ t := one_sub_pow_pos β h0 h1 ht
  have hpos : ∀ s ∈ range t, 0 ≤ (1 - β) * β ^ (t - 1 - s) / (1 - β ^ t) := by
    intro s _
    exact div_nonneg (mul_nonneg (by linarith) (pow_nonneg h0 _)) hd.le
  have hsum : ∑ s ∈ range t, ((1 - β) * β ^ (t - 1 - s) / (1 - β ^ t)) * m
      ≤ ∑ s ∈ range t, ((1 - β) * β ^ (t - 1 - s) / (1 - β ^ t)) * x (s + 1) :=
    sum_le_sum fun s hs =>
      mul_le_mul_of_nonneg_left (hm s (Finset.mem_range.mp hs)) (hpos s hs)
  have htot : ∑ s ∈ range t, ((1 - β) * β ^ (t - 1 - s) / (1 - β ^ t)) * m = m := by
    rw [← Finset.sum_mul, emaBC_weight_sum β t (ne_of_gt hd), one_mul]
  calc m = ∑ s ∈ range t, ((1 - β) * β ^ (t - 1 - s) / (1 - β ^ t)) * m := htot.symm
    _ ≤ ∑ s ∈ range t, ((1 - β) * β ^ (t - 1 - s) / (1 - β ^ t)) * x (s + 1) := hsum
    _ = emaBC β x t := (emaBC_eq_sum β x t).symm

/-- **几何遗忘**: β ∈ [0,1] 时指数越大幂越小 (l ≥ k ⇒ β^l ≤ β^k)。
    EMA 权重 (1-β)β^{t-1-s} 对固定步骤 s 随检查点 t 单调衰减 ——
    早期游走/噪声被指数遗忘, 修正 EMA 是以近期为主的因果平均。 -/
theorem ema_weight_anti (β : ℝ) (h0 : 0 ≤ β) (h1 : β ≤ 1) {k l : ℕ} (hkl : k ≤ l) :
    β ^ l ≤ β ^ k :=
  pow_le_pow_of_le_one h0 h1 hkl

-- ============================================================
-- §5 相位平均协议 (主指标: 检查点集 EMA 均值)
-- ============================================================

/-- **三检查点均值上界**: {15,30,50} 均值 ≤ M (等权 1/3 凸组合)。 -/
theorem phaseAvg3_le_max (u : ℕ → ℝ) (M : ℝ)
    (h1 : u 15 ≤ M) (h2 : u 30 ≤ M) (h3 : u 50 ≤ M) :
    (u 15 + u 30 + u 50) / 3 ≤ M := by
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
  linarith

/-- **三检查点均值下界**: {15,30,50} 均值 ≥ m。 -/
theorem phaseAvg3_ge_min (u : ℕ → ℝ) (m : ℝ)
    (h1 : m ≤ u 15) (h2 : m ≤ u 30) (h3 : m ≤ u 50) :
    m ≤ (u 15 + u 30 + u 50) / 3 := by
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
  linarith

/-- **相位平均协议主定理 (双层凸组合)**: β ∈ [0,1) 且轨迹前 50 步
    全程在 [m, M] 内 ⇒ 主指标 (三检查点修正 EMA 的等权均值) 也严格
    在 [m, M] 内。

    数学内容: EMA 层是轨迹的凸组合 (定理 9), 检查点平均层是 EMA 值
    的凸组合 (定理 11), 凸组合的复合仍是凸组合 —— 故任何单检查点的
    相位漂移都不可能把主指标推出轨迹包络 [m, M]。这是"多检查点
    三角化"测量协议鲁棒性的数学保证 (project_distillation.txt §4)。 -/
theorem phaseAvg_EMA_bounds (β : ℝ) (h0 : 0 ≤ β) (h1 : β < 1) (x : ℕ → ℝ)
    (m M : ℝ)
    (hlo : ∀ s, 1 ≤ s → s ≤ 50 → m ≤ x s)
    (hhi : ∀ s, 1 ≤ s → s ≤ 50 → x s ≤ M) :
    m ≤ (emaBC β x 15 + emaBC β x 30 + emaBC β x 50) / 3 ∧
      (emaBC β x 15 + emaBC β x 30 + emaBC β x 50) / 3 ≤ M := by
  have hb : ∀ t : ℕ, 1 ≤ t → t ≤ 50 → m ≤ emaBC β x t ∧ emaBC β x t ≤ M := by
    intro t ht ht50
    exact ⟨emaBC_ge_min β h0 h1 x ht m (fun s hs => hlo (s + 1) (by omega) (by omega)),
      emaBC_le_max β h0 h1 x ht M (fun s hs => hhi (s + 1) (by omega) (by omega))⟩
  have a := hb 15 (by norm_num) (by norm_num)
  have b := hb 30 (by norm_num) (by norm_num)
  have c := hb 50 (by norm_num) (by norm_num)
  exact ⟨phaseAvg3_ge_min _ _ a.1 b.1 c.1, phaseAvg3_le_max _ _ a.2 b.2 c.2⟩

-- ============================================================
-- §6 λ 标定算术 (S12 记录值登记, sweepf_p*.npz)
-- ============================================================

/-- 标定不变量: 单位强度 = 参考强度/RATIO ⇒ 主工作点 (ratio=RATIO)
    精确恢复参考强度。 -/
theorem calibrate_roundtrip (RATIO lam_ref : ℝ) (h : RATIO ≠ 0) :
    RATIO * (lam_ref / RATIO) = lam_ref := by
  field_simp

/- S12 记录值 (sweep_fixo.py, 2026-08-30/31 全量 4 进程):
     lam_unit_res = 5.006825464552974   (r100_lam_res, sweepf_p4.npz)
     λ_res(ratio) = ratio × lam_unit_res 为浮点实现, 各臂 recorded 值:
       r000 = 0.0                    r035 = 1.7523889125935408
       r020 = 1.0013650929105948     r050 = 2.503412732276487
       r065 = 3.2544365519594334     r080 = 4.005460371642379
       r100 = 5.006825464552974
   以 ℚ 定点缩放登记 (×10¹⁵ / ×10¹⁶), 不在 Lean 内重算。 -/

/-- S12 记录: lam_unit_res (单位驻留正则强度)。 -/
abbrev lamUnitResQ : ℚ := 5006825464552974 / 1000000000000000

/-- S12 记录: λ_res@ratio=0.5 (主工作点, sweepf_p2.npz r050_lam_res)。 -/
abbrev lamRes050Q : ℚ := 2503412732276487 / 1000000000000000

/-- **主工作点标定恒等式 (精确)**: λ_res@0.5 = (1/2)·λ_unit 精确成立
    (÷2 为二进制精确操作, recorded float 无舍入)。 -/
theorem s12_lam_050_exact :
    (1 / 2 : ℚ) * lamUnitResQ = lamRes050Q := by norm_num

/-- **S12 各臂标定校准 (float64 末位舍入级)**: 全部 7 臂的 recorded
    λ_res 与精确有理数 ratio×λ_unit 之差 ≤ 4×10⁻¹⁶ (float64 尾数
    52 bit ≈ 2.2×10⁻¹⁶ 相对精度, 数值 ~5 时绝对尺度)。
    r020/r050/r100/r000 为精确恒等, r035/r065/r080 含 1-3 ulp 舍入。 -/
theorem s12_lam_calibration :
    |(0 : ℚ) - 0 * lamUnitResQ| ≤ 4 / 10 ^ 16
      ∧ |10013650929105948 / 10000000000000000 - (1 / 5 : ℚ) * lamUnitResQ|
          ≤ 4 / 10 ^ 16
      ∧ |17523889125935408 / 10000000000000000 - (7 / 20 : ℚ) * lamUnitResQ|
          ≤ 4 / 10 ^ 16
      ∧ |2503412732276487 / 1000000000000000 - (1 / 2 : ℚ) * lamUnitResQ|
          ≤ 4 / 10 ^ 16
      ∧ |32544365519594334 / 10000000000000000 - (13 / 20 : ℚ) * lamUnitResQ|
          ≤ 4 / 10 ^ 16
      ∧ |4005460371642379 / 1000000000000000 - (4 / 5 : ℚ) * lamUnitResQ|
          ≤ 4 / 10 ^ 16
      ∧ |5006825464552974 / 1000000000000000 - (1 : ℚ) * lamUnitResQ|
          ≤ 4 / 10 ^ 16 := by
  have h1 : (1 / 5 : ℚ) * lamUnitResQ = 10013650929105948 / 10000000000000000 := by
    norm_num [lamUnitResQ]
  have h2 : (7 / 20 : ℚ) * lamUnitResQ = 17523889125935409 / 10000000000000000 := by
    norm_num [lamUnitResQ]
  have h3 : (1 / 2 : ℚ) * lamUnitResQ = 2503412732276487 / 1000000000000000 := by
    norm_num [lamUnitResQ]
  have h4 : (13 / 20 : ℚ) * lamUnitResQ = 32544365519594331 / 10000000000000000 := by
    norm_num [lamUnitResQ]
  have h5 : (4 / 5 : ℚ) * lamUnitResQ = 40054603716423792 / 10000000000000000 := by
    norm_num [lamUnitResQ]
  have h6 : (1 : ℚ) * lamUnitResQ = 5006825464552974 / 1000000000000000 := by
    norm_num [lamUnitResQ]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · rw [h1]; norm_num
  · rw [h2]; norm_num
  · rw [h3]; norm_num
  · rw [h4]; norm_num
  · rw [h5]; norm_num
  · rw [h6]; norm_num

/-- **协议常数登记** (ablation_lrd.py / ablation.py 源码值):
    EMA β = 9/10 (未修正权重 1-β = 1/10);
    LR 衰减: 0.05×0.1 = 1/200 (@it30);
    RATIO = 1/2 主工作点 λ_res = λ_unit/2 (精确);
    检查点 {15,30,50} 之和 = 95, DECAY_AT=30 < ITERS=50。 -/
theorem s12_protocol_regs :
    (1 : ℚ) - 9 / 10 = 1 / 10
      ∧ (1 / 20 : ℚ) * (1 / 10) = 1 / 200
      ∧ (1 / 2 : ℚ) * lamUnitResQ = lamRes050Q
      ∧ (15 + 30 + 50 : ℤ) = 95
      ∧ (30 : ℤ) < 50 := by
  refine ⟨by norm_num, by norm_num, s12_lam_050_exact, by norm_num, by norm_num⟩

end CDD.W2.MeasureEMA
