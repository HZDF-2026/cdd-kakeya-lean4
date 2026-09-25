import CddFormalization.RH_ExplicitFormula
import CddFormalization.RH_SpectralMeasure
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

noncomputable section

/-! # Riemann Hypothesis: 截断 Weil 显式公式 (阶段 2e, 节点 18-21)

    本模块将 RH 等价网络推进到显式公式的核心: 建立 Weil 显式公式的
    三个无条件字典与一个显式声明的组装骨架:

        节点 18: 素数侧字典 — 对数坐标素数谱测度 μ_p = Σ' Λ(n)·δ_{log n},
                  ψ 的累积分布刻画与 Laplace/Mellin-L 级数三重量等同
        节点 19: 残差字典 — -ζ'/ζ 的奇点主部字典:
                  极点 1 分离 (=(s-1)⁻¹ - ζ₁'/ζ₁) + 零点阶数分解
                  (ζ'/ζ = m/(s-ρ) + 解析余项) + 圆道留数 ∮ = -2πi·m
        节点 20: 截断零点和 — T-横带截断零点集的反射不变性与重心定理
                  (Σ Re ρ = |Z_T|/2, 无条件的谱侧一阶矩)
        节点 21: 单项字典 + 组装骨架 — 谱项 (s-ρ)⁻¹ 与素数项 t^ρ 的
                  Mellin 逐项对偶; Hadamard 部分分式缺口作为显式假设

    ## 结构设计: 为什么用"字典 + 截断 + 骨架"

    完整 Weil 显式公式 ψ(x) = x - Σ_ρ x^ρ/ρ - ζ'(0)/ζ(0) - ... 需要
    -ζ'/ζ 的全局部分分式展开, 其解析基础是 ζ 的 Hadamard 乘积
    (Mathlib 尚无). 本模块的诚实策略:

    * **无条件部分** (节点 18-20): 素数侧与谱侧的全部局部字典完全证明 —
      ψ 的测度论结构、-ζ'/ζ 的每个奇点的留数 (极点 +1, m 重零点 -m)、
      截断零点集的组合对称性. 这些是显式公式中"不含 Hadamard"的全部内容.
    * **截断策略** (节点 20): 零点和取 T-横带截断 (有限集), 回避
      条件收敛与重排问题; 重心定理给出截断谱的无条件一阶矩.
    * **显式骨架** (节点 21, 2026-09-08 K2 拆分): 可证层 (21b-a) 以典范
      余项 `hadamardRemainder` 给出定义级分解与无条件组装; 未证层 (21b-b)
      以具名假设 `hadamard_gap_hypothesis` (axiom-风格显式登记) 承载
      Hadamard 缺口, 组装定理以「已证桥 + 未证假设」两式并列给出.
      最后一个缺口 — Mellin 反演的垂直可积性在 ψ 上失败 (阶梯函数的
      谱衰减不足) — 被精确化为单一假设 `VerticalIntegrable`,
      作为反演骨架的条件形式.

    ## 与既有网络的接口

    * 节点 11 (`RH_ExplicitFormula.neg_logDeriv_eq_mul_mellin`):
      -ζ'/ζ = s·𝓜[ψ](-s) — 节点 18 的第四重量、节点 21 组装的入口;
    * 节点 15-17 (`RH_SpectralMeasure`): 谱高度测度 μ_spec — 节点 18 的
      μ_p 是其对偶 (零点谱 ↔ 素数谱), 两个谱测度经 Weil 公式配对;
    * `stripZeros_finite` (节点 15 基础): 节点 20 截断集的有限性来源;
    * 节点 12-14 (`RH_DeviationMeasure`): 偏差测度 d(R) 是截断零点实部
      分布的零阶信息, 节点 20 重心定理是其一阶矩对偶 —
      无条件下截断零点实部均值恒为 1/2, RH ⟺ 高阶矩全部塌缩.

    ## 诚实边界 (不可宣称的内容)

    - Hadamard 乘积与 -ζ'/ζ 全局部分分式: 以具名假设
      `hadamard_gap_hypothesis` 显式登记 (axiom-风格未证假设,
      非隐藏结构字段), 不证明;
    - ψ 上的 Mellin 反演: 垂直可积性失败 (Σ Λ(n)·n^{-σ-iy}/|y| 型
      衰减不足), 完整 Weil 公式需分布/光滑紧支测试函数技术;
    - 零点计数密度、λₙ 收敛性分析: 维持原边界, 不在本模块触碰.

    References:
    - Weil (1952) Sur les "formules explicites" de la théorie des nombres premiers
    - von Mangoldt (1895) Zu Riemann's Abhandlung über die Anzahl der Primzahlen
    - Edwards (1974) Riemann's Zeta Function, §1.10-1.12, §2.1-2.3
    - Iwaniec & Kowalski (2004) Analytic Number Theory, §4.4-4.5
    - RH_ExplicitFormula.lean (节点 10-11: Mellin 桥接)
    - RH_SpectralMeasure.lean (节点 15-17: 谱测度)
-/

namespace RHWeilFormula

open RHMeasureTheory RHExplicitFormula RHSpectralMeasure Chebyshev ArithmeticFunction
open MeasureTheory LSeries Set Complex Filter Metric
open scoped Chebyshev Topology ENNReal Real

-- ============================================================
-- 1. 节点 18: 素数侧字典 — 对数坐标素数谱测度
-- ============================================================

/-- 对数坐标素数谱测度 (节点 18): `μ_p := Σ'_n Λ(n) • δ_{log n}`.

    Hilbert-Pólya 谱高度测度 `μ_spec = Im_* μ_Z` (节点 15) 刻画零点能级
    高度谱; `μ_p` 是其素数侧对偶: 原子位于素数幂的对数 `log n`, 质量为
    von Mangoldt 函数 `Λ(n) = log p` (n = p^k). Weil 显式公式的测度论
    本质即: 两个离散谱测度 (素数谱 / 零点谱) 经 Mellin-Fourier 对偶
    逐项配对. -/
def logPrimeMeasure : Measure ℝ :=
  Measure.sum fun n : ℕ =>
    (ENNReal.ofReal (Λ n)) • Measure.dirac (Real.log (n : ℝ))

/-- 地板不等式辅理: `⌊e^u⌋ < n ⟹ e^u < n`, 用于截断指标的界传递. -/
private lemma key_floor (u : ℝ) (n : ℕ) (h : ⌊Real.exp u⌋₊ < n) : Real.exp u < (n : ℝ) := by
  have h1 : Real.exp u < ((⌊Real.exp u⌋₊ : ℝ) + 1) := Nat.lt_floor_add_one (Real.exp u)
  have h2 : ((⌊Real.exp u⌋₊ : ℝ) + 1) ≤ (n : ℝ) := by
    have : ⌊Real.exp u⌋₊ + 1 ≤ n := by omega
    exact_mod_cast this
  linarith

/-- 素数谱测度的原子质量 (节点 18): `log n` 处的质量为 `Λ(n)` (n ≥ 2, 即素数幂域).

    `log` 在 [2, ∞) 上严格单调保证原子无碰撞; n ∈ {0, 1} 处 Λ = 0,
    不属于素数侧对象. 测度和公式把 μ_p({log n}) 化为
    `Σ' Λ(k)·1_{log k = log n}`, 注入性使级数坍缩为单项 `Λ(n)`. -/
theorem logPrimeMeasure_apply_singleton (n : ℕ) (hn : 2 ≤ n) :
    logPrimeMeasure ({Real.log (n : ℝ)} : Set ℝ) = ENNReal.ofReal (Λ n) := by
  classical
  have hlogn : (0 : ℝ) < Real.log (n : ℝ) := by
    apply Real.log_pos
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  rw [logPrimeMeasure, Measure.sum_apply _ (measurableSet_singleton _)]
  simp only [Measure.smul_apply, Measure.dirac_apply, Set.indicator_apply, Pi.one_apply,
    Set.mem_singleton_iff, smul_eq_mul, mul_ite_zero, mul_one]
  have hlog_inj : ∀ k : ℕ, k ≠ n → Real.log (k : ℝ) ≠ Real.log (n : ℝ) := by
    intro k hke
    by_cases hk2 : 2 ≤ k
    · have hposk : (0 : ℝ) < (k : ℝ) := by
        have : 0 < k := by omega
        exact_mod_cast this
      have hposn : (0 : ℝ) < (n : ℝ) := by
        have : 0 < n := by omega
        exact_mod_cast this
      intro h
      have h2 : Real.exp (Real.log (k : ℝ)) = Real.exp (Real.log (n : ℝ)) := by rw [h]
      rw [Real.exp_log hposk, Real.exp_log hposn] at h2
      exact hke (by exact_mod_cast h2)
    · have hk01 : k = 0 ∨ k = 1 := by omega
      rcases hk01 with rfl | rfl
      · rw [show Real.log ((0 : ℕ) : ℝ) = 0 by simp]
        exact (ne_of_gt hlogn).symm
      · rw [show Real.log ((1 : ℕ) : ℝ) = 0 by simp]
        exact (ne_of_gt hlogn).symm
  have hkey : ∀ k : ℕ,
      (if Real.log (k : ℝ) = Real.log (n : ℝ) then ENNReal.ofReal (Λ k) else 0)
        = if k = n then ENNReal.ofReal (Λ k) else 0 := by
    intro k
    by_cases hkn : k = n
    · subst hkn
      simp
    · rw [if_neg (hlog_inj k hkn), if_neg hkn]
  rw [tsum_congr hkey]
  rw [tsum_eq_sum (s := ({n} : Finset ℕ)) (fun k hk => by
    rw [Finset.mem_singleton] at hk
    rw [if_neg hk])]
  simp

/-- 素数谱测度的累积分布刻画 (节点 18 核心): `μ_p(-∞, u] = ψ(eᵘ)`.

    ψ 是素数谱测度 (对数坐标) 的累积分布函数: 素数计数信息完全编码于
    μ_p 的分布函数. 证明: 测度和公式把 μ_p(Iic u) 化为
    `Σ' Λ(n)·1_{log n ≤ u}`; 而 `log n ≤ u ⟺ n ≤ e^u`, 截断外 Λ 为零
    使级数坍缩为有限和 `Σ_{n ≤ e^u} Λ(n) = ψ(e^u)` (`psi_eq_sum_Icc`).

    这是 Weil 显式公式素数侧的测度论形式: ψ(x) 恰是素数谱测度在
    对数坐标下的分布函数, 显式公式的左端从此以测度论语言陈述. -/
theorem logPrimeMeasure_Iic_eq_psi (u : ℝ) :
    logPrimeMeasure (Set.Iic u) = ENNReal.ofReal (ψ (Real.exp u)) := by
  classical
  set N := ⌊Real.exp u⌋₊ with hN
  have hpsi : ψ (Real.exp u) = ∑ n ∈ Finset.Icc 0 N, Λ n := by
    rw [Chebyshev.psi_eq_sum_Icc (Real.exp u), hN]
  rw [logPrimeMeasure, Measure.sum_apply _ measurableSet_Iic]
  simp only [Measure.smul_apply, Measure.dirac_apply, Set.indicator_apply, Pi.one_apply,
    Set.mem_Iic, smul_eq_mul, mul_ite_zero, mul_one]
  have hkey : ∀ n : ℕ,
      (if Real.log (n : ℝ) ≤ u then ENNReal.ofReal (Λ n) else 0)
        = if n ≤ N then ENNReal.ofReal (Λ n) else 0 := by
    intro n
    by_cases hn0 : n = 0
    · subst hn0
      simp [vonMangoldt_eq_zero_iff.mpr not_isPrimePow_zero]
    · have hpos : (0 : ℝ) < (n : ℝ) := by
        have : 0 < n := Nat.pos_of_ne_zero hn0
        exact_mod_cast this
      by_cases hn : n ≤ N
      · rw [if_pos hn]
        have hnle : (n : ℝ) ≤ Real.exp u := by
          have h1 : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn
          exact h1.trans (Nat.floor_le (Real.exp_nonneg u))
        rw [if_pos ((Real.log_le_log hpos hnle).trans_eq (Real.log_exp u))]
      · rw [if_neg hn]
        have hnotlog : ¬ (Real.log (n : ℝ) ≤ u) := by
          intro hle
          have hnle : (n : ℝ) ≤ Real.exp u := by
            rw [← Real.exp_log hpos]
            exact Real.exp_le_exp.mpr hle
          have hgt : Real.exp u < (n : ℝ) := key_floor u n (by omega)
          exact absurd hgt (not_lt.mpr hnle)
        rw [if_neg hnotlog]
  rw [tsum_congr hkey]
  rw [tsum_eq_sum (s := Finset.Icc 0 N) (fun n hn => by
    have h : ¬ (n ≤ N) := by
      intro hc
      exact hn (Finset.mem_Icc.mpr ⟨Nat.zero_le n, hc⟩)
    exact if_neg h)]
  rw [Finset.sum_congr rfl (fun n hn => if_pos (Finset.mem_Icc.mp hn).2)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => vonMangoldt_nonneg (n := n)), ← hpsi]

/-- 素数谱测度的 Laplace-L 级数字典 (节点 18 核心): Re s > 1 时

        ∫ u, e^{-s·u} ∂μ_p = Σ' Λ(n)·n^{-s} = L ↗Λ s = -ζ'(s)/ζ(s).

    证明: `integral_sum_dirac_eq_tsum` 把 μ_p 的 Laplace 积分化为
    `Σ' Λ(n)·e^{-s·log n}`; 由 `exp(-s·log n) = n^{-s}` 与 L 级数定义
    (`term_def₀` 展开即 `Λ(n)·n^{-s}`) 相消, 再经
    `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` 接到谱侧.

    这是素数侧字典的枢纽: 素数测度的 Laplace 变换 = von Mangoldt
    L 级数 = ζ 的负对数导数, 三个素数侧对象无条件等同, 并与谱侧
    对象 (-ζ'/ζ) 在 Re s > 1 完全挂钩. 节点 11 的 Mellin 桥接
    (-ζ'/ζ = s·𝓜[ψ](-s)) 由此获得第四种表述: μ_p 的 Laplace 变换. -/
theorem integral_exp_logPrimeMeasure_eq_neg_logDeriv (s : ℂ) (hs : 1 < s.re) :
    ∫ u : ℝ, Complex.exp (-s * u) ∂logPrimeMeasure
      = -deriv riemannZeta s / riemannZeta s := by
  classical
  have hcpow : ∀ n : ℕ, n ≠ 0 → Complex.exp (-s * Real.log (n : ℝ)) = ((n : ℂ) ^ (-s)) := by
    intro n hn
    have hne : ((n : ℂ)) ≠ 0 := by exact_mod_cast hn
    rw [Complex.cpow_def_of_ne_zero hne, Complex.ofReal_log (Nat.cast_nonneg (α := ℝ) n)]
    rw [mul_comm]
    rfl
  have hpt : ∀ n : ℕ,
      (ENNReal.ofReal (Λ n)).toReal • Complex.exp (-s * Real.log (n : ℝ))
        = LSeries.term (fun k => (Λ k : ℂ)) s n := by
    intro n
    rw [ENNReal.toReal_ofReal (vonMangoldt_nonneg (n := n))]
    by_cases hn : n = 0
    · subst hn
      simp [vonMangoldt_eq_zero_iff.mpr not_isPrimePow_zero]
    · rw [LSeries.term_def₀ (f := fun k => (Λ k : ℂ))
        (by simp [vonMangoldt_eq_zero_iff.mpr not_isPrimePow_zero]) s n, hcpow n hn]
      rfl
  have hsumm : Summable fun n : ℕ =>
      (ENNReal.ofReal (Λ n)).toReal * ‖Complex.exp (-s * Real.log (n : ℝ))‖ := by
    have h' : Summable fun n : ℕ => LSeries.term (fun k => (Λ k : ℂ)) s n :=
      LSeriesSummable_vonMangoldt hs
    have h2 : Summable fun n : ℕ =>
        (ENNReal.ofReal (Λ n)).toReal • Complex.exp (-s * Real.log (n : ℝ)) :=
      h'.congr (fun n => (hpt n).symm)
    refine h2.norm.congr (fun n => ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  rw [logPrimeMeasure]
  rw [integral_sum_dirac_eq_tsum (c := fun n : ℕ => ENNReal.ofReal (Λ n))
      (x := fun n : ℕ => Real.log (n : ℝ)) (f := fun u : ℝ => Complex.exp (-s * u))
      (fun n => ENNReal.ofReal_ne_top) hsumm]
  rw [tsum_congr hpt]
  rw [(LSeriesSummable_vonMangoldt hs).LSeriesHasSum.tsum_eq]
  rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]

-- ============================================================
-- 2. 节点 19: 残差字典 — -ζ'/ζ 的奇点主部
-- ============================================================

/-! ### 19a. 极点分离: s = 1 处 -ζ'/ζ = (s-1)⁻¹ - ζ₁'/ζ₁ -/

/-- 极点分离下的对数导数恒等式 (节点 19a): s ≠ 1 且 ζ s ≠ 0 时

        -ζ'(s)/ζ(s) = (s-1)⁻¹ - ζ₁'(s)/ζ₁(s).

    ζ₁ = (s-1)·ζ 是 s = 1 极点的乘法分解 (`riemannZeta_eq_inv_sub_mul`),
    取对数导数即得: 极点 s = 1 对 -ζ'/ζ 的贡献是孤立主部 (s-1)⁻¹,
    剩余 -ζ₁'/ζ₁ 在 ζ₁ ≠ 0 处 (特别地在 s = 1 附近) 解析. -/
theorem neg_logDeriv_eq_inv_sub_logDeriv_zetaOne {s : ℂ} (hs : s ≠ 1)
    (hζ : riemannZeta s ≠ 0) :
    -deriv riemannZeta s / riemannZeta s
      = (s - 1)⁻¹ - deriv riemannZeta₁ s / riemannZeta₁ s := by
  have h1 : riemannZeta s = (s - 1)⁻¹ * riemannZeta₁ s := riemannZeta_eq_inv_sub_mul hs
  have h2 : deriv riemannZeta s = -((s - 1)⁻¹) ^ 2 * riemannZeta₁ s
      + (s - 1)⁻¹ * deriv riemannZeta₁ s :=
    deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hs
  have h3 : riemannZeta₁ s ≠ 0 := fun h => hζ (by rw [h1, h, mul_zero])
  have h4 : s - 1 ≠ 0 := sub_ne_zero_of_ne hs
  rw [h1, h2]
  field_simp
  ring

/-- 残差字典 · 极点项 (节点 19a 核心): -ζ'/ζ 在极点 s = 1 处的留数为 +1.

    存在 R > 0, 使得 0 < r < R 时 ∮_{|z-1|=r} (-ζ'(z)/ζ(z)) dz = 2πi·(+1).
    证明: ζ₁ 1 = 1 ≠ 0 与连续性给出 ζ₁ ≠ 0 的球; 球上 -ζ'/ζ 逐点等于
    (z-1)⁻¹ - ζ₁'/ζ₁ (19a); 围道积分线性分解为
    ∮ (z-1)⁻¹ = 2πi (`integral_sub_center_inv`) 与
    ∮ ζ₁'/ζ₁ = 0 (ζ₁'/ζ₁ 在球上可微, Cauchy-Goursat 零积分). -/
theorem exists_circleIntegral_neg_logDeriv_one :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      (∮ z in C(1, r), -deriv riemannZeta z / riemannZeta z) = 2 * π * I := by
  obtain ⟨R, hRpos, hR⟩ := Metric.eventually_nhds_iff_ball.mp riemannZeta₁_ne_zero_of_near_one
  refine ⟨R, hRpos, fun r hr hrR => ?_⟩
  -- 球上 ζ₁ ≠ 0, 且球内不含其他奇点
  have hsph : ∀ z ∈ sphere (1 : ℂ) r, z ∈ Metric.ball 1 R := by
    intro z hz
    have hdist : dist z 1 = r := Metric.mem_sphere.mp hz
    rw [Metric.mem_ball, hdist]
    exact hrR
  have hzne : ∀ z ∈ sphere (1 : ℂ) r, z ≠ 1 := by
    intro z hz h
    rw [h] at hz
    rw [Metric.mem_sphere, dist_self] at hz
    linarith
  -- 被积函数在圆周上逐点等于分离形式
  have hcongr : EqOn (fun z => -deriv riemannZeta z / riemannZeta z)
      (fun z => (z - 1)⁻¹ - deriv riemannZeta₁ z / riemannZeta₁ z) (sphere (1 : ℂ) r) := by
    intro z hz
    have hz1 : z ≠ 1 := hzne z hz
    have hζ1 : riemannZeta₁ z ≠ 0 := hR z (hsph z hz)
    have hζ : riemannZeta z ≠ 0 := by
      rw [riemannZeta_eq_inv_sub_mul hz1]
      exact mul_ne_zero (inv_ne_zero (sub_ne_zero_of_ne hz1)) hζ1
    exact neg_logDeriv_eq_inv_sub_logDeriv_zetaOne hz1 hζ
  -- 两个分量的可积性 (圆周上连续; (z-1)⁻¹ 在圆周上无零点)
  have hcinv : ContinuousOn (fun z : ℂ => (z - 1)⁻¹) (sphere (1 : ℂ) r) :=
    (continuous_id.sub continuous_const).continuousOn.inv₀
      (fun z hz => sub_ne_zero_of_ne (hzne z hz))
  have hclog : ContinuousOn (fun z : ℂ => deriv riemannZeta₁ z / riemannZeta₁ z)
      (sphere (1 : ℂ) r) :=
    (differentiable_riemannZeta₁.deriv.continuous).continuousOn.div
      differentiable_riemannZeta₁.continuous.continuousOn
      (fun z hz => hR z (hsph z hz))
  -- ζ₁'/ζ₁ 在闭环盘上可微 (Cauchy-Goursat 的前提)
  have hDC : DiffContOnCl ℂ (fun z : ℂ => deriv riemannZeta₁ z / riemannZeta₁ z)
      (ball (1 : ℂ) r) := by
    have hd : DifferentiableOn ℂ (fun z : ℂ => deriv riemannZeta₁ z / riemannZeta₁ z)
        (Metric.ball (1 : ℂ) R) := by
      intro z hz
      exact ((differentiable_riemannZeta₁.deriv z).div (differentiable_riemannZeta₁ z)
        (hR z hz)).differentiableWithinAt
    refine hd.diffContOnCl_ball ?_
    intro z hz
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt hz hrR
  rw [circleIntegral.integral_congr (le_of_lt hr) hcongr]
  rw [circleIntegral.integral_sub (hcinv.circleIntegrable (le_of_lt hr))
    (hclog.circleIntegrable (le_of_lt hr))]
  rw [circleIntegral.integral_sub_center_inv 1 (ne_of_gt hr)]
  rw [hDC.circleIntegral_eq_zero (le_of_lt hr)]
  ring

/-! ### 19b. 零点阶数分解: ζ'/ζ = m/(s-ρ) + 解析余项 -/

/-- ζ 不在非极点的邻域内恒为零 (身份定理推论, 节点 19b 辅理):
    若 ρ ≠ 1 且 ζ 在 ρ 邻域内恒为零, 则由解析延拓唯一性
    ζ 在预连通集 {1}ᶜ 上恒为零, 与 ζ 2 ≠ 0 (`riemannZeta_ne_zero_of_one_le_re`)
    矛盾. 这排除 ζ 零点阶数为 ⊤ 的退化情形. -/
private theorem eventually_zero_riemannZeta_false (ρ : ℂ) (hρ1 : ρ ≠ 1)
    (hev : ∀ᶠ s in 𝓝 ρ, riemannZeta s = 0) : False := by
  have hρc : ρ ∈ ({1} : Set ℂ)ᶜ := by simpa using hρ1
  have heqOn : Set.EqOn riemannZeta (fun _ => (0 : ℂ)) ({1} : Set ℂ)ᶜ :=
    analyticOn_riemannZeta.eqOn_of_preconnected_of_eventuallyEq
      (analyticOnNhd_const (v := (0 : ℂ)))
      (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
      hρc (hev.mono fun s hs => hs)
  have h2ne : riemannZeta (2 : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by norm_num)
  exact h2ne (heqOn (by simp))

/-- 零点阶数分解 (节点 19b 核心): ρ ≠ 1 是 ζ 的零点时, 其解析阶

        m := analyticOrderNatAt riemannZeta ρ

    自动有限且 ≥ 1 (身份定理排除 ⊤, ζ ρ = 0 排除 0), 且 ζ'/ζ 在 ρ 的
    去心邻域内分解为 m/(s-ρ) + h(s), 其中余项 h = g'/g 解析
    (g 为阶数分解 ζ = (s-ρ)^m · g 的解析余因子, g ρ ≠ 0).

    这是 -ζ'/ζ 在零点 ρ 处的局部主部字典: 主部恰为 -m/(s-ρ),
    留数为 -m. 证明: 对 ζ = (s-ρ)^m · g 求导 (EventuallyEq 导数传递 +
    乘积法则), 代入 ζ'/ζ 后 (s-ρ)^m 因子相消. -/
theorem exists_logDeriv_zero_order_decomposition (ρ : ℂ) (hρ : riemannZeta ρ = 0)
    (hρ1 : ρ ≠ 1) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧
      ∀ᶠ s in 𝓝[≠] ρ, deriv riemannZeta s / riemannZeta s
        = (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ) + h s := by
  have hA : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ (by simpa using hρ1)
  have hfin : analyticOrderAt riemannZeta ρ ≠ ⊤ := fun h =>
    eventually_zero_riemannZeta_false ρ hρ1 (analyticOrderAt_eq_top.mp h)
  obtain ⟨g, hgA, hg0, hgdecomp⟩ := (hA.analyticOrderAt_ne_top).mp hfin
  set m := analyticOrderNatAt riemannZeta ρ with hm_def
  -- 零点阶数 m ≥ 1: 若 m = 0, 则 ζ ρ = (ρ-ρ)^0 • g ρ = g ρ ≠ 0 与 ρ 是零点矛盾
  have hm : (1 : ℕ) ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · exfalso
      have hself : riemannZeta ρ = (ρ - ρ) ^ m • g ρ := hgdecomp.self_of_nhds
      rw [h0, hρ] at hself
      simp only [sub_self, pow_zero, one_smul] at hself
      exact hg0 hself.symm
    · exact hpos
  -- 阶数分解的球形式: ball ρ R₀ 内 ζ = (·-ρ)^m · g
  obtain ⟨R₀, hR₀pos, hR₀⟩ := Metric.eventually_nhds_iff_ball.mp
    (show ∀ᶠ z in 𝓝 ρ, riemannZeta z = (z - ρ) ^ m * g z by
      filter_upwards [hgdecomp] with z hz
      rw [hz, smul_eq_mul])
  -- g 的解析球与 g ≠ 0 的球 (连续性 + g ρ ≠ 0)
  obtain ⟨R₁, hR₁pos, hR₁ball⟩ := hgA.exists_ball_analyticOnNhd
  obtain ⟨R₂, hR₂pos, hR₂ne⟩ := Metric.eventually_nhds_iff_ball.mp
    (hgA.continuousAt.eventually_ne hg0)
  -- 分解函数 F := (·-ρ)^m · g 在 ball ρ R₀ 内每点的邻域上与 ζ eventually 相等,
  -- 故导数逐点相等 (EventuallyEq.deriv_eq)
  have hderBall : ∀ s ∈ Metric.ball ρ R₀,
      deriv riemannZeta s = deriv (fun u => (u - ρ) ^ m * g u) s := by
    intro s hs
    have hEq : riemannZeta =ᶠ[𝓝 s] (fun u => (u - ρ) ^ m * g u) :=
      Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hs)
        (fun z hz => hR₀ z hz)
    exact hEq.deriv_eq
  refine ⟨fun s => deriv g s / g s, hgA.deriv.div hgA hg0, ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ s in 𝓝 ρ, s ∈ Metric.ball ρ (min R₀ (min R₁ R₂)) from
      Metric.ball_mem_nhds ρ (lt_min hR₀pos (lt_min hR₁pos hR₂pos))).filter_mono
      (nhdsWithin_le_nhds : 𝓝[≠] ρ ≤ 𝓝 ρ)] with s hs5 hsB
  have hsB₀ : s ∈ Metric.ball ρ R₀ :=
    Metric.ball_subset_ball (min_le_left _ _) hsB
  have hsB₁ : s ∈ Metric.ball ρ R₁ :=
    Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hsB
  have hsB₂ : s ∈ Metric.ball ρ R₂ :=
    Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hsB
  have hs2 : DifferentiableAt ℂ g s := (hR₁ball s hsB₁).differentiableAt
  have hs3 : g s ≠ 0 := hR₂ne s hsB₂
  have hs4 : riemannZeta s = (s - ρ) ^ m * g s := hR₀ s hsB₀
  have hs1 : deriv riemannZeta s = deriv (fun u => (u - ρ) ^ m * g u) s :=
    hderBall s hsB₀
  -- 乘积法则: ((u-ρ)^m · g)' = m·(s-ρ)^(m-1)·g + (s-ρ)^m·g'
  have hprod : deriv (fun u => (u - ρ) ^ m * g u) s
      = (m : ℂ) * (s - ρ) ^ (m - 1) * g s + (s - ρ) ^ m * deriv g s := by
    have h1 : HasDerivAt (fun u : ℂ => u - ρ) 1 s := (hasDerivAt_id s).sub_const ρ
    have h2 : HasDerivAt (fun u : ℂ => (u - ρ) ^ m)
        ((m : ℂ) * (s - ρ) ^ (m - 1) * 1) s := h1.pow _
    have h3 : HasDerivAt (fun u : ℂ => (u - ρ) ^ m * g u)
        ((m : ℂ) * (s - ρ) ^ (m - 1) * 1 * g s + (s - ρ) ^ m * deriv g s) s :=
      h2.mul hs2.hasDerivAt
    rw [h3.deriv]
    ring
  have ht : s - ρ ≠ 0 := sub_ne_zero_of_ne hs5
  rw [hs1, hprod, hs4]
  -- 幂次代数: (s-ρ)^m = (s-ρ)^(m-1) · (s-ρ) (m ≥ 1)
  have hpow : (s - ρ) ^ m = (s - ρ) ^ (m - 1) * (s - ρ) := by
    have h1 : m - 1 + 1 = m := by omega
    rw [← h1, Nat.add_sub_cancel, pow_succ]
  have hxk : (s - ρ) ^ (m - 1) ≠ 0 := pow_ne_zero _ ht
  rw [hpow]
  field_simp [ht, hxk, hs3]

/-- 零点孤立性 (节点 19b 推论): ζ 的每个零点 ρ ≠ 1 都有只含自身的零点邻域.

    由阶数分解 ζ = (s-ρ)^m · g (g 解析非零), 球内零点只能是 ρ 本身.
    这保证残差定理 (19c) 中围绕 ρ 的小圆周不穿过、不包含其他零点. -/
theorem exists_ball_inter_riemannZetaZeros_eq_singleton (ρ : ℂ) (hρ : riemannZeta ρ = 0)
    (hρ1 : ρ ≠ 1) :
    ∃ R : ℝ, 0 < R ∧ ∀ z ∈ Metric.ball ρ R, riemannZeta z = 0 → z = ρ := by
  have hA : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ (by simpa using hρ1)
  have hfin : analyticOrderAt riemannZeta ρ ≠ ⊤ := fun h =>
    eventually_zero_riemannZeta_false ρ hρ1 (analyticOrderAt_eq_top.mp h)
  obtain ⟨g, hgA, hg0, hgdecomp⟩ := (hA.analyticOrderAt_ne_top).mp hfin
  set m := analyticOrderNatAt riemannZeta ρ with hm_def
  have hm : (1 : ℕ) ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · exfalso
      have hself : riemannZeta ρ = (ρ - ρ) ^ m • g ρ := hgdecomp.self_of_nhds
      rw [h0, hρ] at hself
      simp only [sub_self, pow_zero, one_smul] at hself
      exact hg0 hself.symm
    · exact hpos
  obtain ⟨R₀, hR₀pos, hR₀⟩ := Metric.eventually_nhds_iff_ball.mp
    (show ∀ᶠ z in 𝓝 ρ, riemannZeta z = (z - ρ) ^ m * g z by
      filter_upwards [hgdecomp] with z hz
      rw [hz, smul_eq_mul])
  obtain ⟨R₁, hR₁pos, hR₁ne⟩ := Metric.eventually_nhds_iff_ball.mp
    (hgA.continuousAt.eventually_ne hg0)
  refine ⟨min R₀ R₁, lt_min hR₀pos hR₁pos, fun z hz hz0 => ?_⟩
  have hg0z : g z ≠ 0 := hR₁ne z (Metric.ball_subset_ball (min_le_right _ _) hz)
  have hdz : riemannZeta z = (z - ρ) ^ m * g z :=
    hR₀ z (Metric.ball_subset_ball (min_le_left _ _) hz)
  rw [hz0] at hdz
  have hpow : (z - ρ) ^ m = 0 := by
    rcases mul_eq_zero.mp hdz.symm with h | h
    · exact h
    · exact absurd h hg0z
  exact sub_eq_zero.mp (pow_eq_zero_iff (by omega) |>.mp hpow)

/-! ### 19c. 围道留数: ∮_{|z-ρ|=r} ζ'/ζ dz = 2πi·m -/

/-- 残差字典 · 零点项 (节点 19c 核心): m 重零点 ρ ≠ 1 处 ζ'/ζ 的留数为 +m.

    存在 R > 0, 使得 0 < r < R 时
        ∮_{|z-ρ|=r} ζ'(z)/ζ(z) dz = 2πi·m,  m = analyticOrderNatAt riemannZeta ρ.
    证明: 19b 的去心邻域分解 ζ'/ζ = m/(z-ρ) + h 在圆周上逐点成立
    (零点孤立性保证 ρ 是球内唯一零点); 围道积分线性分解为
    ∮ m/(z-ρ) = m·2πi (`integral_sub_center_inv`) 与 ∮ h = 0
    (h 解析, Cauchy-Goursat 零积分).

    与 19a 合并: -ζ'/ζ 的奇点主部字典为 极点 1 ↦ +(s-1)⁻¹ (留数 +1),
    m 重零点 ρ ↦ -m/(s-ρ) (留数 -m) — Weil 显式公式谱侧的全部局部信息. -/
theorem exists_circleIntegral_logDeriv_eq_mul_order (ρ : ℂ) (hρ : riemannZeta ρ = 0)
    (hρ1 : ρ ≠ 1) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      (∮ z in C(ρ, r), deriv riemannZeta z / riemannZeta z)
        = 2 * π * I * (analyticOrderNatAt riemannZeta ρ : ℂ) := by
  obtain ⟨h, hA, hev⟩ := exists_logDeriv_zero_order_decomposition ρ hρ hρ1
  -- 从"最终成立"提取球半径
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff_ball.mp
    (eventually_nhdsWithin_iff.mp hev)
  -- h 的解析球
  obtain ⟨R₁, hR₁pos, hball⟩ := hA.exists_ball_analyticOnNhd
  refine ⟨min δ R₁, lt_min hδpos hR₁pos, fun r hr hrR => ?_⟩
  have hsphδ : ∀ z ∈ sphere ρ r, z ∈ Metric.ball ρ δ := by
    intro z hz
    have hdist : dist z ρ = r := Metric.mem_sphere.mp hz
    rw [Metric.mem_ball, hdist]
    exact lt_of_lt_of_le hrR (min_le_left δ R₁)
  have hsph1 : ∀ z ∈ sphere ρ r, z ∈ Metric.ball ρ R₁ := by
    intro z hz
    have hdist : dist z ρ = r := Metric.mem_sphere.mp hz
    rw [Metric.mem_ball, hdist]
    exact lt_of_lt_of_le hrR (min_le_right δ R₁)
  have hzne : ∀ z ∈ sphere ρ r, z ≠ ρ := by
    intro z hz h
    rw [h] at hz
    rw [Metric.mem_sphere, dist_self] at hz
    linarith
  -- 圆周上被积函数逐点等于 m/(z-ρ) + h
  have hcongr : EqOn (fun z => deriv riemannZeta z / riemannZeta z)
      (fun z => (analyticOrderNatAt riemannZeta ρ : ℂ) / (z - ρ) + h z) (sphere ρ r) := by
    intro z hz
    exact hδ z (hsphδ z hz) (hzne z hz)
  -- 两个分量的可积性
  have hcinv : ContinuousOn (fun z : ℂ => (analyticOrderNatAt riemannZeta ρ : ℂ) / (z - ρ))
      (sphere ρ r) :=
    continuousOn_const.div (continuous_id.sub continuous_const).continuousOn
      (fun z hz => sub_ne_zero_of_ne (hzne z hz))
  have hch : ContinuousOn h (sphere ρ r) :=
    hball.continuousOn.mono (fun z hz => hsph1 z hz)
  -- h 在闭环盘上可微
  have hDC : DiffContOnCl ℂ h (ball ρ r) := by
    refine (hball.differentiableOn).diffContOnCl_ball ?_
    intro z hz
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    calc dist z ρ ≤ r := hz
      _ < R₁ := lt_of_lt_of_le hrR (min_le_right δ R₁)
  -- 主部积分: ∮ m/(z-ρ) = m · 2πi
  have hI : (∮ z in C(ρ, r), (analyticOrderNatAt riemannZeta ρ : ℂ) / (z - ρ))
      = (analyticOrderNatAt riemannZeta ρ : ℂ) * (2 * π * I) := by
    rw [circleIntegral.integral_congr (le_of_lt hr) (fun z _ => div_eq_mul_inv _ _),
      circleIntegral.integral_const_mul, circleIntegral.integral_sub_center_inv ρ (ne_of_gt hr)]
  rw [circleIntegral.integral_congr (le_of_lt hr) hcongr]
  rw [circleIntegral.integral_add (hcinv.circleIntegrable (le_of_lt hr))
    (hch.circleIntegrable (le_of_lt hr))]
  rw [hI, hDC.circleIntegral_eq_zero (le_of_lt hr)]
  ring

-- ============================================================
-- 3. 节点 20: 截断零点和 — 反射不变性与重心定理
-- ============================================================

/-- T-横带截断零点集 (节点 20): 高度 `|Im| ≤ T` 的非平凡零点.

    这是 Weil 显式公式中零点和的诚实截断: T-横带内的非平凡零点有限
    (`RHSpectralMeasure.stripZeros_finite`), 有限和回避零点级数的
    条件收敛与重排问题, 是谱侧字典的有限载体. -/
def stripZeros (T : ℝ) : Set ℂ := nontrivialZeros ∩ {z : ℂ | |z.im| ≤ T}

/-- T-横带截断零点集有限 (节点 20 基础). -/
theorem stripZeros_finite' (T : ℝ) : (stripZeros T).Finite :=
  RHSpectralMeasure.stripZeros_finite T

/-- 反射不变性 (节点 20a): T-横带截断零点集在函数方程反射 `ρ ↦ 1-ρ` 下不变.

    反射保持非平凡性 (`zero_symmetry`, 节点 13) 且 `|Im(1-ρ)| = |Im ρ|`,
    故横带截断与反射交换. 这使反射成为截断零点集上的对合,
    是重心定理的组合引擎: 每个零点与其反射配对, 实部相加恒为 1. -/
theorem one_sub_mem_stripZeros {T : ℝ} {ρ : ℂ} (hρ : ρ ∈ stripZeros T) :
    1 - ρ ∈ stripZeros T := by
  obtain ⟨hnt, him⟩ := hρ
  refine ⟨zero_symmetry hnt, ?_⟩
  simp only [Set.mem_setOf_eq, Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
  exact him

/-- 反射稳定有限集的重心引理 (节点 20b 辅理): 有限零点集在反射下
    不变时, 其实部和的重心恰在临界线: `Σ_{ρ ∈ Z} Re ρ = |Z| / 2`.

    证明: 反射对合重排 `Σ Re ρ = Σ (1-ρ).re = Σ (1 - Re ρ) = |Z| - Σ Re ρ`,
    解出 `Σ Re ρ = |Z| / 2`. 重排用 `Finset.sum_nbij`
    (反射是 Z 上的双射), 代数用 `sum_sub_distrib`. -/
private theorem centroid_of_reflection_invariant {s : Finset ℂ}
    (hinv : ∀ ρ ∈ s, 1 - ρ ∈ s) :
    ∑ ρ ∈ s, ρ.re = (s.card : ℝ) / 2 := by
  classical
  -- 重排: Σ Re ρ = Σ (1-ρ).re (反射是 s 上的对合双射)
  have hrearr : ∑ ρ ∈ s, ρ.re = ∑ ρ ∈ s, (1 - ρ).re :=
    Finset.sum_nbij' (fun ρ : ℂ => 1 - ρ) (fun ρ : ℂ => 1 - ρ) hinv hinv
      (fun ρ _ => sub_sub_cancel 1 ρ) (fun ρ _ => sub_sub_cancel 1 ρ)
      (fun ρ _ => by simp)
  -- 逐项展开 (1-ρ).re = 1 - ρ.re
  have hone : ∀ ρ ∈ s, (1 - ρ).re = 1 - ρ.re := fun _ _ => by simp
  -- 代数: Σ Re ρ = Σ (1 - Re ρ) = |s| - Σ Re ρ
  have hsum : ∑ ρ ∈ s, ρ.re = (s.card : ℝ) - ∑ ρ ∈ s, ρ.re := by
    calc ∑ ρ ∈ s, ρ.re = ∑ ρ ∈ s, (1 - ρ).re := hrearr
      _ = ∑ ρ ∈ s, (1 - ρ.re) := Finset.sum_congr rfl hone
      _ = (∑ ρ ∈ s, 1) - ∑ ρ ∈ s, ρ.re := Finset.sum_sub_distrib _ _
      _ = (s.card : ℝ) - ∑ ρ ∈ s, ρ.re := by
          rw [Finset.sum_const, Nat.smul_one_eq_cast]
  linarith

/-- 截断零点实部重心定理 (节点 20b 核心): `Σ_{ρ ∈ Z_T} Re ρ = |Z_T| / 2`.

    无条件的一阶矩恒等式: T-横带截断零点的实部总和恒等于个数的一半.
    这是显式公式谱侧的组合骨架 —— 任何 T 截断下, 零点实部的
    "重心"无条件地落在临界线上. -/
theorem sum_re_stripZeros (T : ℝ) :
    ∑ ρ ∈ (stripZeros_finite' T).toFinset, ρ.re
      = ((stripZeros_finite' T).toFinset.card : ℝ) / 2 :=
  centroid_of_reflection_invariant fun _ρ hρ =>
    (stripZeros_finite' T).mem_toFinset.mpr
      (one_sub_mem_stripZeros ((stripZeros_finite' T).mem_toFinset.mp hρ))

/-- 截断零点实部一阶中心矩恒为零 (节点 20b, 偏差测度对偶形式):
    `Σ_{ρ ∈ Z_T} (Re ρ - 1/2) = 0`.

    与节点 12-14 偏差测度的分工: 偏差测度 `deviation R` 截取零阶信息
    (截断球内偏线零点占比), 本定理给出一阶信息 —— 无条件下截断零点
    实部均值恒为 1/2. RH 的全部内容在高阶矩:
    RH ⟺ 偏差测度恒为零 ⟺ 截断零点的全部中心矩塌缩. -/
theorem sum_sub_re_stripZeros_eq_zero (T : ℝ) :
    ∑ ρ ∈ (stripZeros_finite' T).toFinset, (ρ.re - 1 / 2) = 0 := by
  have h1 : ∑ ρ ∈ (stripZeros_finite' T).toFinset, (ρ.re - 1 / 2)
      = (∑ ρ ∈ (stripZeros_finite' T).toFinset, ρ.re)
        - ((stripZeros_finite' T).toFinset.card : ℝ) / 2 := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_const,
      Nat.smul_one_eq_cast]
  rw [h1, sum_re_stripZeros]
  ring

/-- 截断零点实部均值恒为 1/2 (节点 20b 推论): Z_T 非空时,
    `Re ρ` 在 Z_T 上的平均恒等于临界线实部 1/2.

    与 `RHSpectralMeasure.rh_iff_spectral` 的对照: 谱化 RH 要求
    全部零点落在临界线上 (高阶矩全部塌缩); 本定理说明一阶矩
    (均值) 无条件已落在临界线上 —— 均值不携带 RH 信息,
    RH 的难度全部集中在分布的离散度上. -/
theorem mean_re_stripZeros (T : ℝ)
    (hT : ((stripZeros_finite' T).toFinset.card : ℝ) ≠ 0) :
    (∑ ρ ∈ (stripZeros_finite' T).toFinset, ρ.re)
      / ((stripZeros_finite' T).toFinset.card : ℝ) = 1 / 2 := by
  rw [sum_re_stripZeros]
  field_simp

-- ============================================================
-- 4. 节点 21: 单项字典 + 组装骨架 — Mellin 逐项对偶
-- ============================================================

/-! ### 21a. 单项字典: 谱项 `(s-ρ)⁻¹` ↔ 素数项 `e^{ρu}` 的 Laplace 对偶 -/

/-- **单项字典 · 合并形式 (节点 21a 辅理)**: `Re ρ < Re s` 时

        ∫₀^∞ e^{-(s-ρ)·u} du = (s - ρ)⁻¹.

    由 `integral_exp_mul_complex_Ioi` 直接计算. -/
theorem integral_exp_sub_Ioi_zero (s ρ : ℂ) (h : ρ.re < s.re) :
    ∫ u : ℝ in Set.Ioi 0, Complex.exp (-(s - ρ) * u) = (s - ρ)⁻¹ := by
  have ha : (-(s - ρ)).re < 0 := by
    simp only [Complex.neg_re, Complex.sub_re]
    linarith
  rw [integral_exp_mul_complex_Ioi ha 0, neg_div_neg_eq, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, one_div]

/-- **单项字典 (节点 21a 核心)**: `Re ρ < Re s` 时, 核 `e^{-s·u}` 与
    素数侧单项 `e^{ρ·u}·1_{u≥0}` (u = log t, 即素数项 `t^ρ`) 在 [0,∞) 上的
    Laplace 配对恰为谱项:

        ∫₀^∞ e^{-s·u}·e^{ρ·u} du = (s - ρ)⁻¹.

    Weil 显式公式逐项对偶的原子形式: 部分分式 (节点 19 残差字典) 中
    每个谱单项 `m_ρ/(s-ρ)` 恰是素数侧单项测度 `m_ρ·e^{ρu}·1_{u≥0}du` 的
    Laplace 变换; 取 ρ = 1 得主项 `e^u` (素数侧 `t`) ↦ `(s-1)⁻¹`,
    正是节点 19a 的极点项. 证明: `exp_add` 合并被积函数后化为合并形式. -/
theorem integral_exp_mul_exp_Ioi_zero (s ρ : ℂ) (h : ρ.re < s.re) :
    ∫ u : ℝ in Set.Ioi 0, Complex.exp (-s * u) * Complex.exp (ρ * u) = (s - ρ)⁻¹ := by
  have hcomb : EqOn (fun u : ℝ => Complex.exp (-s * u) * Complex.exp (ρ * u))
      (fun u : ℝ => Complex.exp (-(s - ρ) * u)) (Set.Ioi 0) := by
    intro u _
    show Complex.exp (-s * u) * Complex.exp (ρ * u) = Complex.exp (-(s - ρ) * u)
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hcomb]
  exact integral_exp_sub_Ioi_zero s ρ h

/-! ### 21b. 组装结构: Hadamard 部分分式缺口的显式假设 (2026-09-08 K2 拆分)

    原 `WeilAssemblage` 结构把已证内容与未证缺口混在同一字段, 组装定理
    仅 `rw` 该字段, 易被误读为 Weil 显式公式已被证明. 现拆为两层:

    * **21b-a 可证层**: 典范余项 `hadamardRemainder` 的定义级分解
      `logDeriv_decomp_canonical` 与组装侧无条件形式
      `integral_exp_logPrimeMeasure_eq_assemblage_canonical` — 完全已证;
    * **21b-b 未证假设层**: `hadamard_gap_hypothesis` — Hadamard 缺口
      余项的全局部分分式分解, **axiom-风格具名显式登记, 未证**.
      21c 组装定理以「(a) 已证桥 + (b) 未证假设」两式并列,
      不再把假设字段直接 `rw` 为结论. -/

/-! #### 21b-a. 可证层: 典范余项与定义级分解 (已证) -/

/-- **Hadamard 典范余项 (节点 21b-a)**: `-ζ'/ζ` 减去全部骨架项
    (极点项 (s-1)⁻¹ + T-横带截断谱项) 的差, **按定义**承载未截断零点
    (|Im ρ| > T)、平凡零点与 Hadamard 正则化常数的全部贡献. -/
def hadamardRemainder (T : ℝ) (s : ℂ) : ℂ :=
  -deriv riemannZeta s / riemannZeta s - (s - 1)⁻¹
    + ∑ ρ ∈ (stripZeros_finite' T).toFinset,
        (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)

/-- **可证项 (a) · 定义级分解 (节点 21b-a, 已证)**: 对典范余项
    `R_T = hadamardRemainder T`, 在 `Re s > 1` 上

        -ζ'/ζ(s) = (s-1)⁻¹ - Σ_{ρ ∈ Z_T} m_ρ/(s-ρ) + R_T(s).

    ⚠️ 诚实边界: 本恒等式是 `hadamardRemainder` 定义展开后的 ring 级
    重排, **不含任何解析内容**. 骨架项的局部主部身份由节点 19a/19b
    无条件保证: 极点 s = 1 处 -ζ'/ζ 的留数为 +1
    (`exists_circleIntegral_neg_logDeriv_one`), 每个零点 ρ 的主部恰为
    -m_ρ/(s-ρ) (`exists_logDeriv_zero_order_decomposition`).
    Weil 显式公式的真正未证内容是余项的衰减/正规化控制, 见 21b-b. -/
theorem logDeriv_decomp_canonical (T : ℝ) (s : ℂ) :
    -deriv riemannZeta s / riemannZeta s
      = (s - 1)⁻¹ - ∑ ρ ∈ (stripZeros_finite' T).toFinset,
          (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ) + hadamardRemainder T s := by
  unfold hadamardRemainder
  ring

/-- **可证项 (a) · 组装侧无条件形式 (节点 21b-a, 已证)**: 以典范余项
    R_T 表述的截断显式公式骨架对素数谱测度 Laplace 变换**无条件成立**:
    证明仅用节点 18 的素数侧字典 (∫ e^{-su} ∂μ_p = -ζ'/ζ, Euler 乘积,
    已证) 与 21b-a 的定义级分解, 不引用任何未证假设. -/
theorem integral_exp_logPrimeMeasure_eq_assemblage_canonical (T : ℝ) (s : ℂ)
    (hs : 1 < s.re) :
    ∫ u : ℝ, Complex.exp (-s * u) ∂logPrimeMeasure
      = (s - 1)⁻¹ - ∑ ρ ∈ (stripZeros_finite' T).toFinset,
          (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ) + hadamardRemainder T s := by
  rw [integral_exp_logPrimeMeasure_eq_neg_logDeriv s hs]
  exact logDeriv_decomp_canonical T s

/-! #### 21b-b. 未证假设层: Hadamard 缺口假设 (axiom-风格显式登记) -/

/-- **Hadamard 缺口假设 (节点 21b-b, 未证假设)**: 给定余项代表
    `R : ℂ → ℂ`, 在 `Re s > 1` 上 `-ζ'/ζ(s)` 分解为

        (s-1)⁻¹  -  Σ_{ρ ∈ Z_T} m_ρ/(s-ρ)  +  R(s),

    其中 `Z_T` 是 T-横带截断零点集 (节点 20), `m_ρ = analyticOrderNatAt
    riemannZeta ρ` 是零点重数 (节点 19b 字典保证零点项恰有此主部).

    ⚠️ **本定义是待证假设 (axiom-风格具名登记), 不是已证定理**, 诚实
    边界分三层:
    (1) 分解式的**存在性**不是缺口: 典范余项 `hadamardRemainder T`
        按定义满足本假设 (21b-a `logDeriv_decomp_canonical`);
    (2) 真正未证的是**受控余项的存在性**: Weil 程序需要 R 承载 Hadamard
        正规化 — 未截断零点/平凡零点/常数的显式贡献, 以及 `Re s > 1`
        之外的亚纯延拓与垂直增长 (衰减) 控制. 该控制依赖 ζ 的 Hadamard
        乘积, Mathlib 尚无, 本框架内**无任何受控实例被证明**;
    (3) 因此本假设在文档中列为「未证假设」: 在 Hadamard 乘积进入
        Mathlib 前, 仅作为显式接口登记, 21c 组装定理以本假设为具名
        (可审计) 前提, **不得被解读为 Weil 显式公式已被证明**. -/
def hadamard_gap_hypothesis (T : ℝ) (R : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, 1 < s.re →
    -deriv riemannZeta s / riemannZeta s
      = (s - 1)⁻¹ - ∑ ρ ∈ (stripZeros_finite' T).toFinset,
          (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ) + R s

/-! ### 21c. 组装定理: 素数谱测度 Laplace 变换的谱分解 -/

/-- **组装定理 · 谱侧形式 (节点 21c)**: 在 Hadamard 缺口假设 (21b-b,
    **未证假设**) 下, `Re s > 1` 时素数谱测度的 Laplace 变换 (节点 18)
    取得谱分解:

        ∫ e^{-s·u} ∂μ_p = (s-1)⁻¹ - Σ_{ρ ∈ Z_T} m_ρ/(s-ρ) + R(s).

    **「(a) 已证 + (b) 待证假设」两式并列**:
    (a) 已证 (节点 18 + 21b-a, 无条件): 同一分解对典范余项
        `hadamardRemainder T` 成立
        (`integral_exp_logPrimeMeasure_eq_assemblage_canonical`);
    (b) 待证假设 (21b-b): `R` 为满足分解式的余项代表 — 以具名假设
        `hgap : hadamard_gap_hypothesis T R` 显式引用. 证明结构为
        已证桥 `integral_exp_logPrimeMeasure_eq_neg_logDeriv` 加假设
        本身, 别无其他内容 (审计见 `assemblage_iff_hadamard_gap`). -/
theorem integral_exp_logPrimeMeasure_eq_assemblage (T : ℝ) (R : ℂ → ℂ)
    (hgap : hadamard_gap_hypothesis T R)
    (s : ℂ) (hs : 1 < s.re) :
    ∫ u : ℝ, Complex.exp (-s * u) ∂logPrimeMeasure
      = (s - 1)⁻¹ - ∑ ρ ∈ (stripZeros_finite' T).toFinset,
          (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ) + R s := by
  rw [integral_exp_logPrimeMeasure_eq_neg_logDeriv s hs]
  exact hgap s hs

/-- **组装定理 · Mellin 桥形式 (节点 21c 推论)**: 在 Hadamard 缺口假设
    (21b-b, **未证假设**) 下, 节点 11 的 Mellin 桥 `-ζ'/ζ = s·𝓜[ψ](-s)`
    的右端取得谱分解:

        s · 𝓜[ψ](-s) = (s-1)⁻¹ - Σ_{ρ ∈ Z_T} m_ρ/(s-ρ) + R(s).

    这是反演骨架 (21d) 的被积函数: 沿垂直线的 Mellin 反演把
    右端送回素数侧 (ψ), 与 μ_p 形式 (谱侧形式) 构成同一组装的
    测度论 / Mellin 双语表述. 与谱侧形式相同, 证明结构为已证 Mellin 桥
    (节点 11) 加具名假设 `hgap` 本身, 别无其他内容. -/
theorem mellin_psi_eq_assemblage (T : ℝ) (R : ℂ → ℂ)
    (hgap : hadamard_gap_hypothesis T R) (s : ℂ) (hs : 1 < s.re) :
    s * mellin (fun t : ℝ ↦ ((ψ t : ℝ) : ℂ)) (-s)
      = (s - 1)⁻¹ - ∑ ρ ∈ (stripZeros_finite' T).toFinset,
          (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ) + R s := by
  rw [← neg_logDeriv_eq_mul_mellin s hs]
  exact hgap s hs

/-- **组装定理 · 测度配对形式 (节点 21c 核心)**: 在 Hadamard 缺口假设
    (21b-b, **未证假设**) 下, `Re s > 1` 时

        Laplace[μ_p](s) - Laplace[主项](s) + Σ_{ρ ∈ Z_T} m_ρ·Laplace[谱单项](s) = R(s),

    即素数谱测度与 "主项测度 - 截断谱测度" 之差的 Laplace 变换恰为余项.
    主项是 `e^u·1_{u≥0}du` (素数侧 `t`), 谱单项是 `e^{ρu}·1_{u≥0}du`
    (素数侧 `t^ρ`, u = log t), 各单项的 Laplace 变换由单项字典 (21a)
    逐项计算为 `(s-ρ)⁻¹`. Weil 显式公式的测度论本质在此完全显形:
    素数谱与零点谱经 Laplace-Mellin 对偶逐项配对, 未配对的残差即余项.
    已证/待证结构与谱侧形式一致: 配对恒等式的全部内容 = 已证单项字典
    (21a) + 已证谱侧形式 + 具名假设 `hgap` 本身. -/
theorem assemblage_pairing (T : ℝ) (R : ℂ → ℂ)
    (hgap : hadamard_gap_hypothesis T R) {s : ℂ} (hs : 1 < s.re) :
    (∫ u : ℝ, Complex.exp (-s * u) ∂logPrimeMeasure)
      - (∫ u : ℝ in Set.Ioi 0, Complex.exp (-s * u) * Complex.exp u)
      + ∑ ρ ∈ (stripZeros_finite' T).toFinset, (analyticOrderNatAt riemannZeta ρ : ℂ) *
          ∫ u : ℝ in Set.Ioi 0, Complex.exp (-s * u) * Complex.exp (ρ * u)
      = R s := by
  have h1 := integral_exp_logPrimeMeasure_eq_assemblage T R hgap s hs
  have hmain : ∫ u : ℝ in Set.Ioi 0, Complex.exp (-s * u) * Complex.exp u = (s - 1)⁻¹ := by
    have hcomb : EqOn (fun u : ℝ => Complex.exp (-s * u) * Complex.exp u)
        (fun u : ℝ => Complex.exp (-(s - 1) * u)) (Set.Ioi 0) := by
      intro u _
      show Complex.exp (-s * u) * Complex.exp u = Complex.exp (-(s - 1) * u)
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hcomb]
    exact integral_exp_sub_Ioi_zero s 1 hs
  have hspec : ∀ ρ ∈ (stripZeros_finite' T).toFinset,
      ∫ u : ℝ in Set.Ioi 0, Complex.exp (-s * u) * Complex.exp (ρ * u) = (s - ρ)⁻¹ := by
    intro ρ hρ
    obtain ⟨⟨-, -, hlt⟩, -⟩ := (stripZeros_finite' T).mem_toFinset.mp hρ
    exact integral_exp_mul_exp_Ioi_zero s ρ (lt_trans hlt hs)
  have hsum : ∑ ρ ∈ (stripZeros_finite' T).toFinset, (analyticOrderNatAt riemannZeta ρ : ℂ) *
      ∫ u : ℝ in Set.Ioi 0, Complex.exp (-s * u) * Complex.exp (ρ * u)
    = ∑ ρ ∈ (stripZeros_finite' T).toFinset,
        (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ) := by
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    rw [hspec ρ hρ, div_eq_mul_inv]
  rw [h1, hmain, hsum]
  ring

/-- **审计桥 (节点 21c, 2026-09-08 K2 验证闭环)**: 组装等式在点 `s` 处
    成立 ⟺ Hadamard 缺口分解在点 `s` 处成立 — 相对已证桥 (节点 18)
    而言.

    即: `integral_exp_logPrimeMeasure_eq_assemblage` 的全部非平凡内容
    恰为具名假设 `hadamard_gap_hypothesis` (21b-b, 未证), 其余部分
    (测度论桥 ∫ = -ζ'/ζ) 全部已证. 缺口假设以具名参数出现在组装定理
    签名中, 可直接审计; 不再隐藏于 `structure` 字段 (`#print axioms`
    因此仅显示标准三公理, 无隐藏依赖). -/
theorem assemblage_iff_hadamard_gap (T : ℝ) (R : ℂ → ℂ) (s : ℂ) (hs : 1 < s.re) :
    (∫ u : ℝ, Complex.exp (-s * u) ∂logPrimeMeasure
      = (s - 1)⁻¹ - ∑ ρ ∈ (stripZeros_finite' T).toFinset,
          (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ) + R s)
      ↔ -deriv riemannZeta s / riemannZeta s
          = (s - 1)⁻¹ - ∑ ρ ∈ (stripZeros_finite' T).toFinset,
              (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ) + R s := by
  rw [integral_exp_logPrimeMeasure_eq_neg_logDeriv s hs]

/-! ### 21d. Mellin 反演骨架: ψ 的条件反演 -/

/-- **ψ 在非整数点的连续性 (节点 21d 辅理)**: ψ 是阶梯函数, 在每个
    非整数点连续 (整数点处右连续但左跳跃 Λ(n)).

    证明: `x < 1` 时 ψ 在邻域内恒零 (`psi_eq_zero_of_le_one`);
    `x ≥ 1` 非整数时 x 落在开区间 `(N, N+1)` (N = ⌊x⌋₊) 内, 而
    ψ 在该区间上恒等于 `∑_{k ≤ N} Λ(k)` (`psi_eq_sum_Icc`), 局部常值
    故连续. -/
theorem continuousAt_cpsi_of_not_nat {x : ℝ} (hx : x ∉ Set.range Nat.cast) :
    ContinuousAt (fun t : ℝ ↦ ((ψ t : ℝ) : ℂ)) x := by
  rcases lt_or_ge x 1 with hx1 | hx1
  · have hmem : Set.Iio (1 : ℝ) ∈ 𝓝 x := Iio_mem_nhds hx1
    have hev : (fun t : ℝ ↦ ((ψ t : ℝ) : ℂ)) =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
      filter_upwards [hmem] with t ht
      rw [psi_eq_zero_of_le_one ht.le, Complex.ofReal_zero]
    exact hev.continuousAt
  · set N := ⌊x⌋₊ with hNdef
    have hNx : (N : ℝ) < x := by
      have hle : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
      rcases eq_or_ne (N : ℝ) x with h | h
      · exact absurd (show x ∈ Set.range Nat.cast from ⟨N, h⟩) hx
      · exact lt_of_le_of_ne hle h
    have hxN1 : x < (N : ℝ) + 1 := by
      have hlt := Nat.lt_floor_add_one x
      exact_mod_cast hlt
    have hconst : ∀ t ∈ Set.Ioo (N : ℝ) ((N : ℝ) + 1),
        ((ψ t : ℝ) : ℂ) = ((ψ x : ℝ) : ℂ) := by
      intro t ht
      obtain ⟨ht1, ht2⟩ := ht
      have hfl : ⌊t⌋₊ = N := by
        rw [Nat.floor_eq_iff (by
          have h0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
          linarith)]
        exact ⟨ht1.le, ht2⟩
      rw [psi_eq_sum_Icc t, psi_eq_sum_Icc x, hfl]
    have hev : (fun t : ℝ ↦ ((ψ t : ℝ) : ℂ)) =ᶠ[𝓝 x] fun _ => ((ψ x : ℝ) : ℂ) := by
      filter_upwards [(isOpen_Ioo).mem_nhds ⟨hNx, hxN1⟩] with t ht
      exact hconst t ht
    exact hev.continuousAt

/-- **Mellin 反演骨架 (节点 21d 核心)**: ψ 的 Mellin 反演除垂直可积性外
    全部条件无条件成立 —— 对任意 σ < -1 (𝓜[ψ] 收敛半平面 `Re w < -1`
    内的反演线), x > 0 非整数 (ψ 的连续点) 处

        mellinInv σ (𝓜[ψ]) x = ψ(x),

    唯一假设是垂直可积性 `VerticalIntegrable (mellin ψ) σ`. 该条件在 ψ 上
    不能无条件验证: ψ 是阶梯函数, 其 Mellin 变换沿垂直线的衰减不足
    (这正是完整 Weil 公式需要光滑紧支测试函数技术的根源, 见模块头
    诚实边界). 与组装定理 (21c) 的合并路径: Mellin 桥 (节点 11) 在
    `Re s > 1` 上给出 `-ζ'/ζ = s·𝓜[ψ](-s)`, Hadamard 假设给出右端的
    谱分解, 本骨架把二者经垂直线积分送回素数侧 —— 围道移动的解析
    代价由 `VerticalIntegrable` 与余项 R 的性状共同承担. -/
theorem mellinInv_mellin_psi_eq (σ : ℝ) (hσ : σ < -1) {x : ℝ} (hx : 0 < x)
    (hxnat : x ∉ Set.range Nat.cast)
    (hvert : VerticalIntegrable (mellin (fun t : ℝ ↦ ((ψ t : ℝ) : ℂ))) σ) :
    mellinInv σ (mellin (fun t : ℝ ↦ ((ψ t : ℝ) : ℂ))) x = ((ψ x : ℝ) : ℂ) := by
  have hconv : MellinConvergent (fun t : ℝ ↦ ((ψ t : ℝ) : ℂ)) σ := by
    have h := mellinConvergent_psi (s := (↑(-σ) : ℂ)) (by
      simp only [Complex.ofReal_re]
      linarith)
    rwa [show (-↑(-σ) : ℂ) = (↑σ : ℂ) by rw [Complex.ofReal_neg, neg_neg]] at h
  exact mellinInv_mellin_eq σ _ hx hconv hvert (continuousAt_cpsi_of_not_nat hxnat)

-- ============================================================
-- 5. 节点 22: 测试函数字典 — 光滑紧支测试函数与无条件反演
-- ============================================================

open scoped FourierTransform

/-! ### 22a. 测试函数的 Laplace 型变换 -/

/-- 测试函数的 Laplace 型变换 (节点 22a): `testLaplace φ s := ∫_ℝ φ(u)·e^{s·u} du`.

    对数坐标 u = log t 下的双侧 Laplace 变换. φ ∈ C_c^∞ (光滑紧支) 时:
    * 逐点良定义 (`integrable_testLaplace`, 紧支连续 ⟹ 可积);
    * 沿垂直线 s = σ + y·I 有 Fourier 表示 (`fourierEq_testLaplace`):
      恰为 `φ·e^{σ·}` 的 Fourier 变换在 `-y/(2π)` 处取值 — 由
      C_c^∞ ⊂ 𝓢 与 𝓕 : 𝓢 → 𝓢, 其沿垂直方向无条件超多项衰减
      (Paley-Wiener 型). 这正是 ψ (阶梯函数, 其 Mellin 变换 -ζ'/ζ
      沿垂直线仅多项衰减) 所不具备的性质, 是 `VerticalIntegrable`
      缺口在测试函数世界被消除的根源. -/
def testLaplace (φ : ℝ → ℂ) (s : ℂ) : ℂ := ∫ u : ℝ, φ u * Complex.exp (s * u)

/-- 指数因子的光滑性 (节点 22a 辅理). -/
private theorem contDiff_exp_mul_const (s : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => Complex.exp (s * u)) := by
  have hcoe : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => (u : ℂ)) := Complex.ofRealCLM.contDiff
  exact (contDiff_const.mul hcoe).cexp

/-- 光滑紧支函数乘指数保持光滑紧支 (节点 22a 辅理). -/
private theorem smooth_compact_exp_mul (φ : ℝ → ℂ) (hsm : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hcp : HasCompactSupport φ) (s : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => φ u * Complex.exp (s * u)) ∧
      HasCompactSupport (fun u : ℝ => φ u * Complex.exp (s * u)) := by
  refine ⟨hsm.mul (contDiff_exp_mul_const s), hcp.mono ?_⟩
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  exact fun h => hx (mul_eq_zero.mpr (Or.inl h))

/-- `testLaplace` 被积函数的可积性 (节点 22a): 光滑紧支 φ ⟹ 可积. -/
theorem integrable_testLaplace (φ : ℝ → ℂ) (hsm : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hcp : HasCompactSupport φ) (s : ℂ) :
    Integrable (fun u : ℝ => φ u * Complex.exp (s * u)) := by
  obtain ⟨hsm', hcp'⟩ := smooth_compact_exp_mul φ hsm hcp s
  exact hsm'.continuous.integrable_of_hasCompactSupport hcp'

/-! ### 22b. Fourier 表示与无条件垂直可积性 -/

/-- `testLaplace` 的 Fourier 表示 (节点 22b): 沿垂直线 `s = σ + y·I`，

        testLaplace φ (σ + y·I) = 𝓕[φ·e^{σ·}] (-(y/(2π))).

    证明: 两侧展开后, `exp((σ + y·I)·u) = e^{σ·u}·e^{y·I·u}`,
    而 `𝓕 g t = ∫ g·e^{-2πi·t·u}`, 代入 `t = -y/(2π)` 相消. -/
theorem fourierEq_testLaplace (φ : ℝ → ℂ) (hsm : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hcp : HasCompactSupport φ) (σ y : ℝ) :
    testLaplace φ (σ + y * I) = 𝓕 (fun u : ℝ => φ u * Complex.exp (σ * u)) (-(y / (2 * π))) := by
  have _hconv := integrable_testLaplace φ hsm hcp (σ + y * I)
  have h2π : (2 : ℝ) * π ≠ 0 := by positivity
  have hsplit : ∀ u : ℝ, ((σ + y * I) * u : ℂ) = ↑(σ * u) + ↑(y * u) * I := by
    intro u
    rw [add_mul, mul_right_comm, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  have harg : ∀ u : ℝ,
      (Complex.ofReal (-2 * π * (u * -(y / (2 * π)))) : ℂ) = Complex.ofReal (y * u) := by
    intro u
    rw [Complex.ofReal_inj]
    field_simp
  rw [testLaplace, Real.fourier_eq']
  simp only [Real.inner_apply]
  refine integral_congr_ae (by
    filter_upwards with u
    rw [hsplit u, Complex.exp_add, harg u, smul_eq_mul]
    push_cast
    ring)

/-- **测试函数的无条件垂直可积性 (节点 22c)**: 光滑紧支 φ ⟹ `testLaplace φ`
    沿任意垂直线 `s = σ + y·I` 可积.

    这是 `VerticalIntegrable` 缺口在测试函数世界被消除的定量形式:
    ψ 的 Mellin 变换 (-ζ'/ζ) 沿垂直线仅多项衰减, 垂直积分发散,
    Mellin 反演需要显式假设; 而 φ ∈ C_c^∞ 的 testLaplace 沿垂直线
    是 Schwartz 函数 `φ·e^{σ·}` 的 Fourier 变换 (`fourierEq_testLaplace`),
    Schwartz 空间在 Fourier 变换下不变 (`fourierTransformCLM : 𝓢 →L 𝓢`),
    故沿垂直方向超多项衰减, 无条件可积.

    证明: 被积函数 `y ↦ testLaplace φ (σ + y·I)` 经 Fourier 表示后
    即 `y ↦ 𝓕 g (-y/(2π))` (g = `φ·e^{σ·}` ∈ 𝓢); 变量替换
    `t = -y/(2π)` 把积分化为 `𝓕 g` 的可积性, 由 `SchwartzMap.integrable`
    (Fourier 变换保持 Schwartz 性) 无条件成立. -/
theorem verticalIntegrable_testLaplace (φ : ℝ → ℂ) (hsm : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hcp : HasCompactSupport φ) (σ : ℝ) :
    Integrable (fun y : ℝ => testLaplace φ (σ + y * I)) := by
  obtain ⟨hgsm, hgcp⟩ := smooth_compact_exp_mul φ hsm hcp (σ : ℂ)
  have key := fourierEq_testLaplace φ hsm hcp σ
  have hFint : Integrable (𝓕 (fun u : ℝ => φ u * Complex.exp (σ * u))) :=
    (𝓕 (hgcp.toSchwartzMap hgsm)).integrable
  have h1 : Integrable (fun y : ℝ =>
      (𝓕 (fun u : ℝ => φ u * Complex.exp (σ * u))) ((-1 / (2 * π)) * y)) :=
    hFint.comp_mul_left' (by positivity)
  have harg : ∀ y : ℝ, (-1 / (2 * π)) * y = -(y / (2 * π)) := by
    intro y
    field_simp
  have hpt : ∀ y : ℝ,
      (𝓕 (fun u : ℝ => φ u * Complex.exp (σ * u))) ((-1 / (2 * π)) * y)
        = (𝓕 (fun u : ℝ => φ u * Complex.exp (σ * u))) (-(y / (2 * π))) := by
    intro y
    rw [harg y]
  have h2 : Integrable (fun y : ℝ =>
      (𝓕 (fun u : ℝ => φ u * Complex.exp (σ * u))) (-(y / (2 * π)))) :=
    h1.congr (Filter.Eventually.of_forall hpt)
  exact h2.congr (Filter.Eventually.of_forall (fun y => (key y).symm))

end RHWeilFormula

end
