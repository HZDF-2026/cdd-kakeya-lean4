import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity

/-! # W1 Wave Medium: Cayley 色散算子保酉性与能量守恒 (wave_proto 形式化)

    wave_proto 惯性减速介质 (inertial.py / adjoint.py CayleyOps) 核心数学
    性质的 Lean 4 形式化。物理设置:
      i·w_t = -½∇·(α(x)∇w) + V·w + g|w|²w - iγ·w + ξ
    离散: L = ∇·(α∇) (周期五点, 界面系数算术平均), H = -½L;
    色散步 Cayley (Crank-Nicolson) U = A⁻¹B, A = I - icL, B = I + icL,
    c = dt/4 (inertial.py CayleyOps 文档字符串的逐字对应)。

    ## 本模块证明的定理 (全部 Mathlib 支撑, 零 sorry)

    生成元与酉性:
    1. `cayleyX_conjTranspose`  : L 自伴 ⇒ X = icL 斜自伴 (Xᴴ = -X)
    2. `mul_four_cancel`        : 四因子消去 A⁻¹·B·A·B⁻¹ = 1 (AB=BA 时)
    3. `cayleyOf_unitary`       : X 斜自伴 + A = 1-X 可逆 ⇒ U 酉
                                  (U⬝Uᴴ = 1 ∧ Uᴴ⬝U = 1)
    4. `cayley_unitary`         : 上述在 X = icL 的实例化 (主定理)
    能量守恒 (E(v) = ∑ᵢ‖vᵢ‖² = 总波能量):
    5. `star_mul_self_eq_normSq`: star z * z = ↑(normSq z) (能量桥梁)
    6. `star_dotProduct_eq_sum_normSq` : star v ⬝ᵥ v = ∑ᵢ↑‖vᵢ‖²
    7. `cayleyStep_normSq_sum_preserved`: 酉性 ⇒ Cayley 步保总能量
    8. `phaseStep_normSq_preserved`     : 对角相位步逐点保范 (|e^{-iθ}|=1)
    9. `waveStep_normSq_sum_conserved`  : 整步 (相位∘Cayley∘相位) 能量
                                  守恒 = "γ=0 且无噪声时能量严格守恒"
                                  (S1 实验地基的数学内容)
    均匀 α 快速路径:
    10. `fft_multiplier_normSq_one` / `fft_multiplier_norm_one`:
                                  Fourier 乘子 (1-it)/(1+it) (t = cλ 实)
                                  normSq = 1 且范数 = 1 —— FFT 乘子路径
                                  与 LU 路径同为保酉

    ## 证明结构 (关键代数事实)

    L 实自伴 ⇒ X := icL 满足 Xᴴ = -X (斜自伴)
    ⇒ (1-X)ᴴ = 1+X, (1+X)ᴴ = 1-X
    A := 1-X 与 B := 1+X 均为 X 的多项式 ⇒ A*B = B*A (交换性)
    ⇒ Uᴴ = A*B⁻¹; U*Uᴴ = A⁻¹(BA)B⁻¹ = A⁻¹(AB)B⁻¹ = 1
       右酉由 U*Uᴴ = 1 经 det 乘法性得 IsUnit U.det, 故 U⁻¹ 双侧逆,
       Uᴴ = U⁻¹ ⇒ Uᴴ*U = 1 (无需 A⁻¹B⁻¹ = B⁻¹A⁻¹ 的独立交换性论证)。
    能量: star w ⬝ᵥ w = ∑ conj(w i) * w i = ∑↑(normSq (w i)),
    酉性把 star(U*ᵥv)⬝ᵥ(U*ᵥv) 化为 star v⬝ᵥ(UᴴU)⬝ᵥv = star v⬝ᵥv。

    ## 诚实声明 (形式化范围边界)

    - 本模块形式化的是**算法核心算子的数学性质** (保酉性/守恒性),
      非对 Python 数值代码的等价性验证;
    - L 的自伴性 (五点 stencil + 界面算术平均的对称性) 作为定理前提
      `hL : L.IsHermitian` 登记: 该前提的数值面由 wave_proto 端
      Python 断言 |L - Lᴴ|_max = 0 校准 (工程上已由 BIT 复现间接覆盖);
    - A = 1 - icL 的可逆性作为前提 `hA : IsUnit (1-X).det` 登记
      (五点 Laplacian 特征值 λ ∈ [-8α_max, 0] ⇒ det ≠ 0 数值面成立);
    - 非线性势相位 g|w|²w 以"给定相位场 θ"形式登记 (逐点 |e^{-iθ}| = 1
      对任意实 θ 成立, 与相位依赖场强的具体形式无关);
    - γ > 0 耗散与 ξ 噪声不在此模块 (它们破坏守恒, 是对照机制);
    - FFT 乘子定理对任意实 t = cλ 成立 (λ = 五点 Laplacian 符号,
      均匀 α 时实数), 逐 Fourier 模式保范 ⇒ 整体保能量。

    CDD Framework v28.4 · wave_proto S1-S13 物理内核
    Date: 2026-08-31
    Toolchain: Lean v4.32.2 + Mathlib (mathlib432 local checkout)
-/

namespace CDD.W1.WaveMedium

variable {n : Type*} [Fintype n] [DecidableEq n]

open Complex Matrix

-- ============================================================
-- §1 Cayley 色散算子定义 (inertial.py CayleyOps 逐字对应)
-- ============================================================

/-- 斜自伴生成元 X = (c·i) • L, c = dt/4 (实数)。 -/
noncomputable def cayleyX (L : Matrix n n ℂ) (c : ℝ) : Matrix n n ℂ :=
  ((c : ℂ) * Complex.I) • L

/-- Cayley 色散步 U = A⁻¹ * B, A = 1 - X, B = 1 + X。 -/
noncomputable def cayleyStep (L : Matrix n n ℂ) (c : ℝ) : Matrix n n ℂ :=
  (1 - cayleyX L c)⁻¹ * (1 + cayleyX L c)

/-- 通用 Cayley 步 (以任意斜自伴 X 为生成元): U = (1-X)⁻¹(1+X)。 -/
noncomputable def cayleyOf (X : Matrix n n ℂ) : Matrix n n ℂ :=
  (1 - X)⁻¹ * (1 + X)

/-- 势场/非线性相位步 (对角相位乘子, θ 为给定实相位场)。 -/
noncomputable def phaseStep (θ : n → ℝ) : Matrix n n ℂ :=
  Matrix.diagonal fun i => Complex.exp (-(Complex.I * (θ i : ℂ)))

/-- 完整波演化步: 相位 ∘ Cayley 色散 ∘ 相位 (split-step, 两半相位场
    可不同; inertial.py 的相位-色散-相位结构)。 -/
noncomputable def waveStep (L : Matrix n n ℂ) (c : ℝ) (θ₁ θ₂ : n → ℝ) :
    Matrix n n ℂ :=
  phaseStep θ₂ * (cayleyStep L c * phaseStep θ₁)

-- ============================================================
-- §2 生成元的斜自伴性 (L 自伴 ⇒ Xᴴ = -X)
-- ============================================================

omit [Fintype n] [DecidableEq n] in
/-- L 自伴 ⇒ X = (c·i)•L 斜自伴: Xᴴ = -X。
    c 实数保证 star(c·i) = -c·i (star 与 conj 在 ℂ 上定义相等)。 -/
theorem cayleyX_conjTranspose (L : Matrix n n ℂ) (hL : L.IsHermitian) (c : ℝ) :
    (cayleyX L c)ᴴ = -(cayleyX L c) := by
  have hc : star ((c : ℂ) * Complex.I) = -((c : ℂ) * Complex.I) := by
    simp only [star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [cayleyX, conjTranspose_smul, hL.eq, hc, neg_smul, ← cayleyX]

-- ============================================================
-- §3 A 与 B 的交换性 (均为 X 的多项式)
-- ============================================================

/-- (1 - X)(1 + X) = 1 - X²。 -/
theorem one_sub_mul_one_add (X : Matrix n n ℂ) : (1 - X) * (1 + X) = 1 - X * X := by
  noncomm_ring

/-- (1 + X)(1 - X) = 1 - X²。 -/
theorem one_add_mul_one_sub (X : Matrix n n ℂ) : (1 + X) * (1 - X) = 1 - X * X := by
  noncomm_ring

/-- A = 1-X 与 B = 1+X 交换: AB = BA。 -/
theorem cayley_AB_commute (X : Matrix n n ℂ) :
    (1 - X) * (1 + X) = (1 + X) * (1 - X) := by
  rw [one_sub_mul_one_add, one_add_mul_one_sub]

/-- 四因子消去引理 (Cayley 保酉性证明的代数核心):
    B*A = A*B, P*A = 1, B*Q = 1 ⇒ P*B*(A*Q) = 1。
    实例化 P = A⁻¹, Q = B⁻¹ 即 A⁻¹·B·A·B⁻¹ = 1。 -/
theorem mul_four_cancel (P B A Q : Matrix n n ℂ)
    (hBA : B * A = A * B) (hPA : P * A = 1) (hBQ : B * Q = 1) :
    P * B * (A * Q) = 1 := by
  rw [Matrix.mul_assoc P B (A * Q), ← Matrix.mul_assoc B A Q, hBA,
      ← Matrix.mul_assoc P (A * B) Q, ← Matrix.mul_assoc P A B,
      hPA, Matrix.one_mul, hBQ]

-- ============================================================
-- §4 主定理: Cayley 保酉性
-- ============================================================

/-- **Cayley 保酉性主定理** (wave_proto 全部实验的色散步正确性地基)。

    X 斜自伴 (Xᴴ = -X), A = 1-X 可逆 ⇒ U = A⁻¹(1+X) 酉:
    U⬝Uᴴ = 1 且 Uᴴ⬝U = 1。 -/
theorem cayleyOf_unitary (X : Matrix n n ℂ) (hX : Xᴴ = -X)
    (hA : IsUnit (1 - X).det) :
    cayleyOf X * (cayleyOf X)ᴴ = 1 ∧ (cayleyOf X)ᴴ * cayleyOf X = 1 := by
  have hA' : (1 - X)ᴴ = 1 + X := by
    rw [conjTranspose_sub, conjTranspose_one, hX, sub_neg_eq_add]
  have hB' : (1 + X)ᴴ = 1 - X := by
    rw [conjTranspose_add, conjTranspose_one, hX, sub_eq_add_neg]
  -- B = Aᴴ 可逆: det B = star (det A)
  have hB : IsUnit (1 + X).det := by
    have hAB : (1 + X) = (1 - X)ᴴ := hA'.symm
    rw [hAB, det_conjTranspose]
    exact IsUnit.star hA
  -- U 的共轭转置: Uᴴ = Bᴴ * (A⁻¹)ᴴ = A * B⁻¹
  have hUh : (cayleyOf X)ᴴ = (1 - X) * (1 + X)⁻¹ := by
    rw [cayleyOf, conjTranspose_mul, conjTranspose_nonsing_inv, hB', hA']
  -- 左酉: U*Uᴴ = A⁻¹·B·(A·B⁻¹) = A⁻¹(BA)B⁻¹ = A⁻¹(AB)B⁻¹ = 1
  have hUU : cayleyOf X * (cayleyOf X)ᴴ = 1 := by
    rw [hUh, cayleyOf]
    exact mul_four_cancel _ _ _ _ (cayley_AB_commute X).symm
      (Matrix.nonsing_inv_mul _ hA) (Matrix.mul_nonsing_inv _ hB)
  -- 右酉: U*Uᴴ = 1 ⇒ det U 可逆 (det 乘法性) ⇒ U⁻¹ 双侧逆 ⇒ Uᴴ = U⁻¹
  have hUdet : IsUnit (cayleyOf X).det := by
    have h1 : (cayleyOf X * (cayleyOf X)ᴴ).det = (1 : Matrix n n ℂ).det := by
      rw [hUU]
    rw [Matrix.det_mul, Matrix.det_one] at h1
    exact IsUnit.of_mul_eq_one _ h1
  have hUinv : (cayleyOf X)ᴴ = (cayleyOf X)⁻¹ := by
    calc (cayleyOf X)ᴴ = 1 * (cayleyOf X)ᴴ := (Matrix.one_mul _).symm
      _ = ((cayleyOf X)⁻¹ * cayleyOf X) * (cayleyOf X)ᴴ := by
          rw [Matrix.nonsing_inv_mul _ hUdet]
      _ = (cayleyOf X)⁻¹ * (cayleyOf X * (cayleyOf X)ᴴ) := Matrix.mul_assoc _ _ _
      _ = (cayleyOf X)⁻¹ * 1 := by rw [hUU]
      _ = (cayleyOf X)⁻¹ := Matrix.mul_one _
  exact ⟨hUU, by rw [hUinv, Matrix.nonsing_inv_mul _ hUdet]⟩

/-- **主定理在波介质生成元的实例化**: L 自伴 ⇒ Cayley 色散步
    U = (I - icL)⁻¹(I + icL) 酉 (c = dt/4 实数)。 -/
theorem cayley_unitary (L : Matrix n n ℂ) (hL : L.IsHermitian) (c : ℝ)
    (hA : IsUnit (1 - cayleyX L c).det) :
    cayleyStep L c * (cayleyStep L c)ᴴ = 1 ∧ (cayleyStep L c)ᴴ * cayleyStep L c = 1 :=
  cayleyOf_unitary (cayleyX L c) (cayleyX_conjTranspose L hL c) hA

-- ============================================================
-- §5 能量守恒 (总波能量 E(v) = ∑ᵢ ‖vᵢ‖², normSq 形式)
-- ============================================================

/-- 能量桥梁: star z * z = ↑(normSq z) (star 与 conj 在 ℂ 上定义相等)。 -/
theorem star_mul_self_eq_normSq (z : ℂ) :
    star z * z = ((Complex.normSq z : ℝ) : ℂ) :=
  (Complex.normSq_eq_conj_mul_self).symm

omit [DecidableEq n] in
/-- 共轭点积 = 总能量: star v ⬝ᵥ v = ∑ᵢ ↑(‖vᵢ‖²)。 -/
theorem star_dotProduct_eq_sum_normSq (v : n → ℂ) :
    star v ⬝ᵥ v = ∑ i, ((Complex.normSq (v i) : ℝ) : ℂ) := by
  show ∑ i, star (v i) * v i = ∑ i, ((Complex.normSq (v i) : ℝ) : ℂ)
  exact Finset.sum_congr rfl fun i _ => star_mul_self_eq_normSq (v i)

/-- **Cayley 步能量守恒**: 酉性 ⇒ ∑‖(U*ᵥv)ᵢ‖² = ∑‖vᵢ‖²。
    γ = 0 时色散步严格保总波能量 (S1 实验地基)。 -/
theorem cayleyStep_normSq_sum_preserved (L : Matrix n n ℂ) (hL : L.IsHermitian) (c : ℝ)
    (hA : IsUnit (1 - cayleyX L c).det) (v : n → ℂ) :
    ∑ i, Complex.normSq ((cayleyStep L c *ᵥ v) i) = ∑ i, Complex.normSq (v i) := by
  have hu := cayley_unitary L hL c hA
  have h1 : star (cayleyStep L c *ᵥ v) ⬝ᵥ (cayleyStep L c *ᵥ v) = star v ⬝ᵥ v := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hu.2,
      Matrix.one_mulVec]
  rw [star_dotProduct_eq_sum_normSq, star_dotProduct_eq_sum_normSq,
    ← Complex.ofReal_sum, ← Complex.ofReal_sum] at h1
  exact Complex.ofReal_injective h1

/-- **相位步逐点保范**: 对角相位乘子 e^{-iθ} 逐点保 normSq
    (|e^{-iθ}| = 1, θ 实), 与相位场依赖场强的具体形式无关。 -/
theorem phaseStep_normSq_preserved (θ : n → ℝ) (v : n → ℂ) (i : n) :
    Complex.normSq ((phaseStep θ *ᵥ v) i) = Complex.normSq (v i) := by
  have hre : (-(Complex.I * (θ i : ℂ))).re = 0 := by
    rw [Complex.neg_re, Complex.I_mul_re, Complex.ofReal_im]
    ring
  have hn : Complex.normSq (Complex.exp (-(Complex.I * (θ i : ℂ)))) = 1 := by
    rw [← Complex.norm_mul_self_eq_normSq, Complex.norm_exp, hre, Real.exp_zero, mul_one]
  have hd : (phaseStep θ *ᵥ v) i = Complex.exp (-(Complex.I * (θ i : ℂ))) * v i := by
    simp [phaseStep, Matrix.mulVec_diagonal]
  rw [hd, Complex.normSq_mul, hn, one_mul]

/-- **整步能量守恒** (物理主定理): γ = 0 且无噪声时, 波演化步
    (相位∘Cayley∘相位) 严格保持总波能量 ∑‖wᵢ‖²。 -/
theorem waveStep_normSq_sum_conserved (L : Matrix n n ℂ) (hL : L.IsHermitian) (c : ℝ)
    (hA : IsUnit (1 - cayleyX L c).det) (θ₁ θ₂ : n → ℝ) (v : n → ℂ) :
    ∑ i, Complex.normSq ((waveStep L c θ₁ θ₂ *ᵥ v) i) = ∑ i, Complex.normSq (v i) := by
  have e1 : ∑ i, Complex.normSq ((phaseStep θ₁ *ᵥ v) i) = ∑ i, Complex.normSq (v i) :=
    Finset.sum_congr rfl fun i _ => phaseStep_normSq_preserved θ₁ v i
  have e2 : ∑ i, Complex.normSq ((cayleyStep L c *ᵥ (phaseStep θ₁ *ᵥ v)) i)
          = ∑ i, Complex.normSq ((phaseStep θ₁ *ᵥ v) i) :=
    cayleyStep_normSq_sum_preserved L hL c hA _
  have e3 : ∑ i, Complex.normSq ((phaseStep θ₂ *ᵥ (cayleyStep L c *ᵥ (phaseStep θ₁ *ᵥ v))) i)
          = ∑ i, Complex.normSq ((cayleyStep L c *ᵥ (phaseStep θ₁ *ᵥ v)) i) :=
    Finset.sum_congr rfl fun i _ => phaseStep_normSq_preserved θ₂ _ i
  rw [waveStep, ← Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    e3, e2, e1]

-- ============================================================
-- §6 均匀 α 快速路径: Fourier 乘子保范
-- ============================================================

/-- **FFT 乘子保范 (normSq 形式)**: 均匀 α 快速路径的 Fourier 乘子
    m(λ) = (1 - i·t)/(1 + i·t) (t = c·λ 实数, λ = 五点 Laplacian 符号)
    满足 normSq = 1 —— 乘子逐 Fourier 模式保范 ⇒ FFT 路径与 LU 路径
    同为保酉。 -/
theorem fft_multiplier_normSq_one (t : ℝ) :
    Complex.normSq ((1 - (t : ℂ) * Complex.I) / (1 + (t : ℂ) * Complex.I)) = 1 := by
  have hre_add : (1 + (t : ℂ) * Complex.I).re = 1 := by
    rw [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have him_add : (1 + (t : ℂ) * Complex.I).im = t := by
    rw [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have hre_sub : (1 - (t : ℂ) * Complex.I).re = 1 := by
    rw [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have him_sub : (1 - (t : ℂ) * Complex.I).im = -t := by
    rw [Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have hden : Complex.normSq (1 + (t : ℂ) * Complex.I) = 1 + t * t := by
    rw [Complex.normSq_apply, hre_add, him_add]
    ring
  have hnum : Complex.normSq (1 - (t : ℂ) * Complex.I) = 1 + t * t := by
    rw [Complex.normSq_apply, hre_sub, him_sub]
    ring
  have hne : (1 + t * t : ℝ) ≠ 0 := by
    intro h
    have h2 : t * t = t ^ 2 := by ring
    rw [h2] at h
    have h3 : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
    linarith
  rw [Complex.normSq_div, hnum, hden, div_self hne]

/-- **FFT 乘子保范 (范数形式)**: ‖(1 - it)/(1 + it)‖ = 1 (t 实)。 -/
theorem fft_multiplier_norm_one (t : ℝ) :
    ‖(1 - (t : ℂ) * Complex.I) / (1 + (t : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_def, fft_multiplier_normSq_one, Real.sqrt_one]

end CDD.W1.WaveMedium
