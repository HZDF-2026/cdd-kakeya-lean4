import CddFormalization.RH_WeilFormula

open RHWeilFormula RHExplicitFormula MeasureTheory
open scoped FourierTransform

-- 试验: 𝓕 在 ℝ → ℂ 上的逐点展开
example (g : ℝ → ℂ) (t : ℝ) :
    𝓕 g t = ∫ v : ℝ, Complex.exp (-(2 * π * (v * t) * I)) * g v := by
  rw [Real.fourier_eq']

-- 新增验证: 节点 22-23 所需 API
#check @HasCompactSupport.toSchwartzMap
#check @Integrable.comp_div
#check @Integrable.comp_mul_left'
#check @Integrable.comp_mul_right'
#check @SchwartzMap.integrable
#check @SchwartzMap.fourier_coe
#check @mellinInv_mellin_eq
#check @MellinConvergent
#check @ContDiff.cexp
#check @HasCompactSupport.mono
#check @Real.fourier_eq'
#check @integral_exp_mul_complex_Ioi
#check @integral_prod_symm
#check @integrable_prod_iff
#check @Complex.VerticalIntegrable

-- 紧支函数支撑的乘积包含
example (φ : ℝ → ℂ) (g : ℝ → ℂ) :
    Function.support (fun u => φ u * g u) ⊆ Function.support φ := by
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  exact fun h => hx (mul_eq_zero.mpr (Or.inl h))
example (φ : ℝ → ℂ) (hcp : HasCompactSupport φ) (σ : ℝ) :
    HasCompactSupport (fun u => φ u * Complex.exp (σ * u)) := by
  refine hcp.mono ?_
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  exact fun h => hx (mul_eq_zero.mpr (Or.inl h))
