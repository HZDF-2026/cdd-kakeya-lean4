import CddFormalization.RH_ExplicitFormula
import CddFormalization.RH_SpectralMeasure
import Mathlib.Analysis.MellinInversion
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

-- ============ 命名空间与签名 ============
#check @mellinInv_mellin_eq
#check @VerticalIntegrable
#check @mellinInv
#check @Filter.Tendsto.congr'
#check @riemannZeta_ne_zero_of_one_le_re
#check @exists_eventuallyEq_pow_smul_nonzero_iff
#check @analyticOn_riemannZeta
#check @isLittleO_one_iff
#check @Complex.ofReal_neg

-- ============ P1: 穿孔邻域负映射 ============
private theorem tendsto_neg_nhdsWithin (a : ℂ) :
    Filter.Tendsto (fun w : ℂ ↦ -w) (𝓝[≠] (-a)) (𝓝[≠] a) := by
  intro s hs
  rcases Filter.mem_nhdsWithin.1 hs with ⟨t, ht, hsub⟩
  refine Filter.mem_nhdsWithin.2 ⟨(fun w : ℂ ↦ -w) ⁻¹' t, ?_, ?_⟩
  · exact (continuous_neg.continuousAt).preimage_mem_nhds ht
  · rintro w ⟨hw, -⟩
    exact hsub ⟨hw, by simpa using w ≠ -a⟩

-- ============ P2: 节点 18 核心恒等式 ============
open Chebyshev ArithmeticFunction

theorem probe_mellin_psi_eq_logDeriv {w : ℂ} (hw : w.re < -1) :
    mellin (fun t : ℝ ↦ ((ψ t : ℝ) : ℂ)) w
      = deriv riemannZeta (-w) / (w * riemannZeta (-w)) := by
  have hs : 1 < (-w).re := by rw [Complex.neg_re]; linarith
  have h := RHExplicitFormula.neg_logDeriv_eq_mul_mellin (-w) hs
  rw [neg_neg] at h
  have hz : riemannZeta (-w) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by rw [Complex.neg_re]; linarith)
  have hwne : w ≠ 0 := by
    intro hc; rw [hc] at hw; simp at hw
  field_simp
  ring

-- ============ P3: isLittleO → 残差 (s-1)(-ζ'/ζ) → 1 ============
theorem probe_residue_one :
    Filter.Tendsto (fun s : ℂ ↦ (s - 1) * (-deriv riemannZeta s / riemannZeta s))
      (𝓝[≠] 1) (𝓝 1) := by
  have h0 : (fun s : ℂ ↦ deriv riemannZeta s / riemannZeta s + (s - 1)⁻¹ - γ)
      =o[𝓝[≠] 1] (fun _ ↦ (1 : ℂ)) :=
    log_deriv_riemannZeta_add_inv_sub_sub_isLittleO
  have h1 : Filter.Tendsto
      (fun s : ℂ ↦ deriv riemannZeta s / riemannZeta s + (s - 1)⁻¹ - γ)
      (𝓝[≠] 1) (𝓝 0) := (isLittleO_one_iff _).1 h0
  have h2 : Filter.Tendsto (fun s : ℂ ↦ s - 1) (𝓝[≠] 1) (𝓝 0) :=
    (continuous_id.continuousAt).tendsto.mono_left (nhdsWithin_le_nhds)
  have h3 : Filter.Tendsto (fun s : ℂ ↦ (s - 1) *
      (deriv riemannZeta s / riemannZeta s + (s - 1)⁻¹ - γ)) (𝓝[≠] 1) (𝓝 0) :=
    h2.mul h1
  have h4 : (fun s : ℂ ↦ (s - 1) * (deriv riemannZeta s / riemannZeta s + (s - 1)⁻¹ - γ))
      = fun s : ℂ ↦ (s - 1) * (deriv riemannZeta s / riemannZeta s) + 1
        - γ * (s - 1) := by
    funext s
    rw [mul_add, mul_sub, mul_one, mul_inv_cancel_left₀ (sub_ne_zero.2 (by norm_num))]
    ring
  rw [h4] at h3
  have h5 : Filter.Tendsto (fun s : ℂ ↦ γ * (s - 1)) (𝓝[≠] 1) (𝓝 0) :=
    (tendsto_const_nhds.congr' (funext fun s ↦ by ring).symm ▸ tendsto_const_nhds)
  exact (h3.add (tendsto_const_nhds.congr funext fun s ↦ by ring)).congr funext fun s ↦ by ring

-- ============ P4: 零点阶数分解 → 残差 (s-ρ)·ζ'/ζ → m ============
theorem probe_residue_at_zero (ρ : ℂ) (hρ : ρ ≠ 1)
    (hnot : ¬∀ᶠ s in 𝓝 ρ, riemannZeta s = 0) :
    ∃ m : ℕ, Filter.Tendsto (fun s : ℂ ↦ (s - ρ) * (deriv riemannZeta s / riemannZeta s))
      (𝓝[≠] ρ) (𝓝 m) := by
  have han : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ hρ
  obtain ⟨m, g, hg_an, hg_ne, hg_eq⟩ :=
    (exists_eventuallyEq_pow_smul_nonzero_iff han).2 hnot
  refine ⟨m, ?_⟩
  -- ζ = (s-ρ)^m • g ⟹ ζ' = m(s-ρ)^{m-1}g + (s-ρ)^m g' (on nhds)
  have hgd : ∀ᶠ s in 𝓝 ρ, HasDerivAt g (deriv g s) s :=
    (hg_an.differentiableAt).hasDerivAt.eventually... -- 不确定 API
  sorry
