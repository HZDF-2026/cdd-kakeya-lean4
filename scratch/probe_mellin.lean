import CddFormalization.RH_ExplicitFormula
import Mathlib.Analysis.MellinTransform

/-! # probe_mellin: RH_ExplicitFormula Mellin 桥接定理冒烟测试

    桥接定理已集成至主模块 (§6, 节点 11 完成):
    - `RHExplicitFormula.mellinConvergent_psi`
    - `RHExplicitFormula.mellin_psi_eq`
    - `RHExplicitFormula.neg_logDeriv_eq_mul_mellin`

    本文件仅作独立回归验证, 不含重复声明. -/

open RHExplicitFormula RHMeasureTheory RHLiCriterion ArithmeticFunction Chebyshev MeasureTheory
open Filter Asymptotics Finset Complex Real Set
open scoped Chebyshev Topology

noncomputable section

section SmokeTest

-- 定理可用性: Mellin 收敛性
example {s : ℂ} (hs : 1 < s.re) :
    MellinConvergent (fun t : ℝ ↦ ((ψ t : ℝ) : ℂ)) (-s) :=
  mellinConvergent_psi hs

-- 定理可用性: Mellin 支集收缩
example {s : ℂ} (hs : 1 < s.re) :
    mellin (fun t : ℝ ↦ ((ψ t : ℝ) : ℂ)) (-s) =
      ∫ t in Set.Ioi (1 : ℝ), ((ψ t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) :=
  mellin_psi_eq hs

-- 定理可用性: 显式公式的 Mellin 变换形式
example (s : ℂ) (hs : 1 < s.re) :
    -deriv riemannZeta s / riemannZeta s = s * mellin (fun t : ℝ ↦ ((ψ t : ℝ) : ℂ)) (-s) :=
  neg_logDeriv_eq_mul_mellin s hs

end SmokeTest

end
