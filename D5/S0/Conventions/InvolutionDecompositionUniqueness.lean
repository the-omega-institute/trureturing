/- GID: D5/S0/Conventions/InvolutionDecompositionUniqueness
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fixed and negated summands uniquely equal the canonical half-sum and half-difference. -/

import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import D5.S0.Conventions.InvolutionDecomposition

/- Provenance: Native proof over pinned mathlib. -/

/-
SEARCH RECEIPT:
* The existence theorem is `D5/S0/Conventions/InvolutionDecomposition.lean:15`.
* Pinned mathlib defines `LinearMap.fixedSubmodule` at
  `.lake/packages/mathlib/Mathlib/LinearAlgebra/FixedSubmodule.lean:32` and identifies it with a
  kernel at the same file's line 43, but gives no involution-specific complement there.
* Pinned mathlib proves general eigenspace independence at
  `.lake/packages/mathlib/Mathlib/LinearAlgebra/Eigenspace/Basic.lean:715` and the generic
  projection-to-complement bridge `LinearMap.IsProj.isCompl` at
  `.lake/packages/mathlib/Mathlib/LinearAlgebra/Projection.lean:594`.
* Bare-source searches over pinned `Mathlib` and all of `D5` combined `involution`/`involutive`
  with `fixedSubmodule`, `eigenspace`, `IsCompl`, and `IsProj`, and also searched `even` with
  `odd`; no named fixed/negated eigenspace decomposition or even/odd projection was found.
* The proof below reuses linear-map additivity from
  `.lake/packages/mathlib/Mathlib/Algebra/Module/LinearMap/Defs.lean:322` and pinned mathlib's
  `module` tactic.
-/

namespace D5.S0.Conventions.InvolutionDecompositionUniqueness

/-- Any fixed-plus-negated decomposition has the canonical half-sum and half-difference parts;
no involutivity assumption is needed. -/
theorem involution_decomposition_unique
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (reverse : V →ₗ[ℝ] V)
    (x e o : V) (hsum : x = e + o) (heven : reverse e = e) (hodd : reverse o = -o) :
    e = (2 : ℝ)⁻¹ • (x + reverse x) ∧ o = (2 : ℝ)⁻¹ • (x - reverse x) := by
  have hreverse_sum : reverse x = e - o := by
    rw [hsum, map_add, heven, hodd]
    module
  have heven_formula : x + reverse x = (2 : ℝ) • e := by
    rw [hreverse_sum, hsum]
    module
  have hodd_formula : x - reverse x = (2 : ℝ) • o := by
    rw [hreverse_sum, hsum]
    module
  constructor
  · rw [heven_formula, smul_smul]
    norm_num
  · rw [hodd_formula, smul_smul]
    norm_num

#print axioms involution_decomposition_unique

end D5.S0.Conventions.InvolutionDecompositionUniqueness
