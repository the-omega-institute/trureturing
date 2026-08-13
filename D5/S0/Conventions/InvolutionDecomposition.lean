/- GID: D5/S0/Conventions/InvolutionDecomposition
   generality: G
   mirror-B: D5/B/S0/Conventions/InvolutionDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every real-linear involution splits each vector into fixed and negated parts. -/

import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Module

namespace D5.S0.Conventions.InvolutionDecomposition

/-- A real-linear involution decomposes every vector into an even part and an odd part. -/
theorem involution_even_odd_decomposition
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (reverse : V →ₗ[ℝ] V) (hreverse : Function.Involutive reverse) (x : V) :
    let evenPart := (2 : ℝ)⁻¹ • (x + reverse x)
    let oddPart := (2 : ℝ)⁻¹ • (x - reverse x)
    x = evenPart + oddPart ∧
      reverse evenPart = evenPart ∧ reverse oddPart = -oddPart := by
  dsimp
  constructor
  · module
  constructor <;> simp only [map_smul, map_add, map_sub, hreverse x] <;> module

/-- The hypotheses of the decomposition theorem are jointly inhabited. -/
example : Function.Involutive (LinearMap.id (R := ℝ) (M := ℝ)) := by
  intro x
  rfl

#print axioms involution_even_odd_decomposition

end D5.S0.Conventions.InvolutionDecomposition
