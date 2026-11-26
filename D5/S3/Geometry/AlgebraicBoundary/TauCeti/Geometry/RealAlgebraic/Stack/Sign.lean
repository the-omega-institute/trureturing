/- GID: D5/S3/Geometry/AlgebraicBoundary/TauCeti/Geometry/RealAlgebraic/Stack/Sign
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/TauCeti/Geometry/RealAlgebraic/Stack/Sign
   mirror-E: none(waiver:external-source-adaptation)
   anchors: []
   utility: none
   digest: Pinned TauCeti real algebraic dependency for entire boundary recovery. -/

/- Source: TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/Geometry/RealAlgebraic/Stack/Sign.lean.
Adaptation: ordinary D5 import routes; the original declarations and proofs are retained.
License: docs/reports/licenses/TauCeti-LICENSE.txt. Original copyright notices follow.
Retire each transplanted declaration when the actual pinned mathlib supplies an equivalent
statement, and replace its consumers by direct imports and applications of that pinned owner.
This adaptation contributes no independent mathematical novelty or escape credit. -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import D5.S3.Geometry.AlgebraicBoundary.TauCeti.Geometry.RealAlgebraic.SignInvariant
public import D5.S3.Geometry.AlgebraicBoundary.TauCeti.Geometry.RealAlgebraic.Stack.Basic

/-!
# Sign-invariance on the cells of a stack

Let `θ₀ < θ₁ < … < θₖ₋₁` be continuous functions on a preconnected base `X`, and let `f` be a
continuous function on the cylinder `X × ℝ`. If every zero of `f` lies on one of the sections,
then `f` has no zero on any sector, so it is sign-invariant on each sector, because the sectors
are preconnected. If moreover the zeros of `f` are exactly the points of the sections indexed by
some `I`, then `f` vanishes on the sections indexed by `I` and has no zero on the others, so it is
sign-invariant on each section as well.

For a family `P : X → ℝ[X]` of polynomials whose evaluation is jointly continuous, this is the
step of delineability that turns root data into sign data. Suppose either every `P x` is zero, or
none is and the roots of each `P x` are exactly the values `θ i x` for `i ∈ I`. Then
`(x, t) ↦ (P x).eval t` is sign-invariant on every section and every sector of the stack. Only
the location of the roots matters here; their multiplicities do not.

## Main declarations

* `TauCeti.signInvariant_sectionSet`, `TauCeti.signInvariant_sectorSet`: sign-invariance on the
  sections and sectors of a continuous function whose zeros lie on sections.
* `TauCeti.signInvariant_eval_sectionSet`, `TauCeti.signInvariant_eval_sectorSet`: the same for
  the evaluation of a polynomial family whose roots are given by the stack.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Section 5.1.
-/

public section

open Function Polynomial Set

namespace TauCeti

variable {X α R : Type*} {k : ℕ} [TopologicalSpace X] [PreconnectedSpace X]
  [Zero R] [LinearOrder R] [TopologicalSpace R] [OrderTopology R]

/-- Over a preconnected base, a function on the cylinder is sign-invariant on the section of a
continuous function `θ i` of a stack whose sections are disjoint, provided its zeros are exactly
the points of the sections indexed by some set `I`. It vanishes on the section if `i ∈ I`, and is
nowhere zero on it otherwise. -/
theorem signInvariant_sectionSet [TopologicalSpace α] {θ : Fin k → X → α} {f : X × α → R}
    {I : Set (Fin k)} {i : Fin k} (hf : ContinuousOn f (sectionSet θ i))
    (hc : Continuous (θ i)) (hθ : ∀ x, Injective fun i ↦ θ i x)
    (hzero : ∀ z, f z = 0 ↔ ∃ i ∈ I, z ∈ sectionSet θ i) :
    SignInvariant f (sectionSet θ i) := by
  by_cases hi : i ∈ I
  · exact (signInvariant_const 0).congr fun z hz ↦ ((hzero z).2 ⟨i, hi, hz⟩).symm
  · refine (isPreconnected_sectionSet hc).signInvariant hf fun z hz h ↦ hi ?_
    -- A zero on section `i` lies on a section indexed by `I`, which must be section `i` itself.
    obtain ⟨i', hi', hz'⟩ := (hzero z).1 h
    change θ i z.1 = z.2 at hz
    change θ i' z.1 = z.2 at hz'
    rwa [← hθ z.1 (hz'.trans hz.symm)]

/-- Over a preconnected base, a function on the cylinder whose zeros all lie on sections is
sign-invariant on each sector of a stack of continuous, pointwise strictly ordered real
functions. -/
theorem signInvariant_sectorSet {θ : Fin k → X → ℝ} {f : X × ℝ → R} {j : Fin (k + 1)}
    (hf : ContinuousOn f (sectorSet θ j)) (hc : ∀ i, Continuous (θ i))
    (hθ : ∀ x, StrictMono fun i ↦ θ i x) (hzero : ∀ z, f z = 0 → ∃ i, z ∈ sectionSet θ i) :
    SignInvariant f (sectorSet θ j) :=
  (isPreconnected_sectorSet hc hθ j).signInvariant hf fun z hz h ↦
    let ⟨i, hi⟩ := hzero z h
    disjoint_left.1 (disjoint_sectionSet_sectorSet θ i j) hi hz

/-- Let `P` be a family of polynomials over a preconnected base, with jointly continuous
evaluation, which is either zero everywhere or nowhere zero. If the roots of each nonzero `P x`
are exactly the values `θ i x` for `i ∈ I`, where the `θ i x` are pointwise distinct, then the
evaluation of `P` is sign-invariant on the section of each continuous `θ i`. -/
theorem signInvariant_eval_sectionSet {K : Type*} [Semiring K] [LinearOrder K]
    [TopologicalSpace K] [OrderTopology K] {θ : Fin k → X → K} {P : X → K[X]}
    {I : Set (Fin k)} {i : Fin k} (hP : Continuous fun z : X × K ↦ (P z.1).eval z.2)
    (hc : Continuous (θ i)) (hθ : ∀ x, Injective fun i ↦ θ i x)
    (hnull : (∀ x, P x = 0) ∨ ∀ x, P x ≠ 0)
    (hroots : ∀ x, P x ≠ 0 → ∀ t, (P x).eval t = 0 ↔ ∃ i ∈ I, θ i x = t) :
    SignInvariant (fun z : X × K ↦ (P z.1).eval z.2) (sectionSet θ i) := by
  rcases hnull with h | h
  · exact (signInvariant_const 0).congr fun z _ ↦ by simp [h]
  · exact signInvariant_sectionSet hP.continuousOn hc hθ fun z ↦ by
      simpa only [sectionSet, Function.graph, Set.mem_setOf_eq] using hroots z.1 (h z.1) z.2

/-- Let `P` be a family of real polynomials over a preconnected base, with jointly continuous
evaluation, which is either zero everywhere or nowhere zero. If every root of each nonzero `P x`
is one of the values `θ i x` of a stack of continuous, pointwise strictly ordered functions, then
the evaluation of `P` is sign-invariant on each sector of the stack. -/
theorem signInvariant_eval_sectorSet {θ : Fin k → X → ℝ} {P : X → ℝ[X]} {j : Fin (k + 1)}
    (hP : Continuous fun z : X × ℝ ↦ (P z.1).eval z.2) (hc : ∀ i, Continuous (θ i))
    (hθ : ∀ x, StrictMono fun i ↦ θ i x) (hnull : (∀ x, P x = 0) ∨ ∀ x, P x ≠ 0)
    (hroots : ∀ x, P x ≠ 0 → ∀ t, (P x).eval t = 0 → ∃ i, θ i x = t) :
    SignInvariant (fun z : X × ℝ ↦ (P z.1).eval z.2) (sectorSet θ j) := by
  rcases hnull with h | h
  · exact (signInvariant_const 0).congr fun z _ ↦ by simp [h]
  · exact signInvariant_sectorSet hP.continuousOn hc hθ fun z hz ↦ by
      simpa only [sectionSet, Function.graph, Set.mem_setOf_eq] using hroots z.1 (h z.1) z.2 hz

end TauCeti
