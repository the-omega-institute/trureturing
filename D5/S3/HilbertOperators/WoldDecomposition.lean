/- GID: D5/S3/HilbertOperators/WoldDecomposition
   generality: G
   mirror-B: D5/B/S3/HilbertOperators/WoldDecomposition
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.Projection.Basic, mathlib/module/Mathlib.Analysis.InnerProductSpace.LinearMap, mathlib/module/Mathlib.Analysis.Normed.Operator.LinearIsometry]
   utility: none
   digest: Every finite wandering decomposition has an exact norm identity; an isometry restricts to a linear isometric equivalence on the intersection of its power ranges. -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of the upstream source tree.
The full license, including the intended-use preface, is retained at
`docs/reports/lovasz-suppliers/atlas-LICENSE.txt`.
Source: facebookresearch/atlas-lean at immutable revision
`a60759060b5616df0d5775b42da4d337719feb32`,
`MathlibExt/Analysis/InnerProductSpace/WoldDecomposition.lean`.
Original source SHA-256:
8a6fa41461cae3f678ece91c2374ed6ef1d398ca2555b0f32e833a30c4eb3192.
Modifications: native header and namespace; remove module/public wrappers,
unused imports, unused power-orthogonality, uniqueness and residual-orthogonality
branches, and the unconsumed coercion companion. Consumed support is private
and range instances are local. Retained mathematical statements and proof
bodies follow the source. This reuses known mathematics and its formal proof;
no original mathematical or proof credit is claimed.
Retire the transplant and directly reuse equivalent Mathlib declarations when
this repository actually adopts a pinned Mathlib revision supplying the same
arbitrary-level finite support, norm identity and residual equivalence scopes.
-/

import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Tactic.Ring

/-!
# Finite wandering decomposition and residual isometry

For an arbitrary real or complex inner product space, the wandering subspace
is the orthogonal complement of the range of an isometry. Completeness gives
a finite decomposition at every natural level, including zero, with wandering
coefficients supported strictly below that level. Its squared norm identity
holds even without completeness for every supplied decomposition. The
intersection of all power ranges carries the actual restricted isometry as a
linear isometric equivalence, also without completeness. No separability,
finite dimension or surjectivity on the ambient space is assumed.

These statements assert neither an infinite direct-sum decomposition nor
coefficientwise uniqueness. See the sourced Library note for correspondence.
-/

namespace D5.S3.HilbertOperators.WoldDecomposition

open scoped _root_.InnerProductSpace
open Submodule Finset

section Basic

variable {𝕜 : Type*} [RCLike 𝕜] {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H]

/-- The **wandering subspace** of an isometry `V`: the orthogonal complement of
its range. Vectors here are orthogonal to every vector in the range of `V`. -/
noncomputable def wanderingSub (V : H →ₗᵢ[𝕜] H) : Submodule 𝕜 H :=
  (LinearMap.range (V : H →ₗ[𝕜] H))ᗮ

end Basic

section Complete

variable {𝕜 : Type*} [RCLike 𝕜] {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The range of an isometry is complete. -/
local instance (V : H →ₗᵢ[𝕜] H) : CompleteSpace (LinearMap.range (V : H →ₗ[𝕜] H)) := by
  have h : IsComplete ((LinearMap.range (V : H →ₗ[𝕜] H)) : Set H) := by
    rw [LinearMap.coe_range]
    exact V.isometry.isUniformInducing.isComplete_range
  exact h.completeSpace_coe

/-- The range of an isometry admits an orthogonal projection. -/
local instance (V : H →ₗᵢ[𝕜] H) :
    (LinearMap.range (V : H →ₗ[𝕜] H)).HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace _

/- proof_shape: bind-only; admission_basis: consumed-helper; escape-witness: none.
Consumers: exists_wandering_add_range. -/
/-- The ambient space splits as the wandering subspace plus the range. -/
private theorem isCompl_wandering (V : H →ₗᵢ[𝕜] H) :
    IsCompl (wanderingSub V) (LinearMap.range (V : H →ₗ[𝕜] H)) :=
  (LinearMap.range (V : H →ₗ[𝕜] H)).isCompl_orthogonal.symm

/- proof_shape: bind-only; admission_basis: consumed-helper; escape-witness: none.
Consumers: exists_wold_decomposition. -/
/-- One step of the Wold decomposition: every vector splits as a wandering
vector plus a vector in the range. -/
private theorem exists_wandering_add_range (V : H →ₗᵢ[𝕜] H) (x : H) :
    ∃ w ∈ wanderingSub V, ∃ y : H, x = w + V y := by
  obtain ⟨⟨w, hw⟩, ⟨y, hy⟩, hxy, -⟩ :=
    existsUnique_add_of_isCompl (isCompl_wandering V) x
  obtain ⟨y', hy'⟩ := LinearMap.mem_range.mp hy
  have hy'' : V y' = y := hy'
  exact ⟨w, hw, y', by calc x = w + y := hxy.symm
                            _ = w + V y' := by rw [hy'']⟩

/- proof_shape: content; admission_basis: escape-witness (source transplant).
Escape-witness: the induction extends a single common coefficient family at
level n while proving its support and reconstruction at level n+1.
Consumers: public finite decomposition endpoint. -/
/-- Finite Wold decomposition: every vector is a finite sum of pushed-forward
wandering vectors plus a remainder in the range of `V ^ n`. The wandering
coefficients vanish at and beyond `n`. -/
theorem exists_wold_decomposition (V : H →ₗᵢ[𝕜] H) (x : H) (n : ℕ) :
    ∃ w : ℕ → H, ∃ y : H, (∀ k, w k ∈ wanderingSub V) ∧ (∀ k ≥ n, w k = 0) ∧
      x = (∑ k ∈ Finset.range n, (V ^ k) (w k)) + (V ^ n) y := by
  induction n generalizing x with
  | zero =>
    refine ⟨fun _ => 0, x, fun _ => by simp [wanderingSub], fun k _ => rfl, by simp⟩
  | succ n ih =>
    obtain ⟨w, y, hwW, hwsupp, hy⟩ := ih x
    obtain ⟨wn, hwn, y', hy'⟩ := exists_wandering_add_range V y
    have hsum : (∑ k ∈ Finset.range n,
        (V ^ k) (Function.update w n wn k)) =
        ∑ k ∈ Finset.range n, (V ^ k) (w k) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k ≠ n := by
        have : k < n := Finset.mem_range.mp hk
        omega
      rw [Function.update_of_ne hkn wn w]
    refine ⟨Function.update w n wn, y', ?_, ?_, ?_⟩
    · intro k
      by_cases hk : k = n
      · subst hk
        rw [Function.update_self]
        exact hwn
      · rw [Function.update_of_ne hk wn w]
        exact hwW k
    · intro k hk
      rw [Function.update_of_ne (by omega : k ≠ n) wn w]
      exact hwsupp k (by omega)
    · calc x = (∑ k ∈ Finset.range n, (V ^ k) (w k)) + (V ^ n) y := hy
        _ = (∑ k ∈ Finset.range n, (V ^ k) (w k)) +
              ((V ^ n) wn + (V ^ (n + 1)) y') := by
            rw [hy', map_add, pow_succ, LinearIsometry.coe_mul,
              Function.comp_apply]
        _ = ((∑ k ∈ Finset.range n, (V ^ k) (w k)) + (V ^ n) wn) +
              (V ^ (n + 1)) y' := by rw [add_assoc]
        _ = (∑ k ∈ Finset.range (n + 1), (V ^ k) (Function.update w n wn k)) +
              (V ^ (n + 1)) y' := by
            rw [Finset.sum_range_succ, Function.update_self, hsum]

/- proof_shape: content; admission_basis: escape-witness (source transplant).
Escape-witness: the finite induction groups the terminal wandering vector
with the actual isometric remainder and proves the resulting squared norm.
Consumers: public norm identity endpoint. -/
omit [CompleteSpace H] in
/-- Pythagoras for a Wold decomposition: the squared norm of a vector is the sum
of the squared norms of its wandering coefficients plus the squared norm of
the remainder. -/
theorem wold_norm_sq (V : H →ₗᵢ[𝕜] H) (n : ℕ) (w : ℕ → H)
    (hw : ∀ k, w k ∈ wanderingSub V) (y : H) (x : H)
    (hx : x = (∑ k ∈ Finset.range n, (V ^ k) (w k)) + (V ^ n) y) :
    ‖x‖ ^ 2 = (∑ k ∈ Finset.range n, ‖w k‖ ^ 2) + ‖y‖ ^ 2 := by
  induction n generalizing w y x with
  | zero =>
    rw [hx]
    simp
  | succ n ih =>
    have hgroup : x = (∑ k ∈ Finset.range n, (V ^ k) (w k)) +
        (V ^ n) (w n + V y) := by
      rw [hx, Finset.sum_range_succ, map_add, pow_succ, LinearIsometry.coe_mul,
        Function.comp_apply, add_assoc]
    have hstep := ih w hw (w n + V y) x hgroup
    have hpyth : ‖w n + V y‖ ^ 2 = ‖w n‖ ^ 2 + ‖y‖ ^ 2 := by
      have hmem : V y ∈ LinearMap.range (V : H →ₗ[𝕜] H) := ⟨y, rfl⟩
      have h0 := (Submodule.mem_orthogonal _ _).mp (hw n) _ hmem
      have hs : ⟪w n, V y⟫_𝕜 = (starRingEnd 𝕜) ⟪V y, w n⟫_𝕜 :=
        (inner_conj_symm _ _).symm
      have hinner : ⟪w n, V y⟫_𝕜 = 0 := by
        rw [hs, h0]
        exact map_zero _
      calc ‖w n + V y‖ ^ 2 = ‖w n‖ ^ 2 + ‖V y‖ ^ 2 := by
            simpa only [pow_two] using
              norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hinner
        _ = ‖w n‖ ^ 2 + ‖y‖ ^ 2 := by rw [LinearIsometry.norm_map]
    rw [hstep, hpyth, Finset.sum_range_succ]
    ring

omit [CompleteSpace H] in
/-- The **residual subspace** of an isometry: vectors in the range of every
power of `V`. -/
noncomputable def residualSub (V : H →ₗᵢ[𝕜] H) : Submodule 𝕜 H :=
  ⨅ n, LinearMap.range ((V ^ n : H →ₗᵢ[𝕜] H) : H →ₗ[𝕜] H)

/- proof_shape: bind-only; admission_basis: consumed-helper; escape-witness: none.
Consumers: restrict_residual_bijective, inner_restrict_residual, woldResidualEquiv. -/
omit [CompleteSpace H] in
/-- The isometry maps its residual subspace into itself. -/
private theorem mapsTo_residual (V : H →ₗᵢ[𝕜] H) :
    ∀ x ∈ residualSub V, V x ∈ residualSub V := by
  intro x hx
  show V x ∈ ⨅ n, LinearMap.range ((V ^ n : H →ₗᵢ[𝕜] H) : H →ₗ[𝕜] H)
  rw [Submodule.mem_iInf]
  intro n
  cases n with
  | zero =>
    exact ⟨V x, by simp⟩
  | succ n =>
    have hxn : x ∈ LinearMap.range ((V ^ n : H →ₗᵢ[𝕜] H) : H →ₗ[𝕜] H) :=
      (Submodule.mem_iInf _).mp hx n
    obtain ⟨z, hz⟩ := hxn
    have hz' : (V ^ n : H →ₗᵢ[𝕜] H) z = x := hz
    refine ⟨z, ?_⟩
    show (V ^ (n + 1) : H →ₗᵢ[𝕜] H) z = V x
    rw [pow_succ', LinearIsometry.coe_mul, Function.comp_apply, hz']

/- proof_shape: content; admission_basis: escape-witness (source transplant).
Escape-witness: cancellation by V places a preimage in every power range
simultaneously, establishing surjectivity of the actual restriction.
Consumers: woldResidualEquiv. -/
omit [CompleteSpace H] in
/-- The restriction of an isometry to its residual subspace is bijective. -/
private theorem restrict_residual_bijective (V : H →ₗᵢ[𝕜] H) :
    Function.Bijective (((V : H →ₗ[𝕜] H).restrict (mapsTo_residual V) :
      residualSub V →ₗ[𝕜] residualSub V)) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    have h := congrArg (fun z : residualSub V => (z : H)) hxy
    have h' : V (x : H) = V (y : H) := h
    exact V.injective h'
  · intro y
    have hy1 : (y : H) ∈
        LinearMap.range ((V ^ 1 : H →ₗᵢ[𝕜] H) : H →ₗ[𝕜] H) :=
      (Submodule.mem_iInf _).mp y.property 1
    rw [pow_one] at hy1
    obtain ⟨x₀, hx₀⟩ := hy1
    have hx₀' : V x₀ = (y : H) := hx₀
    have hx₀res : x₀ ∈ residualSub V := by
      show x₀ ∈ ⨅ n, LinearMap.range ((V ^ n : H →ₗᵢ[𝕜] H) : H →ₗ[𝕜] H)
      rw [Submodule.mem_iInf]
      intro n
      have hyn : (y : H) ∈
          LinearMap.range ((V ^ (n + 1) : H →ₗᵢ[𝕜] H) : H →ₗ[𝕜] H) :=
        (Submodule.mem_iInf _).mp y.property (n + 1)
      obtain ⟨z, hz⟩ := hyn
      have hz' : (V ^ (n + 1) : H →ₗᵢ[𝕜] H) z = (y : H) := hz
      rw [pow_succ', LinearIsometry.coe_mul, Function.comp_apply] at hz'
      rw [← hx₀'] at hz'
      have hzx : (V ^ n) z = x₀ := V.injective hz'
      exact ⟨z, hzx⟩
    refine ⟨⟨x₀, hx₀res⟩, ?_⟩
    apply Subtype.ext
    show V x₀ = (y : H)
    exact hx₀'

/- proof_shape: bind-only; admission_basis: consumed-helper; escape-witness: none.
Consumers: woldResidualEquiv. -/
omit [CompleteSpace H] in
/-- The restriction of an isometry to its residual subspace preserves inner
products. -/
private theorem inner_restrict_residual (V : H →ₗᵢ[𝕜] H) (x y : residualSub V) :
    ⟪((V : H →ₗ[𝕜] H).restrict (mapsTo_residual V) x : H),
        ((V : H →ₗ[𝕜] H).restrict (mapsTo_residual V) y : H)⟫_𝕜 =
      ⟪(x : H), (y : H)⟫_𝕜 := by
  show ⟪V (x : H), V (y : H)⟫_𝕜 = ⟪(x : H), (y : H)⟫_𝕜
  exact LinearIsometry.inner_map_map V _ _

/- Definition packaging of the consumed residual bijection and inner-product
preservation; the forward map is literally V restricted to residualSub V. -/
omit [CompleteSpace H] in
/-- The isometry restricts to a unitary operator (a linear isometric
equivalence) on its residual subspace. -/
noncomputable def woldResidualEquiv (V : H →ₗᵢ[𝕜] H) :
    residualSub V ≃ₗᵢ[𝕜] residualSub V :=
  LinearEquiv.isometryOfInner
    (LinearEquiv.ofBijective ((V : H →ₗ[𝕜] H).restrict (mapsTo_residual V))
      (restrict_residual_bijective V))
    (inner_restrict_residual V)

end Complete

end D5.S3.HilbertOperators.WoldDecomposition
