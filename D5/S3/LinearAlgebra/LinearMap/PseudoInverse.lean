/- GID: D5/S3/LinearAlgebra/LinearMap/PseudoInverse
   generality: G
   mirror-B: none(waiver:covered-by-monotone-interval-stability-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pseudo-inverses of linear maps of semisimple modules -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-
Source: https://github.com/TauCetiProject/TauCeti/blob/557dcf0fc5cc930bb3dd80a7f1aff6d8f2288647/TauCeti/LinearAlgebra/LinearMap/PseudoInverse.lean
Modifications: local module imports and Lean 4.35 compatibility; only live field-level prerequisites retained.
License and applicable notices: docs/reports/licenses/TauCeti-LICENSE.txt and docs/reports/licenses/TauCeti-interval-stability.md.
-/
module

public import OmegaBuild.Commands

public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Pseudo-inverses of linear maps of semisimple modules

A **pseudo-inverse** of a linear map `f` is a linear map `g` in the opposite direction with
`f ∘ g ∘ f = f`. Every linear map between semisimple modules has one, in particular every linear
map of vector spaces over a division ring: the corestriction of `f` to its range splits because
`ker f` has a complement, and a section of it extends to the whole target because the range of
`f` has a complement.

A pseudo-inverse concretely splits the exact sequence from `ker f` through the range of `f`:
`1 - g ∘ f` takes values in `ker f` and fixes it. Additive functors preserve split exact
sequences; in particular, extension of scalars carries this splitting along.
-/

compile_only_with_mathlib

@[expose] public section

/-- **Every linear map of semisimple modules has a pseudo-inverse**: a linear map `g` in the
opposite direction with `f ∘ g ∘ f = f`. This applies in particular to linear maps of vector
spaces over a division ring. -/
theorem LinearMap.exists_comp_comp_eq_self {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [IsSemisimpleModule R M] [IsSemisimpleModule R N]
    (f : M →ₗ[R] N) : ∃ g : N →ₗ[R] M, f ∘ₗ g ∘ₗ f = f := by
  obtain ⟨s, hs⟩ :=
    IsSemisimpleModule.lifting_property f.rangeRestrict f.surjective_rangeRestrict .id
  obtain ⟨g, hg⟩ :=
    IsSemisimpleModule.extension_property f.range.subtype f.range.injective_subtype s
  refine ⟨g, LinearMap.ext fun x ↦ ?_⟩
  have hgx : g (f x) = s (f.rangeRestrict x) := by
    simpa using LinearMap.congr_fun hg (f.rangeRestrict x)
  simpa [hgx] using congrArg Subtype.val (LinearMap.congr_fun hs (f.rangeRestrict x))
