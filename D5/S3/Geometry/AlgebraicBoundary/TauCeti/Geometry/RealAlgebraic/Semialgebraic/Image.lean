/- GID: D5/S3/Geometry/AlgebraicBoundary/TauCeti/Geometry/RealAlgebraic/Semialgebraic/Image
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/TauCeti/Geometry/RealAlgebraic/Semialgebraic/Image
   mirror-E: none(waiver:external-source-adaptation)
   anchors: []
   utility: none
   digest: Pinned TauCeti real algebraic dependency for entire boundary recovery. -/

/- Source: TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/Geometry/RealAlgebraic/Semialgebraic/Image.lean.
Adaptation: ordinary D5 import routes; selected original declarations and their proof bodies are retained.
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

public import D5.S3.Geometry.AlgebraicBoundary.TauCeti.Geometry.RealAlgebraic.Semialgebraic.QuantifierElimination

/-!
# Projection of semialgebraic sets

Given projection closure, eliminating a finite set of coordinates from a
semialgebraic set preserves semialgebraicity. These lemmas supply the
coordinate projections used in the closure argument.
-/

public section

open MvPolynomial Set

namespace TauCeti

variable {σ τ R : Type*} [CommRing R] [LinearOrder R] [HasSemialgebraicProjections R]

/-- Given projection closure, the projection of a semialgebraic subset of `σ ⊕ τ → R` that forgets
the finitely many coordinates `σ` is semialgebraic. -/
theorem IsSemialgebraic.image_comp_inr [Finite σ] {s : Set (σ ⊕ τ → R)}
    (hs : IsSemialgebraic s) :
    IsSemialgebraic ((fun z : σ ⊕ τ → R => z ∘ Sum.inr) '' s) := by
  revert τ
  refine Finite.induction_empty_option
    (P := fun σ => ∀ {τ : Type _} {s : Set (σ ⊕ τ → R)}, IsSemialgebraic s →
      IsSemialgebraic ((fun z : σ ⊕ τ → R => z ∘ Sum.inr) '' s))
    (fun {α β} e ih {τ} {s} hs => ?_) (fun {τ} {s} hs => ?_)
    (fun {α} _ ih {τ} {s} hs => ?_) σ
  · -- Transport along `e : α ≃ β` in the coordinates to be forgotten.
    convert ih (hs.preimage_comp (Equiv.sumCongr e.symm (Equiv.refl τ))) using 1
    ext y
    simp only [mem_image, mem_preimage]
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z ∘ Equiv.sumCongr e (Equiv.refl τ), ?_, rfl⟩
      convert hz using 1
      ext (b | c) <;> simp
    · rintro ⟨z, hz, rfl⟩
      exact ⟨_, hz, rfl⟩
  · -- With no coordinates to forget, the projection is the bijection `Sum.inr`.
    convert hs.preimage_comp (Equiv.emptySum PEmpty τ) using 1
    ext y
    simp only [mem_image, mem_preimage]
    constructor
    · rintro ⟨z, hz, rfl⟩
      convert hz using 1
      ext (b | c)
      · exact b.elim
      · rfl
    · intro hy
      exact ⟨_, hy, rfl⟩
  · -- Forget the coordinate `none` with `IsSemialgebraic.image_comp_some`, then the coordinates
    -- `α` by induction.
    let k : Option α ⊕ τ → Option (α ⊕ τ) :=
      Sum.elim (Option.elim · none (some ∘ Sum.inl)) (some ∘ Sum.inr)
    convert ih (hs.preimage_comp k).image_comp_some using 1
    ext y
    simp only [mem_image, mem_preimage, exists_exists_and_eq_and]
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(Option.elim · (z (.inl none)) (z ∘ Sum.elim (Sum.inl ∘ some) Sum.inr)), ?_, rfl⟩
      convert hz using 1
      ext ((_ | a) | c) <;> rfl
    · rintro ⟨w, hw, rfl⟩
      exact ⟨_, hw, rfl⟩

/-- Given projection closure, the projection of a semialgebraic subset of `σ ⊕ τ → R` that forgets
the finitely many coordinates `τ` is semialgebraic. -/
theorem IsSemialgebraic.image_comp_inl [Finite τ] {s : Set (σ ⊕ τ → R)}
    (hs : IsSemialgebraic s) :
    IsSemialgebraic ((fun z : σ ⊕ τ → R => z ∘ Sum.inl) '' s) := by
  convert (hs.preimage_comp (Equiv.sumComm σ τ)).image_comp_inr using 1
  ext y
  simp only [mem_image, mem_preimage]
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z ∘ Equiv.sumComm τ σ, ?_, rfl⟩
    convert hz using 1
    ext (a | b) <;> rfl
  · rintro ⟨z, hz, rfl⟩
    exact ⟨_, hz, rfl⟩

end TauCeti
