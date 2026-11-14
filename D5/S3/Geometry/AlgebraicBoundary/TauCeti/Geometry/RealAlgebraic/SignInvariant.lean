/- GID: D5/S3/Geometry/AlgebraicBoundary/TauCeti/Geometry/RealAlgebraic/SignInvariant
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/TauCeti/Geometry/RealAlgebraic/SignInvariant
   mirror-E: none(waiver:external-source-adaptation)
   anchors: []
   utility: none
   digest: Pinned TauCeti real algebraic dependency for entire boundary recovery. -/

/- Source: TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/Geometry/RealAlgebraic/SignInvariant.lean.
Adaptation: ordinary D5 import routes; selected declarations retain their original proofs.
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

public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Instances.Sign
import D5.S3.Geometry.AlgebraicBoundary.TauCeti.Topology.LocallyConstant.Preconnected

/-!
# Sign-invariant functions

A function `f` is *sign-invariant* on a set `s` when it has the same sign at any two points of
`s`, where the sign `SignType.sign` takes the values `-1`, `0` and `1`. In particular a function
that vanishes somewhere on `s` is sign-invariant on `s` only if it vanishes on all of `s`. This is
the invariance asked of the cells of a cylindrical algebraic decomposition adapted to a family of
polynomials: each polynomial of the family is sign-invariant on each cell.

The basic source of sign-invariance is connectedness: a function that is continuous and nowhere
zero on a preconnected set is sign-invariant there, since its sign is a continuous map to the
discrete space `SignType`.

A set on which each function of a family is sign-invariant lies inside or outside each set
described by a condition on their signs. If the sets of a cover each have this property, one sample
point from each of them realizes every sign vector that the functions take.

The retained source supplies the useful proof dependencies. Further exact applications,
including their assumptions and boundary cases, are developed in the owning Blueprint.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Section 5.1.
-/

public section

open Set

namespace TauCeti

variable {α β R : Type*}

section Preorder

variable [Zero R] [Preorder R] [DecidableLT R]

/-- A function `f` is sign-invariant on `s` if it has the same sign, possibly zero, at any two
points of `s`. -/
def SignInvariant (f : α → R) (s : Set α) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, SignType.sign (f x) = SignType.sign (f y)

variable {f g : α → R} {s t : Set α}

theorem signInvariant_def :
    SignInvariant f s ↔ ∀ x ∈ s, ∀ y ∈ s, SignType.sign (f x) = SignType.sign (f y) :=
  Iff.rfl

theorem SignInvariant.congr (h : SignInvariant f s) (hfg : EqOn f g s) : SignInvariant g s :=
  fun x hx y hy ↦ by rw [← hfg hx, ← hfg hy]; exact h x hx y hy

/-- Sign-invariance on an image is sign-invariance of the composite on the source set. -/
theorem signInvariant_image {u : β → α} {s : Set β} :
    SignInvariant f (u '' s) ↔ SignInvariant (f ∘ u) s := by
  simp [SignInvariant]

/-- A function is sign-invariant on a set containing at most one point. -/
theorem _root_.Set.Subsingleton.signInvariant (hs : s.Subsingleton) : SignInvariant f s :=
  fun x hx y hy ↦ by rw [hs hx hy]

/-- A constant function is sign-invariant on every set. -/
@[simp]
theorem signInvariant_const (c : R) : SignInvariant (fun _ : α ↦ c) s :=
  fun _ _ _ _ ↦ rfl

/-! ### Sign conditions -/

section SignCondition

variable {ι : Type*} {f : ι → α → R}

/-- If each function `f i` is sign-invariant on `t`, then `t` lies inside or outside every set
described by a condition on the signs of the `f i`. -/
theorem subset_or_disjoint_setOf_sign (hf : ∀ i, SignInvariant (f i) t)
    (Φ : (ι → SignType) → Prop) :
    t ⊆ {x | Φ fun i ↦ SignType.sign (f i x)} ∨
      Disjoint t {x | Φ fun i ↦ SignType.sign (f i x)} := by
  by_cases h : ∃ x ∈ t, Φ fun i ↦ SignType.sign (f i x)
  · obtain ⟨x, hx, hΦ⟩ := h
    refine .inl fun y hy ↦ ?_
    rwa [mem_ofPred_eq, funext fun i ↦ hf i y hy x hx]
  · exact .inr <| disjoint_left.2 fun x hx hΦ ↦ h ⟨x, hx, hΦ⟩

/-- **Sample points realize all sign conditions.** Let the functions `f i` be sign-invariant on
each set of a family `𝒞` covering `α`, and pick a sample point `x E` in each `E ∈ 𝒞`. Then the
sign vectors of the `f i` at the sample points are exactly the sign vectors they take on `α`. -/
theorem range_sign_sample_eq {𝒞 : Set (Set α)} (h𝒞 : ⋃₀ 𝒞 = univ)
    (hf : ∀ i, ∀ E ∈ 𝒞, SignInvariant (f i) E) (x : 𝒞 → α) (hx : ∀ E : 𝒞, x E ∈ (E : Set α)) :
    (range fun E i ↦ SignType.sign (f i (x E))) = range fun y i ↦ SignType.sign (f i y) := by
  refine (range_comp_subset_range x fun y i ↦ SignType.sign (f i y)).antisymm ?_
  rintro _ ⟨y, rfl⟩
  obtain ⟨E, hE, hy⟩ := mem_sUnion.1 (h𝒞 ▸ mem_univ y)
  exact ⟨⟨E, hE⟩, funext fun i ↦ hf i E hE _ (hx ⟨E, hE⟩) y hy⟩

end SignCondition

end Preorder

/-- A function that is continuous and nowhere zero on a preconnected set is sign-invariant
there. -/
theorem _root_.IsPreconnected.signInvariant [Zero R] [LinearOrder R] [TopologicalSpace R]
    [OrderTopology R] [TopologicalSpace α] {f : α → R} {s : Set α} (hs : IsPreconnected s)
    (hf : ContinuousOn f s) (h0 : ∀ x ∈ s, f x ≠ 0) : SignInvariant f s :=
  fun _ hx _ hy ↦ hs.constant (f := fun x ↦ SignType.sign (f x))
    (fun z hz ↦ (continuousAt_sign_of_ne_zero (h0 z hz)).comp_continuousWithinAt (hf z hz)) hx hy

end TauCeti
