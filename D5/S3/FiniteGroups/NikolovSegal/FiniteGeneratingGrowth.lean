/- GID: D5/S3/FiniteGroups/NikolovSegal/FiniteGeneratingGrowth
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/FiniteGeneratingGrowth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite-group coordinate, extraction or product mathematics. -/

import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Data.Fintype.Card

set_option autoImplicit false
open scoped Pointwise

namespace NikolovSegal.SmallTwistedProduct
universe u
variable {G : Type u} [Group G] [DecidableEq G]

/-- A finite set stable under right multiplication by g is stable under g⁻¹.
The inverse follows from actual finite injectivity/surjectivity on the set. -/
theorem finite_right_stable_inv (A : Finset G) (g : G)
    (h : ∀ x ∈ A, x*g ∈ A) : ∀ x ∈ A, x*g⁻¹ ∈ A := by
  let f : A → A := fun x => ⟨x.1*g,h x.1 x.2⟩
  have hi : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    exact mul_right_cancel (congrArg Subtype.val he)
  have hs := Finite.surjective_of_injective hi
  intro x hx
  obtain ⟨y,hy⟩ := hs ⟨x,hx⟩
  have he : y.1*g = x := congrArg Subtype.val hy
  have hi : x*g⁻¹ = y.1 := by rw [← he]; simp
  rw [hi]
  exact y.2

/-- Right stability propagates through the real subgroup closure. -/
theorem right_stable_closure (A : Finset G) (T : Set G)
    (h : ∀ t ∈ T, ∀ x ∈ A, x*t ∈ A) {g : G} (hg : g ∈ Subgroup.closure T) :
    ∀ x ∈ A, x*g ∈ A := by
  induction hg using Subgroup.closure_induction with
  | mem g hg => exact h g hg
  | one => intro x hx; simpa using hx
  | mul g k hg hk ihg ihk =>
    intro x hx
    simpa only [mul_assoc] using ihk (x*g) (ihg x hx)
  | inv g hg ih => exact finite_right_stable_inv A g ih

/-- Genuine strict growth for every nonempty proper finite subset and every
identity-containing whole-group generating subset. No coverage premise. -/
theorem card_mul_strict_of_generating [Fintype G] (A T : Finset G)
    (hA : A.Nonempty) (hproper : A ≠ Finset.univ) (hone : 1 ∈ T)
    (hgen : Subgroup.closure (T : Set G) = ⊤) : A.card < (A*T).card := by
  by_contra hlt
  have hle : (A*T).card ≤ A.card := by omega
  have hsub : A ⊆ A*T := by
    intro x hx
    exact Finset.mem_mul.mpr ⟨x,hx,1,hone,by simp⟩
  have he : A*T = A := (Finset.eq_of_subset_of_card_le hsub hle).symm
  have hs : ∀ t ∈ (T : Set G), ∀ x ∈ A, x*t ∈ A := by
    intro t ht x hx
    rw [← he]
    exact Finset.mem_mul.mpr ⟨x,hx,t,ht,rfl⟩
  obtain ⟨x,hx⟩ := hA
  apply hproper
  apply Finset.eq_univ_iff_forall.mpr
  intro y
  have hg : x⁻¹*y ∈ Subgroup.closure (T : Set G) := by rw [hgen]; trivial
  simpa only [mul_inv_cancel_left] using right_stable_closure A (T : Set G) hs hg x hx

end NikolovSegal.SmallTwistedProduct
