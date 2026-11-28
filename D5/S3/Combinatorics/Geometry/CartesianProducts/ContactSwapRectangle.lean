/- GID: D5/S3/Combinatorics/Geometry/CartesianProducts/ContactSwapRectangle
   generality: G
   mirror-B: none(waiver:covered-by-q9-k33-aligned-layer-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two coordinate swaps and one contact force a common Cartesian product. -/

module

public import OmegaBuild.Commands
public import Mathlib.Data.Set.Prod

/-!
Omega original.

Two coordinate swaps and one contact force a common Cartesian product.
-/

compile_only_with_mathlib

@[expose] public section

set_option autoImplicit false

namespace Omega.ContactSwapRectangle

variable {α β : Type*}

/-- A contact differs in both coordinates. Both endpoints can simultaneously
swap their first coordinates, and both can simultaneously swap their second. -/
def ClosedUnderContactSwaps (A D : Set (α × β)) : Prop :=
  ∀ ⦃a a' : α⦄ ⦃b b' : β⦄, (a, b) ∈ A → (a', b') ∈ D → a ≠ a' → b ≠ b' →
    ((a', b) ∈ A ∧ (a, b') ∈ D) ∧ ((a, b') ∈ A ∧ (a', b) ∈ D)

/-- Every contact fills the four corners in both aligned sets. -/
theorem contact_rectangle {A D : Set (α × β)} (h : ClosedUnderContactSwaps A D)
    {a a' : α} {b b' : β} (ha : (a, b) ∈ A) (hd : (a', b') ∈ D)
    (hr : a ≠ a') (hc : b ≠ b') :
    (a, b) ∈ A ∩ D ∧ (a', b) ∈ A ∩ D ∧ (a, b') ∈ A ∩ D ∧ (a', b') ∈ A ∩ D := by
  obtain ⟨⟨h10A, h01D⟩, ⟨h01A, h10D⟩⟩ := h ha hd hr hc
  obtain ⟨_, ⟨h11A, h00D⟩⟩ := h h10A h01D hr.symm hc
  exact ⟨⟨ha, h00D⟩, ⟨h10A, h10D⟩, ⟨h01A, h01D⟩, ⟨h11A, hd⟩⟩

/-- One contact forces the aligned sets to coincide with the product of their
coordinate projections. The factors can have arbitrary cardinality. -/
theorem eq_prod_of_contact {A D : Set (α × β)} (h : ClosedUnderContactSwaps A D)
    {a a' : α} {b b' : β} (ha : (a, b) ∈ A) (hd : (a', b') ∈ D)
    (hr : a ≠ a') (hc : b ≠ b') :
    A = D ∧ A = (Prod.fst '' A) ×ˢ (Prod.snd '' A) := by
  classical
  obtain ⟨h00, h10, h01, h11⟩ := contact_rectangle h ha hd hr hc
  -- For any point, some corner of this shared rectangle differs in both coordinates.
  have opposite (x : α) (y : β) : ∃ u v, (u, v) ∈ A ∩ D ∧ x ≠ u ∧ y ≠ v := by
    by_cases hx : x = a
    · have hxa : x ≠ a' := fun he => hr (hx.symm.trans he)
      by_cases hy : y = b
      · exact ⟨a', b', h11, hxa, fun he => hc (hy.symm.trans he)⟩
      · exact ⟨a', b, h10, hxa, hy⟩
    · by_cases hy : y = b
      · exact ⟨a, b', h01, hx, fun he => hc (hy.symm.trans he)⟩
      · exact ⟨a, b, h00, hx, hy⟩
  have heq : A = D := by
    apply Set.ext
    rintro ⟨x, y⟩
    obtain ⟨u, v, huv, hxu, hyv⟩ := opposite x y
    constructor
    · intro hxy
      exact (contact_rectangle h hxy huv.2 hxu hyv).1.2
    · intro hxy
      obtain ⟨_, _, _, hcorner⟩ := contact_rectangle h huv.1 hxy hxu.symm hyv.symm
      exact hcorner.1
  refine ⟨heq, Set.Subset.antisymm ?_ ?_⟩
  · intro z hz
    exact ⟨⟨z, hz, rfl⟩, ⟨z, hz, rfl⟩⟩
  · rintro ⟨x, y⟩ hxy
    obtain ⟨hx, hy⟩ := Set.mem_prod.mp hxy
    obtain ⟨⟨x', v⟩, hxmin, hx'⟩ := (Set.mem_image Prod.fst A x).mp hx
    obtain ⟨⟨u, y'⟩, hymin, hy'⟩ := (Set.mem_image Prod.snd A y).mp hy
    change x' = x at hx'
    change y' = y at hy'
    subst x'
    subst y'
    by_cases hxu : x = u
    · simpa only [hxu] using hymin
    by_cases hvy : v = y
    · simpa only [hvy] using hxmin
    have hyD : (u, y) ∈ D := heq ▸ hymin
    exact (h hxmin hyD hxu hvy).2.1

end Omega.ContactSwapRectangle
