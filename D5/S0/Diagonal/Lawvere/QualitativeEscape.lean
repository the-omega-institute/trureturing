/- GID: D5/S0/Diagonal/Lawvere/QualitativeEscape
   generality: G
   mirror-B: D5/B/S0/Diagonal/Lawvere/QualitativeEscape
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A fixed-point-free twist escapes every listing, needing no finiteness. -/

import D5.S0.Diagonal.EscapeCount

universe u v

namespace D5.S0.Diagonal.Lawvere.QualitativeEscape

open EscapeCount

variable {A : Type u} {Y : Type v}

/-- Lawvere's qualitative form on the self-application fragment: if the twist `f` has no
fixed point then the twisted diagonal of every listing lies outside that listing's range.

This carries no finiteness hypothesis on either `A` or `Y`, so it strictly extends the
counting route of `CaptureCount.escape_all_of_fixfree`, which needs `Fintype A` and
`Fintype Y` in order to compare cardinalities. -/
theorem escaped_of_fixedPointFree (f : Y → Y) (hf : ∀ y, f y ≠ y) (g : A → A → Y) :
    IsEscaped f g := by
  rintro ⟨a, ha⟩
  exact hf (g a a) (diagonal_landing_fixed ha)

/-- The fixed-point-free hypothesis is load bearing: a twist that fixes a point captures
a listing, so the implication above is not an instance of a hypothesis-free statement. -/
theorem exists_captured_listing_of_fixedPoint :
    ∃ (f : Bool → Bool) (g : Unit → Unit → Bool), ¬ IsEscaped f g := by
  refine ⟨id, fun _ _ => true, ?_⟩
  intro hEscaped
  exact hEscaped ⟨(), rfl⟩

/-- Escape is not vacuous for want of listings: on a two-symbol alphabet the negation
twist is fixed-point free, and it escapes the constant listing. -/
theorem not_escaped_isEscaped_witness :
    IsEscaped (A := Unit) (Y := Bool) (fun b => !b) (fun _ _ => true) := by
  refine escaped_of_fixedPointFree _ ?_ _
  decide

/-- Definition 2.4 packaged: the diagonal construction of a listing is pointwise the
twist applied to the listing's diagonal entries, escape is exactly absence of that
diagonal from the listing's range, a fixed-point-free twist escapes every listing, and
the hypothesis cannot be dropped. -/
theorem self_application_fragment_package (f : Y → Y) (g : A → A → Y) :
    (∀ a : A, diagonal f g a = f (g a a)) ∧
      (IsEscaped f g ↔ diagonal f g ∉ Set.range g) ∧
      ((∀ y, f y ≠ y) → ∀ h : A → A → Y, IsEscaped f h) ∧
      (∃ (f₀ : Bool → Bool) (g₀ : Unit → Unit → Bool), ¬ IsEscaped f₀ g₀) := by
  refine ⟨fun _ => rfl, Iff.rfl, ?_, exists_captured_listing_of_fixedPoint⟩
  intro hf h
  exact escaped_of_fixedPointFree f hf h

end D5.S0.Diagonal.Lawvere.QualitativeEscape
