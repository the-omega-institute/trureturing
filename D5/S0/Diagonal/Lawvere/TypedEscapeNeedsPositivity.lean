/- GID: D5/S0/Diagonal/Lawvere/TypedEscapeNeedsPositivity
   generality: G
   mirror-B: D5/B/S0/Diagonal/Lawvere/TypedEscapeNeedsPositivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Typed Lawvere escape can fail the order-interval audit required of an effect. -/

import D5.S0.Diagonal.Lawvere.QualitativeEscape
import Mathlib.Tactic

/- Library-search audit trail (2026-08-24):
   * `rg -n -F 'TypedEscapeNeedsPositivity' D5 Golden/Frozen/accepted` returned no matches.
   * `rg -n 'effect|Lawvere|escape|orderInterval' D5/` found the public theorem
     `QualitativeEscape.escaped_of_fixedPointFree` and the distinct effect-boundary theorem
     `SharpEffectComplementBoundary.sharp_effect_complement_boundary`; neither supplies an
     escaped diagonal that fails its effect audit. No relevant private theorem was found.
   * `rg -n 'IsEffect|effect.*Set.Icc|Set.Icc.*effect' D5 .lake/packages/mathlib/Mathlib`
     found no reusable effect-interval predicate. The proof therefore uses the public Lawvere
     theorem, elementary ordered-additive-group arithmetic, and an integer witness. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Diagonal.Lawvere.TypedEscapeNeedsPositivity

open D5.S0.Diagonal.EscapeCount
open D5.S0.Diagonal.Lawvere.QualitativeEscape

/-- Membership in the order interval from zero to the distinguished order unit. -/
def IsEffect {R : Type*} [Zero R] [One R] [LE R] (E : R) : Prop :=
  0 ≤ E ∧ E ≤ 1

/-- An abstract diagonal passes the effect audit when every value it constructs lies in the
order interval from zero to one. -/
def PassesEffectAudit {A R : Type*} [Zero R] [One R] [LE R]
    (twist : R → R) (listing : A → A → R) : Prop :=
  ∀ a, IsEffect (diagonal twist listing a)

/-- In an ordered additive group, ordinary complement preserves the effect interval. -/
theorem complement_isEffect {R : Type*} [AddCommGroup R] [PartialOrder R]
    [IsOrderedAddMonoid R] [One R] {E : R}
    (hE : IsEffect E) : IsEffect (1 - E) := by
  exact ⟨sub_nonneg.mpr hE.2, sub_le_self 1 hE.1⟩

/-- Lawvere escape alone does not imply effect escape: integer complement is fixed-point-free,
and its diagonal escapes the displayed one-address listing, but the escaped value is negative
and therefore fails the effect order-interval audit. -/
theorem typed_escape_does_not_imply_effect_audit :
    ∃ listing : Unit → Unit → ℤ,
      (∀ E : ℤ, 1 - E ≠ E) ∧
        IsEscaped (fun E : ℤ ↦ 1 - E) listing ∧
          ¬ PassesEffectAudit (fun E : ℤ ↦ 1 - E) listing := by
  let listing : Unit → Unit → ℤ := fun _ _ ↦ 2
  have hfree : ∀ E : ℤ, 1 - E ≠ E := by
    intro E hfixed
    omega
  refine ⟨listing, hfree, escaped_of_fixedPointFree _ hfree listing, ?_⟩
  intro hAudit
  have hEffect := hAudit ()
  norm_num [PassesEffectAudit, IsEffect, diagonal, listing] at hEffect

example : IsEffect (0 : ℤ) := by
  norm_num [IsEffect]

#print axioms typed_escape_does_not_imply_effect_audit

end D5.S0.Diagonal.Lawvere.TypedEscapeNeedsPositivity
