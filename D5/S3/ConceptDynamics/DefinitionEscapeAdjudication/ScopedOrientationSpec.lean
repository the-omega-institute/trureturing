/- GID: D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/ScopedOrientationSpec
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscapeAdjudication/ScopedOrientationSpec
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An exogenous orientation specification induces a preorder on its admissible scope. -/

import Mathlib.Order.Defs.PartialOrder

/-!
An orientation relation is supplied together with provenance, version, scope,
and proofs valid on the eligible part of that scope. The projected operator is
typed only on that admissible domain.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.Adjudication.ScopedOrientationSpec

universe u

/-- Exogenous, read-only data for orienting targets eligible for a fixed goal. -/
structure OrientationSpec
    (Goal Target Source Version : Type u)
    (G : Goal) (Eligible : Target → Goal → Prop) where
  relation : Target → Target → Prop
  source : Source
  version : Version
  scope : Target → Prop
  refl_on_admissible :
    ∀ target, Eligible target G → scope target → relation target target
  trans_on_admissible :
    ∀ a b c,
      Eligible a G → scope a →
      Eligible b G → scope b →
      Eligible c G → scope c →
      relation a b → relation b c → relation a c

/-- The intersection of goal eligibility and the declared specification scope. -/
def AdmissibleTarget
    {Goal Target Source Version : Type u}
    {G : Goal} {Eligible : Target → Goal → Prop}
    (spec : OrientationSpec Goal Target Source Version G Eligible) :=
  {target : Target // Eligible target G ∧ spec.scope target}

/-- Projection of the external relation to the admissible scoped domain. -/
def orient
    {Goal Target Source Version : Type u}
    {G : Goal} {Eligible : Target → Goal → Prop}
    (spec : OrientationSpec Goal Target Source Version G Eligible)
    (a b : AdmissibleTarget spec) : Prop :=
  spec.relation a.1 b.1

/-- The projected orientation relation is reflexive and transitive on exactly
the targets carrying both eligibility and scope witnesses. -/
theorem scoped_orientation_is_preorder
    {Goal Target Source Version : Type u}
    {G : Goal} {Eligible : Target → Goal → Prop}
    (spec : OrientationSpec Goal Target Source Version G Eligible) :
    (∀ a, orient spec a a) ∧
      (∀ ⦃a b c⦄, orient spec a b → orient spec b c → orient spec a c) := by
  constructor
  · rintro ⟨target, hEligible, hScope⟩
    exact spec.refl_on_admissible target hEligible hScope
  · rintro ⟨a, haEligible, haScope⟩ ⟨b, hbEligible, hbScope⟩
      ⟨c, hcEligible, hcScope⟩ hab hbc
    exact spec.trans_on_admissible a b c
      haEligible haScope hbEligible hbScope hcEligible hcScope hab hbc

/-- The relation laws package the scoped orientation as an actual preorder. -/
@[instance_reducible] def scopedPreorder
    {Goal Target Source Version : Type u}
    {G : Goal} {Eligible : Target → Goal → Prop}
    (spec : OrientationSpec Goal Target Source Version G Eligible) :
    Preorder (AdmissibleTarget spec) where
  le := orient spec
  le_refl := (scoped_orientation_is_preorder spec).1
  le_trans := (scoped_orientation_is_preorder spec).2
  lt := fun a b => orient spec a b ∧ ¬ orient spec b a
  lt_iff_le_not_ge := by intros; rfl

#print axioms scoped_orientation_is_preorder

end D5.S3.ConceptDynamics.DefinitionEscape.Adjudication.ScopedOrientationSpec
