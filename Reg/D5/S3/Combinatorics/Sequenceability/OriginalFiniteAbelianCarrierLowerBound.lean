import Reg.D5.S3.Combinatorics.Sequenceability.OriginalSharpnessCarrierLowerBound
import D5.S3.Combinatorics.Sequenceability.OriginalFiniteAbelianCarrierLowerBound
import Mathlib.Algebra.Group.ULift

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

namespace Reg.D5.S3.Combinatorics.Sequenceability.OriginalFiniteAbelianCarrierLowerBound

open _root_.Reg.D5.S3.Combinatorics.Sequenceability.OriginalSharpnessCarrierLowerBound
  (signature actual rejected dependence)
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.Combinatorics.Sequenceability.OriginalFiniteOrderSharpness
  (Index Coordinate q triple WitnessGroup label sharpness)
open _root_.D5.S3.Combinatorics.Sequenceability.OriginalFiniteAbelianCarrierLowerBound
  (finite_abelian_carrier_card_lower_bound)
open scoped Classical BigOperators

/-- The whole source telescope, varying only its carrier-cardinality readout. -/
abbrev arena : DependentFamily.Arena where
  signature := signature.{u}
  Law R := ∀ {G : Type u} [AddCommGroup G] [Finite G]
    (m : ℕ) (_hm : 3 ≤ m) (f : Coordinate m → G)
    (_hq : addOrderOf (f (q m)) = m)
    (_hzero : ∀ C : Finset (Coordinate m),
      (C.Nonempty ∧ (∑ x ∈ C, f x) = 0) ↔
        ∃ j : Index m, C = triple m j),
    2 * m * (m - 1) ≤ R.readout () () G

abbrev sourceScope := type_of% (@finite_abelian_carrier_card_lower_bound.{u})

private theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := Iff.rfl

private theorem actual_positive : arena.{u}.Law actual.{u} :=
  @finite_abelian_carrier_card_lower_bound.{u}

/-- An already constructed original carrier provides the nonvacuous intervention. -/
private abbrev Fixture := ULift.{u} (WitnessGroup 3)

private def fixtureLabel (x : Coordinate 3) : Fixture.{u} :=
  (AddEquiv.ulift : Fixture.{u} ≃+ WitnessGroup 3).symm (label 3 x)

private theorem fixture_properties :
    addOrderOf (fixtureLabel.{u} (q 3)) = 3 ∧
    (∀ C : Finset (Coordinate 3),
      (C.Nonempty ∧ (∑ x ∈ C, fixtureLabel.{u} x) = 0) ↔
        ∃ j : Index 3, C = triple 3 j) := by
  have hsource := sharpness 3 (by decide)
  have horder := hsource.2.2.2.2.1
  have hclass := hsource.2.2.2.2.2.1
  constructor
  · simpa only [fixtureLabel, AddEquiv.addOrderOf_eq] using horder
  · intro C
    let e : Fixture.{u} ≃+ WitnessGroup 3 := AddEquiv.ulift
    have hsum : e (∑ x ∈ C, fixtureLabel.{u} x) = ∑ x ∈ C, label 3 x := by
      simp only [map_sum, fixtureLabel, e, AddEquiv.apply_symm_apply]
    have htransport :
        (C.Nonempty ∧ (∑ x ∈ C, fixtureLabel.{u} x) = 0) ↔
          (C.Nonempty ∧ (∑ x ∈ C, label 3 x) = 0) := by
      constructor
      · rintro ⟨hn, hz⟩
        refine ⟨hn, ?_⟩
        rw [← hsum, hz, map_zero]
      · rintro ⟨hn, hz⟩
        refine ⟨hn, e.injective ?_⟩
        rw [hsum, hz, map_zero]
    exact htransport.trans (hclass C)

private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  letI : Finite (WitnessGroup 3) := (sharpness 3 (by decide)).1
  have hf := fixture_properties.{u}
  have hbad := h (G := Fixture.{u}) 3 (by decide) fixtureLabel.{u}
    hf.1 hf.2
  change 12 ≤ (0 : ℕ) at hbad
  omega

def familyRegistration : DependentFamily.Registration arena.{u} sourceScope.{u} where
  actual := actual.{u}
  bridge := source_bridge.{u}
  variation := ⟨actual_positive.{u}, rejected.{u}, rejected_law.{u}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected.{u}, ?_, rfl, rejected_law.{u}⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence.{u}

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@finite_abelian_carrier_card_lower_bound.{u})
      (DependentFamily.Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Combinatorics.Sequenceability.OriginalFiniteAbelianCarrierLowerBound.finite_abelian_carrier_card_lower_bound.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Sequenceability.OriginalFiniteAbelianCarrierLowerBound.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨familyRegistration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence
    ⟨(show Nonempty (DependentFamily.Realization signature.{u}) from ⟨actual.{u}⟩)⟩ trivial
  readout := some (DependentFamily.realize signature.{u}
    (fun _ _ G => Nat.card G) (fun e => nomatch e))
  variation := .evidence ⟨(familyRegistration.{u}).variation⟩ trivial
  sensitivity := .evidence ⟨(familyRegistration.{u}).sensitivity⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Sequenceability.OriginalFiniteAbelianCarrierLowerBound
    definition := none
    coordinates := #[]
    readouts := #[{
      -- Source-only candidate: eight full telescope binders, then LE.rhs.
      -- The actual inspector must validate this path before admission.
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Sequenceability.OriginalFiniteAbelianCarrierLowerBound
