import Reg.D5.S3.Combinatorics.Sequenceability.OriginalSharpnessCarrierLowerBound
import D5.S3.Combinatorics.Sequenceability.OriginalCyclicSevenCarrierLowerBound
import D5.S3.Combinatorics.Sequenceability.OriginalSignedCyclicQuotientSharpness
import Mathlib.Algebra.Group.ULift

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

namespace Reg.D5.S3.Combinatorics.Sequenceability.OriginalCyclicSevenCarrierLowerBound

open _root_.Reg.D5.S3.Combinatorics.Sequenceability.OriginalSharpnessCarrierLowerBound
  (signature actual rejected dependence)
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.Combinatorics.Sequenceability.OriginalFiniteOrderSharpness
  (Index Coordinate q triple)
open _root_.D5.S3.Combinatorics.Sequenceability.OriginalSignedCyclicQuotientSharpness
  (WitnessGroup label modulus sharpness)
open _root_.D5.S3.Combinatorics.Sequenceability.OriginalCyclicSevenCarrierLowerBound
  (cyclic_seven_carrier_card_lower_bound)
open scoped Classical BigOperators

/-- The complete order-seven cyclic source telescope, varying only its cardinality readout. -/
abbrev arena : DependentFamily.Arena where
  signature := signature.{u}
  Law R := ∀ {G : Type u} [AddCommGroup G] [Finite G] [IsAddCyclic G]
    (f : Coordinate 7 → G)
    (_hq : addOrderOf (f (q 7)) = 7)
    (_hzero : ∀ C : Finset (Coordinate 7),
      (C.Nonempty ∧ (∑ x ∈ C, f x) = 0) ↔
        ∃ j : Index 7, C = triple 7 j),
    154 ≤ R.readout () () G

abbrev sourceScope := type_of% (@cyclic_seven_carrier_card_lower_bound.{u})

private theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := Iff.rfl

private theorem actual_positive : arena.{u}.Law actual.{u} :=
  @cyclic_seven_carrier_card_lower_bound.{u}

/-- The existing signed s=three, k=zero construction is a 154-element carrier. -/
private abbrev Fixture := ULift.{u} (WitnessGroup 3 0)

private def fixtureLabel (x : Coordinate 7) : Fixture.{u} :=
  (AddEquiv.ulift : Fixture.{u} ≃+ WitnessGroup 3 0).symm (label 3 0 x)

private theorem fixture_properties :
    Nat.card Fixture.{u} = 154 ∧
    addOrderOf (fixtureLabel.{u} (q 7)) = 7 ∧
    (∀ C : Finset (Coordinate 7),
      (C.Nonempty ∧ (∑ x ∈ C, fixtureLabel.{u} x) = 0) ↔
        ∃ j : Index 7, C = triple 7 j) := by
  have h := sharpness 0 3 (by decide)
  have hcard : Nat.card (WitnessGroup 3 0) = 154 := by
    simpa only [show modulus 3 * (4 * modulus 3 - 6 + 2 * 0) = 154 from by decide]
      using h.2.1
  have horder : addOrderOf (label 3 0 (q 7)) = 7 := h.2.2.1
  have hclass : ∀ C : Finset (Coordinate 7),
      (C.Nonempty ∧ (∑ x ∈ C, label 3 0 x) = 0) ↔
        ∃ j : Index 7, C = triple 7 j := h.2.2.2.2
  constructor
  · simpa only [Fixture, Nat.card_ulift] using hcard
  · constructor
    · simpa only [fixtureLabel, AddEquiv.addOrderOf_eq] using horder
    · intro C
      let e : Fixture.{u} ≃+ WitnessGroup 3 0 := AddEquiv.ulift
      have hsum : e (∑ x ∈ C, fixtureLabel.{u} x) = ∑ x ∈ C, label 3 0 x := by
        simp only [map_sum, fixtureLabel, e, AddEquiv.apply_symm_apply]
      have htransport :
          (C.Nonempty ∧ (∑ x ∈ C, fixtureLabel.{u} x) = 0) ↔
            (C.Nonempty ∧ (∑ x ∈ C, label 3 0 x) = 0) := by
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
  have hs := sharpness 0 3 (by decide)
  letI : Finite (WitnessGroup 3 0) := hs.1
  letI : IsAddCyclic (WitnessGroup 3 0) := hs.2.2.2.1 (by decide)
  let e : WitnessGroup 3 0 ≃+ Fixture.{u} :=
    (AddEquiv.ulift : Fixture.{u} ≃+ WitnessGroup 3 0).symm
  letI : IsAddCyclic Fixture.{u} :=
    isAddCyclic_of_surjective e e.surjective
  have hf := fixture_properties.{u}
  have hbad := h (G := Fixture.{u}) fixtureLabel.{u} hf.2.1 hf.2.2
  change 154 ≤ (0 : ℕ) at hbad
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
      (@cyclic_seven_carrier_card_lower_bound.{u})
      (DependentFamily.Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Combinatorics.Sequenceability.OriginalCyclicSevenCarrierLowerBound.cyclic_seven_carrier_card_lower_bound.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Sequenceability.OriginalCyclicSevenCarrierLowerBound.familyRegistration
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
    owner := `D5.S3.Combinatorics.Sequenceability.OriginalCyclicSevenCarrierLowerBound
    definition := none
    coordinates := #[]
    readouts := #[{
      -- G, its three group hypotheses, f, hq, hzero; then the conclusion's rhs.
      -- Source-only: the native inspector must confirm this raw seven-binder path.
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Sequenceability.OriginalCyclicSevenCarrierLowerBound
