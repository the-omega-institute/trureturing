import Reg.D5.S3.Combinatorics.Sequenceability.OriginalSharpnessCarrierLowerBound
import D5.S3.Combinatorics.Sequenceability.OriginalCyclicFiveCarrierLowerBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u_2

namespace Reg.D5.S3.Combinatorics.Sequenceability.OriginalCyclicFiveCarrierLowerBound

open _root_.Reg.D5.S3.Combinatorics.Sequenceability.OriginalSharpnessCarrierLowerBound
  (signature actual rejected dependence)

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.Combinatorics.Sequenceability.OriginalFiniteOrderSharpness
  (Index Coordinate q triple)
open _root_.D5.S3.Combinatorics.Sequenceability.OriginalCyclicFiveCarrierLowerBound
  (cyclic_five_carrier_card_lower_bound)
open _root_.D5.S3.Combinatorics.Sequenceability.OriginalPolynomialCyclicOrderSharpness
  (WitnessGroup label sharpness)
open scoped Classical BigOperators

/-- The complete parameter-five cyclic telescope, varying only the carrier readout. -/
abbrev arena : DependentFamily.Arena where
  signature := signature.{u_2}
  Law R := ∀ {G : Type u_2} [AddCommGroup G] [Finite G] [IsAddCyclic G]
    (f : Coordinate 5 → G)
    (_hq : addOrderOf (f (q 5)) = 5)
    (_hzero : ∀ C : Finset (Coordinate 5),
      (C.Nonempty ∧ (∑ x ∈ C, f x) = 0) ↔
        ∃ j : Index 5, C = triple 5 j),
    70 ≤ R.readout () () G

abbrev sourceScope := type_of% (@cyclic_five_carrier_card_lower_bound.{u_2})

private theorem source_bridge :
    sourceScope.{u_2} ↔ arena.{u_2}.Law actual.{u_2} := Iff.rfl

private theorem actual_positive : arena.{u_2}.Law actual.{u_2} :=
  @cyclic_five_carrier_card_lower_bound.{u_2}

/-- Reuse the existing polynomial cyclic construction at the required parameter. -/
private abbrev Fixture := ULift.{u_2} (WitnessGroup 5)

private def fixtureLabel (x : Coordinate 5) : Fixture.{u_2} :=
  (AddEquiv.ulift : Fixture.{u_2} ≃+ WitnessGroup 5).symm (label 5 x)

private theorem fixture_properties :
    addOrderOf (fixtureLabel.{u_2} (q 5)) = 5 ∧
    (∀ C : Finset (Coordinate 5),
      (C.Nonempty ∧ (∑ x ∈ C, fixtureLabel.{u_2} x) = 0) ↔
        ∃ j : Index 5, C = triple 5 j) := by
  obtain ⟨_, _, _, _, _, _, horder, hclass, _, _, _, _, _⟩ :=
    sharpness 5 (by decide)
  constructor
  · simpa only [fixtureLabel, AddEquiv.addOrderOf_eq] using horder
  · intro C
    let e : Fixture.{u_2} ≃+ WitnessGroup 5 := AddEquiv.ulift
    have hsum : e (∑ x ∈ C, fixtureLabel.{u_2} x) = ∑ x ∈ C, label 5 x := by
      simp only [map_sum, fixtureLabel, e, AddEquiv.apply_symm_apply]
    have htransport :
        (C.Nonempty ∧ (∑ x ∈ C, fixtureLabel.{u_2} x) = 0) ↔
          (C.Nonempty ∧ (∑ x ∈ C, label 5 x) = 0) := by
      constructor
      · rintro ⟨hn, hz⟩
        refine ⟨hn, ?_⟩
        rw [← hsum, hz, map_zero]
      · rintro ⟨hn, hz⟩
        refine ⟨hn, e.injective ?_⟩
        rw [hsum, hz, map_zero]
    exact htransport.trans (hclass C)

private theorem rejected_law : ¬ arena.{u_2}.Law rejected.{u_2} := by
  intro h
  letI : Finite (WitnessGroup 5) := (sharpness 5 (by decide)).1
  letI : IsAddCyclic (WitnessGroup 5) := ZMod.instIsAddCyclic _
  let e : WitnessGroup 5 ≃+ Fixture.{u_2} :=
    (AddEquiv.ulift : Fixture.{u_2} ≃+ WitnessGroup 5).symm
  letI : IsAddCyclic Fixture.{u_2} :=
    isAddCyclic_of_surjective e e.surjective
  have hf := fixture_properties.{u_2}
  have hbad := h (G := Fixture.{u_2}) fixtureLabel.{u_2} hf.1 hf.2
  change 70 ≤ (0 : ℕ) at hbad
  omega

def familyRegistration : DependentFamily.Registration arena.{u_2} sourceScope.{u_2} where
  actual := actual.{u_2}
  bridge := source_bridge.{u_2}
  variation := ⟨actual_positive.{u_2}, rejected.{u_2}, rejected_law.{u_2}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected.{u_2}, ?_, rfl, rejected_law.{u_2}⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence.{u_2}

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@cyclic_five_carrier_card_lower_bound.{u_2})
      (DependentFamily.Realization signature.{u_2}) Unit Unit where
  unitName := `D5.S3.Combinatorics.Sequenceability.OriginalCyclicFiveCarrierLowerBound.cyclic_five_carrier_card_lower_bound.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Sequenceability.OriginalCyclicFiveCarrierLowerBound.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u_2}⟩
  objectArena := .source ⟨arena.{u_2}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u_2} ⟨familyRegistration.{u_2}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence
    ⟨(show Nonempty (DependentFamily.Realization signature.{u_2}) from ⟨actual.{u_2}⟩)⟩ trivial
  readout := some (DependentFamily.realize signature.{u_2}
    (fun _ _ G => Nat.card G) (fun e => nomatch e))
  variation := .evidence ⟨(familyRegistration.{u_2}).variation⟩ trivial
  sensitivity := .evidence ⟨(familyRegistration.{u_2}).sensitivity⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Sequenceability.OriginalCyclicFiveCarrierLowerBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Sequenceability.OriginalCyclicFiveCarrierLowerBound
