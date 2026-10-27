import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Sequenceability.OriginalSharpnessCarrierLowerBound
import D5.S3.Combinatorics.Sequenceability.OriginalPolynomialCyclicOrderSharpness
import Mathlib.Algebra.Group.ULift

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u_2

namespace Reg.D5.S3.Combinatorics.Sequenceability.OriginalSharpnessCarrierLowerBound

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.Combinatorics.Sequenceability.OriginalFiniteOrderSharpness
  (Index Coordinate q triple)
open _root_.D5.S3.Combinatorics.Sequenceability.OriginalSharpnessCarrierLowerBound
  (carrier_card_lower_bound)
open _root_.D5.S3.Combinatorics.Sequenceability.OriginalPolynomialCyclicOrderSharpness
  (WitnessGroup label sharpness)
open scoped Classical BigOperators

abbrev signature : DependentFamily.Signature where
  Params := Unit
  State _ := Type u_2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature.{u_2} :=
  DependentFamily.realize signature (fun _ _ G => Nat.card G) (fun e => nomatch e)

def rejected : DependentFamily.Realization signature.{u_2} :=
  DependentFamily.realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The entire source telescope, with only its carrier-cardinality readout varied. -/
abbrev arena : DependentFamily.Arena where
  signature := signature.{u_2}
  Law R := ∀ {G : Type u_2} [AddCommGroup G] [Finite G]
    (m : ℕ) (_hm : 2 ≤ m) (f : Coordinate m → G)
    (_hq : addOrderOf (f (q m)) = m)
    (_hzero : ∀ C : Finset (Coordinate m),
      (C.Nonempty ∧ (∑ x ∈ C, f x) = 0) ↔
        ∃ j : Index m, C = triple m j),
    m * (m + 1) ≤ R.readout () () G

abbrev sourceScope := type_of% (@carrier_card_lower_bound.{u_2})

private theorem source_bridge : sourceScope.{u_2} ↔ arena.{u_2}.Law actual := Iff.rfl

private theorem actual_positive : arena.{u_2}.Law actual :=
  @carrier_card_lower_bound.{u_2}

/-- A universe lift of an existing finite cyclic realization. -/
private abbrev Fixture := ULift.{u_2} (WitnessGroup 2)

private def fixtureLabel (x : Coordinate 2) : Fixture.{u_2} :=
  (AddEquiv.ulift : Fixture.{u_2} ≃+ WitnessGroup 2).symm (label 2 x)

private theorem fixture_properties :
    addOrderOf (fixtureLabel.{u_2} (q 2)) = 2 ∧
    (∀ C : Finset (Coordinate 2),
      (C.Nonempty ∧ (∑ x ∈ C, fixtureLabel.{u_2} x) = 0) ↔
        ∃ j : Index 2, C = triple 2 j) := by
  obtain ⟨_, _, _, _, _, _, horder, hclass, _, _, _, _, _⟩ :=
    sharpness 2 (by decide)
  constructor
  · simpa only [fixtureLabel, AddEquiv.addOrderOf_eq] using horder
  · intro C
    let e : Fixture.{u_2} ≃+ WitnessGroup 2 := AddEquiv.ulift
    have hsum : e (∑ x ∈ C, fixtureLabel.{u_2} x) = ∑ x ∈ C, label 2 x := by
      simp only [map_sum, fixtureLabel, e, AddEquiv.apply_symm_apply]
    have htransport :
        (C.Nonempty ∧ (∑ x ∈ C, fixtureLabel.{u_2} x) = 0) ↔
          (C.Nonempty ∧ (∑ x ∈ C, label 2 x) = 0) := by
      constructor
      · rintro ⟨hn, hz⟩
        refine ⟨hn, ?_⟩
        rw [← hsum, hz, map_zero]
      · rintro ⟨hn, hz⟩
        refine ⟨hn, e.injective ?_⟩
        rw [hsum, hz, map_zero]
    exact htransport.trans (hclass C)

private theorem rejected_law : ¬ arena.{u_2}.Law rejected := by
  intro h
  letI : Finite (WitnessGroup 2) := (sharpness 2 (by decide)).1
  have hf := fixture_properties.{u_2}
  have hbad := h (G := Fixture.{u_2}) 2 (by decide) fixtureLabel hf.1 hf.2
  change 2 * (2 + 1) ≤ (0 : ℕ) at hbad
  omega

private theorem dependence :
    DependentFamily.ObservationalDependence signature.{u_2} actual := by
  intro i
  refine ⟨(), ULift.{u_2} Unit, ULift.{u_2} Bool, ?_⟩
  change Nat.card (ULift.{u_2} Unit) ≠ Nat.card (ULift.{u_2} Bool)
  simp [Nat.card_eq_fintype_card]

def familyRegistration : DependentFamily.Registration arena.{u_2} sourceScope.{u_2} where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@carrier_card_lower_bound.{u_2}) (DependentFamily.Realization signature.{u_2})
      Unit Unit where
  unitName := `D5.S3.Combinatorics.Sequenceability.OriginalSharpnessCarrierLowerBound.carrier_card_lower_bound.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Sequenceability.OriginalSharpnessCarrierLowerBound.familyRegistration
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
    owner := `D5.S3.Combinatorics.Sequenceability.OriginalSharpnessCarrierLowerBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Sequenceability.OriginalSharpnessCarrierLowerBound

namespace Reg.D5.S3.Combinatorics.Sequenceability.OriginalSharpnessCarrierLowerBound.Cyclic

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.Combinatorics.Sequenceability.OriginalFiniteOrderSharpness
  (Index Coordinate q triple)
open _root_.D5.S3.Combinatorics.Sequenceability.OriginalSharpnessCarrierLowerBound
  (cyclic_carrier_card_lower_bound)
open _root_.D5.S3.Combinatorics.Sequenceability.OriginalPolynomialCyclicOrderSharpness
  (WitnessGroup sharpness)
open scoped Classical BigOperators

/-- The full cyclic source telescope, varying only the carrier-cardinality readout. -/
abbrev arena : DependentFamily.Arena where
  signature := signature.{u_2}
  Law R := ∀ {G : Type u_2} [AddCommGroup G] [Finite G] [IsAddCyclic G]
    (m : ℕ) (_hm : 2 ≤ m) (f : Coordinate m → G)
    (_hq : addOrderOf (f (q m)) = m)
    (_hzero : ∀ C : Finset (Coordinate m),
      (C.Nonempty ∧ (∑ x ∈ C, f x) = 0) ↔
        ∃ j : Index m, C = triple m j),
    2 * m * m ≤ R.readout () () G

abbrev sourceScope := type_of% (@cyclic_carrier_card_lower_bound.{u_2})

private theorem source_bridge :
    sourceScope.{u_2} ↔ arena.{u_2}.Law actual.{u_2} := Iff.rfl

private theorem actual_positive : arena.{u_2}.Law actual.{u_2} :=
  @cyclic_carrier_card_lower_bound.{u_2}

private theorem rejected_law : ¬ arena.{u_2}.Law rejected.{u_2} := by
  intro h
  letI : Finite (WitnessGroup 2) := (sharpness 2 (by decide)).1
  letI : IsAddCyclic (WitnessGroup 2) := ZMod.instIsAddCyclic _
  let e : WitnessGroup 2 ≃+ Fixture.{u_2} :=
    (AddEquiv.ulift : Fixture.{u_2} ≃+ WitnessGroup 2).symm
  letI : IsAddCyclic Fixture.{u_2} :=
    isAddCyclic_of_surjective e e.surjective
  have hf := fixture_properties.{u_2}
  have hbad := h (G := Fixture.{u_2}) 2 (by decide) fixtureLabel.{u_2} hf.1 hf.2
  change 2 * 2 * 2 ≤ (0 : ℕ) at hbad
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
      (@cyclic_carrier_card_lower_bound.{u_2})
      (DependentFamily.Realization signature.{u_2}) Unit Unit where
  unitName := `D5.S3.Combinatorics.Sequenceability.OriginalSharpnessCarrierLowerBound.cyclic_carrier_card_lower_bound.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Sequenceability.OriginalSharpnessCarrierLowerBound.Cyclic.familyRegistration
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
    owner := `D5.S3.Combinatorics.Sequenceability.OriginalSharpnessCarrierLowerBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Sequenceability.OriginalSharpnessCarrierLowerBound.Cyclic

namespace Reg.D5.S3.Combinatorics.Sequenceability.OriginalSharpnessCarrierLowerBound.Odd

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.Combinatorics.Sequenceability.OriginalFiniteOrderSharpness
  (Index Coordinate q triple)
open _root_.D5.S3.Combinatorics.Sequenceability.OriginalSharpnessCarrierLowerBound
  (odd_carrier_card_lower_bound)
open _root_.D5.S3.Combinatorics.Sequenceability.OriginalPolynomialCyclicOrderSharpness
  (WitnessGroup label sharpness)
open scoped Classical BigOperators

/-- The full odd-cardinality source telescope, varying only the carrier-cardinality readout. -/
abbrev arena : DependentFamily.Arena where
  signature := signature.{u_2}
  Law R := ∀ {G : Type u_2} [AddCommGroup G] [Finite G]
    (m : ℕ) (_hm : 2 ≤ m) (f : Coordinate m → G)
    (_hq : addOrderOf (f (q m)) = m)
    (_hzero : ∀ C : Finset (Coordinate m),
      (C.Nonempty ∧ (∑ x ∈ C, f x) = 0) ↔
        ∃ j : Index m, C = triple m j)
    (_hodd : Odd (Nat.card G)),
    m * (2 * m + 1) ≤ R.readout () () G

abbrev sourceScope := type_of% (@odd_carrier_card_lower_bound.{u_2})

private theorem source_bridge :
    sourceScope.{u_2} ↔ arena.{u_2}.Law actual.{u_2} := Iff.rfl

private theorem actual_positive : arena.{u_2}.Law actual.{u_2} :=
  @odd_carrier_card_lower_bound.{u_2}

/-- A universe lift of the existing thirty-three-element realization. -/
private abbrev Fixture := ULift.{u_2} (WitnessGroup 3)

private def fixtureLabel (x : Coordinate 3) : Fixture.{u_2} :=
  (AddEquiv.ulift : Fixture.{u_2} ≃+ WitnessGroup 3).symm (label 3 x)

private theorem fixture_properties :
    addOrderOf (fixtureLabel.{u_2} (q 3)) = 3 ∧
    (∀ C : Finset (Coordinate 3),
      (C.Nonempty ∧ (∑ x ∈ C, fixtureLabel.{u_2} x) = 0) ↔
        ∃ j : Index 3, C = triple 3 j) := by
  obtain ⟨_, _, _, _, _, _, horder, hclass, _, _, _, _, _⟩ :=
    sharpness 3 (by decide)
  constructor
  · simpa only [fixtureLabel, AddEquiv.addOrderOf_eq] using horder
  · intro C
    let e : Fixture.{u_2} ≃+ WitnessGroup 3 := AddEquiv.ulift
    have hsum : e (∑ x ∈ C, fixtureLabel.{u_2} x) = ∑ x ∈ C, label 3 x := by
      simp only [map_sum, fixtureLabel, e, AddEquiv.apply_symm_apply]
    have htransport :
        (C.Nonempty ∧ (∑ x ∈ C, fixtureLabel.{u_2} x) = 0) ↔
          (C.Nonempty ∧ (∑ x ∈ C, label 3 x) = 0) := by
      constructor
      · rintro ⟨hn, hz⟩
        refine ⟨hn, ?_⟩
        rw [← hsum, hz, map_zero]
      · rintro ⟨hn, hz⟩
        refine ⟨hn, e.injective ?_⟩
        rw [hsum, hz, map_zero]
    exact htransport.trans (hclass C)

private theorem fixture_odd : Odd (Nat.card Fixture.{u_2}) := by
  have hcard : Nat.card (WitnessGroup 3) = 33 := by
    simpa using (sharpness 3 (by decide)).2.2.1
  change Odd (Nat.card (ULift.{u_2} (WitnessGroup 3)))
  rw [Nat.card_ulift, hcard]
  decide

private theorem rejected_law : ¬ arena.{u_2}.Law rejected.{u_2} := by
  intro h
  letI : Finite (WitnessGroup 3) := (sharpness 3 (by decide)).1
  have hf := fixture_properties.{u_2}
  have hbad := h (G := Fixture.{u_2}) 3 (by decide) fixtureLabel.{u_2}
    hf.1 hf.2 fixture_odd.{u_2}
  change 3 * (2 * 3 + 1) ≤ (0 : ℕ) at hbad
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
      (@odd_carrier_card_lower_bound.{u_2})
      (DependentFamily.Realization signature.{u_2}) Unit Unit where
  unitName := `D5.S3.Combinatorics.Sequenceability.OriginalSharpnessCarrierLowerBound.odd_carrier_card_lower_bound.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Sequenceability.OriginalSharpnessCarrierLowerBound.Odd.familyRegistration
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
    owner := `D5.S3.Combinatorics.Sequenceability.OriginalSharpnessCarrierLowerBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Sequenceability.OriginalSharpnessCarrierLowerBound.Odd
