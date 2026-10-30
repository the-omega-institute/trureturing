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

namespace Reg.D5.S3.Combinatorics.Sequenceability.OriginalCyclicFiveCarrierLowerBound.Normalization

universe v
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.Reg.D5.S3.Combinatorics.Sequenceability.OriginalSharpnessCarrierLowerBound
  (signature actual dependence)
open _root_.D5.S3.Combinatorics.Sequenceability.OriginalCyclicFiveCarrierLowerBound
  (normalized_signed_classes)

/-- Only the returned half-modulus bound varies; the positivity premise and the
forbidden total sum retain their original cardinalities. -/
abbrev arena : DependentFamily.Arena where
  signature := signature.{v}
  Law R := ∀ {K : Type v} [AddCommGroup K] [Finite K] [IsAddCyclic K]
    (t : ℕ) (_hn : 0 < Nat.card K) (A : Fin t → K)
    (_hA0 : ∀ i, A i ≠ 0) (_hAA : Function.Injective A)
    (_hAN : ∀ i j, i ≠ j → A i ≠ -A j)
    (_htriple : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ∀ s t u : Bool,
      (if s then -A i else A i) + (if t then -A j else A j) +
        (if u then -A k else A k) ≠ 0),
    ∃ r : Fin t → ℕ,
      (∀ i, 0 < r i) ∧ (∀ i, 2 * r i ≤ R.readout () () K) ∧ Function.Injective r ∧
      (∀ i j k, i ≠ j → i ≠ k → j ≠ k → r i + r j ≠ r k) ∧
      (∀ i j k, i ≠ j → i ≠ k → j ≠ k → r i + r j + r k ≠ Nat.card K)

abbrev sourceScope := type_of% (@normalized_signed_classes.{v})
private theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := Iff.rfl
private theorem actual_positive : arena.{v}.Law actual.{v} := @normalized_signed_classes.{v}

def rejected1 : DependentFamily.Realization signature.{v} :=
  DependentFamily.realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private abbrev Fixture := ULift.{v} (ZMod 2)
private def fixtureA (_ : Fin 1) : Fixture.{v} := ⟨1⟩

private theorem rejected_law : ¬ arena.{v}.Law rejected1.{v} := by
  intro h
  let e : ZMod 2 ≃+ Fixture.{v} :=
    (AddEquiv.ulift : Fixture.{v} ≃+ ZMod 2).symm
  letI : IsAddCyclic Fixture.{v} := isAddCyclic_of_surjective e e.surjective
  have hA0 (i : Fin 1) : fixtureA.{v} i ≠ 0 := by
    intro he
    have hz := congrArg ULift.down he
    change (1 : ZMod 2) = 0 at hz
    norm_num at hz
  have hAA : Function.Injective fixtureA.{v} := fun i j _ => Subsingleton.elim i j
  have hAN (i j : Fin 1) (hij : i ≠ j) : fixtureA.{v} i ≠ -fixtureA.{v} j :=
    (hij (Subsingleton.elim i j)).elim
  have htriple (i j k : Fin 1) (hij : i ≠ j) (_hik : i ≠ k) (_hjk : j ≠ k)
      (s t u : Bool) :
      (if s then -fixtureA.{v} i else fixtureA.{v} i) +
        (if t then -fixtureA.{v} j else fixtureA.{v} j) +
        (if u then -fixtureA.{v} k else fixtureA.{v} k) ≠ 0 :=
    (hij (Subsingleton.elim i j)).elim
  have hn : 0 < Nat.card Fixture.{v} := by
    simp only [Fixture, Nat.card_ulift, Nat.card_zmod]
    decide
  obtain ⟨r, hpos, hbound, _, _, _⟩ :=
    h (K := Fixture.{v}) 1 hn fixtureA.{v} hA0 hAA hAN htriple
  have hp := hpos 0
  have hb := hbound 0
  change 2 * r 0 ≤ 1 at hb
  omega

def familyRegistration : DependentFamily.Registration arena.{v} sourceScope.{v} where
  actual := actual.{v}
  bridge := source_bridge.{v}
  variation := ⟨actual_positive.{v}, rejected1.{v}, rejected_law.{v}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected1.{v}, ?_, rfl, rejected_law.{v}⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence.{v}

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@normalized_signed_classes.{v})
      (DependentFamily.Realization signature.{v}) Unit Unit where
  unitName := `D5.S3.Combinatorics.Sequenceability.OriginalCyclicFiveCarrierLowerBound.normalized_signed_classes.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Sequenceability.OriginalCyclicFiveCarrierLowerBound.Normalization.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{v}⟩
  objectArena := .source ⟨arena.{v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{v} ⟨familyRegistration.{v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence
    ⟨(show Nonempty (DependentFamily.Realization signature.{v}) from ⟨actual.{v}⟩)⟩ trivial
  readout := some (DependentFamily.realize signature.{v}
    (fun _ _ G => Nat.card G) (fun e => nomatch e))
  variation := .evidence ⟨(familyRegistration.{v}).variation⟩ trivial
  sensitivity := .evidence ⟨(familyRegistration.{v}).sensitivity⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Sequenceability.OriginalCyclicFiveCarrierLowerBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "fn", "arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Sequenceability.OriginalCyclicFiveCarrierLowerBound.Normalization
