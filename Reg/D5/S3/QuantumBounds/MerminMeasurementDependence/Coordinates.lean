import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuantumBounds.MerminMeasurementDependence.Coordinates
import Reg.Support.DependentFamily
import Reg.D5.S3.QuantumBounds.MerminMeasurementDependence.Coordinates.Settings

/-! Source-bound audits of the public bit, weight, and even-setting coordinates. -/

namespace Reg.D5.S3.QuantumBounds.MerminMeasurementDependence.Coordinates

open _root_.D5.S3.QuantumBounds.MerminMeasurementDependence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace bit_cases

abbrev signature : Signature where
  Params := Unit
  State _ := ZMod 2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

/-- The zero test uses only the finite coordinate of `ZMod 2`. -/
private def zeroDecision (z : ZMod 2) : Decidable (z = 0) where
  decide := Nat.casesOn (show Fin 2 from z).val true (fun _ => false)
  reflects_decide := by
    fin_cases z
    · exact rfl
    · exact one_ne_zero

def actual : Realization signature :=
  realize signature (fun _ _ z => @decide (z = 0) (zeroDecision z)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ z : ZMod 2, R.readout () () z = true ∨ z = 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0
  norm_num [rejected, realize] at hb

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize, zeroDecision]

def source_registration : Registration arena
    (type_of% (@bit_cases)) where
  actual := actual
  bridge := by simp only [actual, realize, decide_eq_true_eq]
  variation := ⟨by
    simpa only [actual, realize, decide_eq_true_eq] using
      bit_cases,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@bit_cases)
      (Realization signature) Unit Unit := {
  unitName := `MerminMeasurementDependence.Coordinates.bit_cases.unit
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ z => @decide (z = 0) (zeroDecision z)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumBounds.MerminMeasurementDependence.Coordinates
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

set_option pp.proofs false in
#print bit_cases
#print axioms source_registration
#print axioms registration

end bit_cases

namespace bitSign_add

abbrev signature : Signature where
  Params := ZMod 2
  State _ := ZMod 2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ a b => bitSign (a + b)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ a b : ZMod 2, R.readout () a b = bitSign a * bitSign b

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0 0
  norm_num [rejected, realize, bitSign, boolSign] at hb

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  norm_num [actual, realize, bitSign, boolSign]

def source_registration : Registration arena
    (type_of% (@bitSign_add)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨bitSign_add,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@bitSign_add)
      (Realization signature) Unit Unit := {
  unitName := `MerminMeasurementDependence.Coordinates.bitSign_add.unit
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ a b => bitSign (a + b)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumBounds.MerminMeasurementDependence.Coordinates
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

set_option pp.proofs false in
#print bitSign_add
#print axioms source_registration
#print axioms registration

end bitSign_add

namespace bitSign_boolBit

abbrev signature : Signature where
  Params := Unit
  State _ := Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ b => bitSign (b.toNat : ZMod 2)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ b : Bool, R.readout () () b = boolSign b

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h false
  norm_num [rejected, realize, boolSign] at hb

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), false, true, ?_⟩
  norm_num [actual, realize, bitSign, boolSign]

def source_registration : Registration arena
    (type_of% (@bitSign_boolBit)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨bitSign_boolBit,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@bitSign_boolBit)
      (Realization signature) Unit Unit := {
  unitName := `MerminMeasurementDependence.Coordinates.bitSign_boolBit.unit
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ b => bitSign (b.toNat : ZMod 2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumBounds.MerminMeasurementDependence.Coordinates
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

set_option pp.proofs false in
#print bitSign_boolBit
#print axioms source_registration
#print axioms registration

end bitSign_boolBit

namespace boolBit_bitBool

abbrev signature : Signature where
  Params := Unit
  State _ := ZMod 2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ZMod 2
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => (decide (z = 1)).toNat) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ z : ZMod 2, R.readout () () z = z

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0
  norm_num [rejected, realize] at hb

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def source_registration : Registration arena
    (type_of% (@boolBit_bitBool)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨boolBit_bitBool,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@boolBit_bitBool)
      (Realization signature) Unit Unit := {
  unitName := `MerminMeasurementDependence.Coordinates.boolBit_bitBool.unit
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => (decide (z = 1)).toNat) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumBounds.MerminMeasurementDependence.Coordinates
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

set_option pp.proofs false in
#print boolBit_bitBool
#print axioms source_registration
#print axioms registration

end boolBit_bitBool

namespace prod_boolSign

abbrev signature : Signature where
  Params := Unit
  State _ := Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ b => boolSign b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena.{u} : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} (x : ι → Bool) (I : Finset ι),
    (∏ i ∈ I, R.readout () () (x i)) = bitSign (∑ i ∈ I, ((x i).toNat : ZMod 2))

private theorem rejected_law.{u} : ¬ arena.{u}.Law rejected := by
  intro h
  have hb := h (fun _ : ULift.{u} Unit => false) {⟨()⟩}
  norm_num [rejected, realize, bitSign, boolSign] at hb

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), false, true, ?_⟩
  norm_num [actual, realize, boolSign]

def source_registration.{u} : Registration arena.{u}
    (type_of% (@prod_boolSign.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨prod_boolSign,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration.{u} :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@prod_boolSign.{u})
      (Realization signature) Unit Unit := {
  unitName := `MerminMeasurementDependence.Coordinates.prod_boolSign.unit
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ b => boolSign b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumBounds.MerminMeasurementDependence.Coordinates
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

set_option pp.proofs false in
#print prod_boolSign
#print axioms source_registration
#print axioms registration

end prod_boolSign

namespace settingWeight_eq_sum

abbrev signature : Signature where
  Params := ℕ
  State n := Fin n → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ n x => hammingDist x (fun _ : Fin n => false)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (x : Fin n → Bool), R.readout () n x = ∑ i, (x i).toNat

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (n := 1) (fun _ => true)
  norm_num [rejected, realize] at hb

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (fun _ => false), (fun _ => true), ?_⟩
  norm_num [actual, realize, hammingDist]

def source_registration : Registration arena
    (type_of% (@settingWeight_eq_sum)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨settingWeight_eq_sum,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@settingWeight_eq_sum)
      (Realization signature) Unit Unit := {
  unitName := `MerminMeasurementDependence.Coordinates.settingWeight_eq_sum.unit
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ n x => hammingDist x (fun _ : Fin n => false)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumBounds.MerminMeasurementDependence.Coordinates
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

set_option pp.proofs false in
#print settingWeight_eq_sum
#print axioms source_registration
#print axioms registration

end settingWeight_eq_sum

namespace parity_sum

abbrev signature : Signature where
  Params := ℕ
  State n := Fin n → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ZMod 2
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ n x => ∑ i : Fin n, ((x i).toNat : ZMod 2)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (x : Fin n → Bool),
    R.readout () n x = (hammingDist x (fun _ => false) : ZMod 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (n := 0) (fun _ => false)
  norm_num [rejected, realize, hammingDist] at hb

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (fun _ => false), (fun _ => true), ?_⟩
  norm_num [actual, realize]

def source_registration : Registration arena
    (type_of% (@parity_sum)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨parity_sum,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@parity_sum)
      (Realization signature) Unit Unit := {
  unitName := `MerminMeasurementDependence.Coordinates.parity_sum.unit
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ n x => ∑ i : Fin n, ((x i).toNat : ZMod 2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumBounds.MerminMeasurementDependence.Coordinates
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

set_option pp.proofs false in
#print parity_sum
#print axioms source_registration
#print axioms registration

end parity_sum

namespace setting_parity

abbrev signature : Signature where
  Params := Unit
  State _ := Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ZMod 2
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ b => b.toNat) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (x : Setting n), ∑ i, R.readout () () (x.1 i) = 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let x : Setting 1 := ⟨fun _ => false, by simp [hammingDist]⟩
  have hb := h x
  norm_num [rejected, realize] at hb

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), false, true, ?_⟩
  norm_num [actual, realize]

def source_registration : Registration arena
    (type_of% (@setting_parity)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨setting_parity,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@setting_parity)
      (Realization signature) Unit Unit := {
  unitName := `MerminMeasurementDependence.Coordinates.setting_parity.unit
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ b => b.toNat) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumBounds.MerminMeasurementDependence.Coordinates
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

set_option pp.proofs false in
#print setting_parity
#print axioms source_registration
#print axioms registration

end setting_parity

end
end Reg.D5.S3.QuantumBounds.MerminMeasurementDependence.Coordinates
