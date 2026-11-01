import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuantumBounds.MerminMeasurementDependence.Coordinates
import Reg.Support.DependentFamily

/-! Source-bound audits of the public bit, weight, and even-setting coordinates. -/

namespace Reg.D5.S3.QuantumBounds.MerminMeasurementDependence.Coordinates.Settings

open _root_.D5.S3.QuantumBounds.MerminMeasurementDependence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace settingWeight_snoc

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
  Law R := ∀ {d : ℕ} (x : Fin d → Bool) (b : Bool),
    hammingDist (Fin.snoc x b) (fun _ => false) = R.readout () d x + b.toNat

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (d := 1) (fun _ => true) false
  have hw : hammingDist (Fin.snoc (fun _ : Fin 1 => true) false)
      (fun _ => false) = 1 := by decide
  norm_num [rejected, realize, hw] at hb

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (fun _ => false), (fun _ => true), ?_⟩
  norm_num [actual, realize, hammingDist]

def source_registration : Registration arena
    (type_of% (@settingWeight_snoc)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨settingWeight_snoc,
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
      (@settingWeight_snoc)
      (Realization signature) Unit Unit := {
  unitName := `MerminMeasurementDependence.Coordinates.settingWeight_snoc.unit
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
      path := #["body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

set_option pp.proofs false in
#print settingWeight_snoc
#print axioms source_registration
#print axioms registration

end settingWeight_snoc

namespace weight_not_add_weight

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
  Law R := ∀ {n : ℕ} (x : Fin n → Bool),
    hammingDist (fun i => !(x i)) (fun _ => false) + R.readout () n x = n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (n := 1) (fun _ => true)
  norm_num [rejected, realize, hammingDist] at hb

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (fun _ => false), (fun _ => true), ?_⟩
  norm_num [actual, realize, hammingDist]

def source_registration : Registration arena
    (type_of% (@weight_not_add_weight)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨weight_not_add_weight,
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
      (@weight_not_add_weight)
      (Realization signature) Unit Unit := {
  unitName := `MerminMeasurementDependence.Coordinates.weight_not_add_weight.unit
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
      path := #["body", "body", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

set_option pp.proofs false in
#print weight_not_add_weight
#print axioms source_registration
#print axioms registration

end weight_not_add_weight

namespace evenSetting_freeSetting

abbrev signature : Signature where
  Params := ℕ
  State n := Setting (n + 1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Fin n → ZMod 2
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => freeSetting x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} (x : Setting (d + 1)), evenSetting (R.readout () d x) = x

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := congrArg freeSetting (h (evenSetting (fun _ : Fin 1 => 1)))
  rw [freeSetting_evenSetting, freeSetting_evenSetting] at hb
  have hc := congrFun hb 0
  norm_num [rejected, realize] at hc

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, evenSetting (fun _ => 0), evenSetting (fun _ => 1), ?_⟩
  intro h
  have hc := congrFun h 0
  norm_num [actual, realize, freeSetting_evenSetting] at hc

def source_registration : Registration arena
    (type_of% (@evenSetting_freeSetting)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨evenSetting_freeSetting,
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
      (@evenSetting_freeSetting)
      (Realization signature) Unit Unit := {
  unitName := `MerminMeasurementDependence.Coordinates.evenSetting_freeSetting.unit
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
  readout := some (realize signature (fun _ _ x => freeSetting x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumBounds.MerminMeasurementDependence.Coordinates
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

set_option pp.proofs false in
#print evenSetting_freeSetting
#print axioms source_registration
#print axioms registration

end evenSetting_freeSetting

namespace freeSetting_evenSetting

abbrev signature : Signature where
  Params := ℕ
  State n := Fin n → ZMod 2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Setting (n + 1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => evenSetting x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => evenSetting (fun _ => 0)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} (x : Fin d → ZMod 2), freeSetting (R.readout () d x) = x

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := congrFun (h (d := 1) (fun _ => 1)) 0
  norm_num [rejected, realize, freeSetting_evenSetting] at hb

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hc := congrFun (congrArg freeSetting h) 0
  norm_num [actual, realize, freeSetting_evenSetting] at hc

def source_registration : Registration arena
    (type_of% (@freeSetting_evenSetting)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨freeSetting_evenSetting,
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
      (@freeSetting_evenSetting)
      (Realization signature) Unit Unit := {
  unitName := `MerminMeasurementDependence.Coordinates.freeSetting_evenSetting.unit
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
  readout := some (realize signature (fun _ _ x => evenSetting x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumBounds.MerminMeasurementDependence.Coordinates
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

set_option pp.proofs false in
#print freeSetting_evenSetting
#print axioms source_registration
#print axioms registration

end freeSetting_evenSetting

namespace evenRepresentative_last

abbrev signature : Signature where
  Params := ℕ
  State n := Setting (2 * n + 2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Setting (2 * n + 2)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ k x => evenRepresentative k x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k : ℕ) (x : Setting (2 * k + 2)),
    (R.readout () k x).1 (Fin.last (2 * k + 1)) = false

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0 (evenSetting (fun _ : Fin 1 => 1))
  norm_num [rejected, realize, evenSetting, evenExtension, bitSign, boolSign] at hb

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  let a : Setting 4 := ⟨fun _ => false, by decide⟩
  let b : Setting 4 := ⟨fun j => decide (j.val < 2), by decide⟩
  refine ⟨1, a, b, ?_⟩
  intro h
  have hc := congrArg (fun x : Setting 4 => x.1 0) h
  norm_num [actual, realize, a, b, evenRepresentative, flipSetting] at hc

def source_registration : Registration arena
    (type_of% (@evenRepresentative_last)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨evenRepresentative_last,
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
      (@evenRepresentative_last)
      (Realization signature) Unit Unit := {
  unitName := `MerminMeasurementDependence.Coordinates.evenRepresentative_last.unit
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
  readout := some (realize signature (fun _ k x => evenRepresentative k x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumBounds.MerminMeasurementDependence.Coordinates
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

set_option pp.proofs false in
#print evenRepresentative_last
#print axioms source_registration
#print axioms registration

end evenRepresentative_last

end
end Reg.D5.S3.QuantumBounds.MerminMeasurementDependence.Coordinates.Settings
