import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.GoldenResource.EightStepAbundancy
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.GoldenResource.EightStepAbundancy

open _root_.D5.S3.Arith.GoldenResource.EightStepAbundancy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p k => layerDenominator p k) (fun e => nomatch e)

theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, 0, 1, ?_⟩
  norm_num [actual, realize, layerDenominator]

abbrev monoArena : Arena where
  signature := signature
  Law R := ∀ p : ℕ, ∀ {a b : ℕ}, a ≤ b → R.readout () p a ≤ R.readout () p b

def monoRejected : Realization signature :=
  realize signature (fun _ _ k => if k = 0 then 1 else 0) (fun e => nomatch e)

theorem mono_rejected_law : ¬ monoArena.Law monoRejected := by
  intro h
  have hh := h 2 (a := 0) (b := 1) (by norm_num)
  norm_num [monoRejected, realize] at hh

abbrev posArena : Arena where
  signature := signature
  Law R := ∀ {p k : ℕ}, p.Prime → 1 ≤ k → 0 < R.readout () p k

def posRejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

theorem pos_rejected_law : ¬ posArena.Law posRejected := by
  intro h
  have hh := h (p := 2) (k := 1) (by norm_num) (by norm_num)
  norm_num [posRejected, realize] at hh

abbrev ratioArena : Arena where
  signature := signature
  Law R := ∀ {p k : ℕ}, p.Prime → 1 ≤ k →
    (1 - (p : ℝ)⁻¹ ^ (k + 1)) / (1 - (p : ℝ)⁻¹ ^ k) =
      1 + 1 / (R.readout () p k : ℝ)

def ratioRejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

theorem ratio_rejected_law : ¬ ratioArena.Law ratioRejected := by
  intro h
  have hh := h (p := 2) (k := 1) (by norm_num) (by norm_num)
  norm_num [ratioRejected, realize] at hh

def monoFamily : Registration monoArena (type_of% @denominator_mono) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨denominator_mono, monoRejected, mono_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨monoRejected, ?_, rfl, mono_rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def monoAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@denominator_mono) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.GoldenResource.EightStepAbundancy.denominator_mono.audit
  realizationName := `Reg.D5.S3.Arith.GoldenResource.EightStepAbundancy.monoFamily
  realizationSource := none
  generated := false
  arena := .source ⟨monoArena⟩
  objectArena := .source ⟨monoArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source monoArena ⟨monoFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.GoldenResource.EightStepAbundancy
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms monoFamily
#print axioms monoAudit

def posFamily : Registration posArena (type_of% @denominator_pos) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨denominator_pos, posRejected, pos_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨posRejected, ?_, rfl, pos_rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def posAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@denominator_pos) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.GoldenResource.EightStepAbundancy.denominator_pos.audit
  realizationName := `Reg.D5.S3.Arith.GoldenResource.EightStepAbundancy.posFamily
  realizationSource := none
  generated := false
  arena := .source ⟨posArena⟩
  objectArena := .source ⟨posArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source posArena ⟨posFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.GoldenResource.EightStepAbundancy
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms posFamily
#print axioms posAudit

def ratioFamily : Registration ratioArena (type_of% @layer_ratio_identity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨layer_ratio_identity, ratioRejected, ratio_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨ratioRejected, ?_, rfl, ratio_rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def ratioAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@layer_ratio_identity) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.GoldenResource.EightStepAbundancy.layer_ratio_identity.audit
  realizationName := `Reg.D5.S3.Arith.GoldenResource.EightStepAbundancy.ratioFamily
  realizationSource := none
  generated := false
  arena := .source ⟨ratioArena⟩
  objectArena := .source ⟨ratioArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source ratioArena ⟨ratioFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.GoldenResource.EightStepAbundancy
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms ratioFamily
#print axioms ratioAudit

end
end Reg.D5.S3.Arith.GoldenResource.EightStepAbundancy
