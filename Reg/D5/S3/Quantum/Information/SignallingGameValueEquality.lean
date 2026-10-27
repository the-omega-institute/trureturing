import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.SignallingGameValueEquality
import Reg.Support.DependentFamily

/-! Source-bound audit of the attained no-signalling value in the uniform signalling game. -/

namespace Reg.D5.S3.Quantum.Information.SignallingGameValueEquality

open _root_.D5.S3.Quantum.Information.SignallingGameValueEquality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the sharp value as Bob's question count varies, with Alice's count fixed. -/
abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ m n => 1 / (max (m : ℝ) (n : ℝ))) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- Retain both nonemptiness hypotheses and the three attained greatest-value assertions. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
    IsGreatest (noSignallingValues m n) (r.readout () m n) ∧
    IsGreatest (quantumValues m n) (1 / (max m n : ℝ)) ∧
    IsGreatest (classicalValues m n) (1 / (max m n : ℝ))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h 2 2 (by norm_num) (by norm_num)).1.unique
    (result 2 2 (by norm_num) (by norm_num)).1
  change (1 : ℝ) = 1 / (max (2 : ℝ) 2) at hbad
  norm_num at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 1, 2, ?_⟩
  norm_num [actual, realize]

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Information.SignallingGameValueEquality.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.SignallingGameValueEquality.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Information.SignallingGameValueEquality.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ m n => 1 / (max (m : ℝ) (n : ℝ))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.SignallingGameValueEquality
    definition := some {
      owner := `D5.S3.Quantum.Information.SignallingGameValueEquality
      name := `D5.S3.Quantum.Information.SignallingGameValueEquality.claim
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Information.SignallingGameValueEquality
