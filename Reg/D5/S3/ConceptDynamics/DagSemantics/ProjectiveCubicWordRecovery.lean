import D5.S3.ConceptDynamics.DagSemantics.ProjectiveCubicWordRecovery
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false

namespace Reg.D5.S3.ConceptDynamics.DagSemantics.ProjectiveCubicWordRecovery

open _root_.D5.S3.ConceptDynamics.DagSemantics.ProjectiveCubicWordRecovery
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

private abbrev Params := Σ n : ℕ, Σ _ : Fin (n+1), Fin (n+1)
private abbrev Word (q : Params) := Fin (q.1+1) → ZMod 3

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Params Word (fun _ => Bool)

def actual : Realization signature :=
  realize signature (fun _ q b => pairRead b q.2.1 q.2.2)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ q b => !(pairRead b q.2.1 q.2.2))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (a b : Fin (n+1) → ZMod 3),
    (∀ (i j : Fin (n+1)), i.val < j.val → j.val ≤ i.val+2 →
      pairRead a i j = R.readout () ⟨n,i,j⟩ b) ↔
      ∃ s : Fin n → ZMod 3, (∀ i, s i = 1 ∨ s i = -1) ∧
        (∀ i, derivative b i = s i * derivative a i) ∧
        ∀ ⦃i j⦄, Relation.ReflTransGen (Active (derivative a) next) i j → s i = s j

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have rh := (h 1 (fun _ => 0) (fun _ => 0)).mpr
    ⟨fun _ => 1, fun _ => Or.inl rfl, fun _ => by simp, by intros; rfl⟩
  have hf := rh 0 1 (by decide) (by decide)
  change (true : Bool) = false at hf
  contradiction

private theorem actual_dependence :
    actual.readout () ⟨1,0,1⟩ (fun _ => 0) ≠
      actual.readout () ⟨1,0,1⟩ (fun i => if i=0 then 0 else 1) := by
  change (true : Bool) ≠ false
  decide

def family : Registration arena (type_of% @projective_cubic_word_recovery) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@projective_cubic_word_recovery,rejected,rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := fun _ => ⟨⟨1,0,1⟩,fun _ => 0,fun i => if i=0 then 0 else 1,actual_dependence⟩

/-- Select the actual ternary equality readout at the second word. -/
def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@projective_cubic_word_recovery) (type_of% actual) Unit Unit where
  unitName := `D5.S3.ConceptDynamics.DagSemantics.ProjectiveCubicWordRecovery.projective_cubic_word_recovery.__information_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.DagSemantics.ProjectiveCubicWordRecovery.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.DagSemantics.ProjectiveCubicWordRecovery
    definition := none
    coordinates := #[0,3,4]
    readouts := #[{
      path := #["body","body","body","fn","arg","body","body","body","body","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn","fn","arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end
end Reg.D5.S3.ConceptDynamics.DagSemantics.ProjectiveCubicWordRecovery
