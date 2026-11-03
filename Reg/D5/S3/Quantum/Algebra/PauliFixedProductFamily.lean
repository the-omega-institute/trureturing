import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Algebra.PauliFixedProductFamily
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily

noncomputable section
namespace Reg.D5.S3.Quantum.Algebra.PauliFixedProductFamily

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ t => reportSquared t) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law A := ∀ t : ℝ, A.readout () () t=288*t^2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0
  norm_num [rejected,realize] at hh

def family : Registration arena (type_of% (@full_report)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨full_report,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(),0,1,?_⟩
    simp [actual,realize,full_report]

noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@full_report) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Algebra.PauliFixedProductFamily.full_report.information_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.PauliFixedProductFamily.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ t => reportSquared t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.PauliFixedProductFamily
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","fn","arg","fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration
end Reg.D5.S3.Quantum.Algebra.PauliFixedProductFamily
