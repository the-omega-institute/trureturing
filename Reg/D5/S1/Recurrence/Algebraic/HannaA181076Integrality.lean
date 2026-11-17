import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S1.Recurrence.Algebraic.HannaA181076Integrality

namespace Reg.D5.S1.Recurrence.Algebraic.HannaA181076Integrality

open LeanInformationAudit PowerSeries
open _root_.D5.S1.Recurrence.Algebraic.HannaA181076Integrality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State _ := PowerSeries ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ m S => coeff m S) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 / 2 : ℚ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ m : ℕ, ∃ z : ℤ, r.readout () m A = (z : ℚ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨z, hz⟩ := h 0
  change (1 / 2 : ℚ) = (z : ℚ) at hz
  have hq : (0 : ℚ) < (z : ℚ) ∧ (z : ℚ) < 1 := by
    constructor <;> linarith
  have hi : (0 : ℤ) < z ∧ z < 1 := by exact_mod_cast hq
  omega

def family : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨0, C (0 : ℚ), C (1 : ℚ), ?_⟩
    simp [actual, realize]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    result (Realization signature) Type Unit where
  unitName := `Reg.D5.S1.Recurrence.Algebraic.HannaA181076Integrality.auditUnit
  realizationName := `Reg.D5.S1.Recurrence.Algebraic.HannaA181076Integrality.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ m S => coeff m S) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Algebraic.HannaA181076Integrality
    definition := some {
      owner := `D5.S1.Recurrence.Algebraic.HannaA181076Integrality
      name := `D5.S1.Recurrence.Algebraic.HannaA181076Integrality.claim
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S1.Recurrence.Algebraic.HannaA181076Integrality
