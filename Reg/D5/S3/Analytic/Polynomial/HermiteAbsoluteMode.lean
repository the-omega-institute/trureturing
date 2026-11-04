import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Polynomial.HermiteAbsoluteMode
import Reg.Support.DependentFamily

/-! Source-family audit of the absolute Hermite mode transition. -/

namespace Reg.D5.S3.Analytic.Polynomial.HermiteAbsoluteMode
open _root_.D5.S3.Analytic.Polynomial.HermiteAbsoluteMode
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => b n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r :=
    (∀ n, IsSmallestAbsMax n (r.readout () () n)) ∧
    ∀ n : ℕ, (r.readout () () (n + 1) : ℤ) - (r.readout () () n : ℤ) = 1 ∨
      (r.readout () () (n + 1) : ℤ) - (r.readout () () n : ℤ) = -1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h.2 0
  change (0 : ℤ) - 0 = 1 ∨ (0 : ℤ) - 0 = -1 at hh
  omega

def source_registration : Registration arena claim where
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
    refine ⟨(), 0, 1, ?_⟩
    change b 0 ≠ b 1
    intro he
    have hstep := result.2 0
    change (b 1 : ℤ) - (b 0 : ℤ) = 1 ∨ (b 1 : ℤ) - (b 0 : ℤ) = -1 at hstep
    rw [← he] at hstep
    omega

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      (@result) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Polynomial.HermiteAbsoluteMode.unit
  realizationName := `Reg.D5.S3.Analytic.Polynomial.HermiteAbsoluteMode.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => b n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Polynomial.HermiteAbsoluteMode
    definition := some {
      owner := `D5.S3.Analytic.Polynomial.HermiteAbsoluteMode
      name := `D5.S3.Analytic.Polynomial.HermiteAbsoluteMode.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Analytic.Polynomial.HermiteAbsoluteMode
