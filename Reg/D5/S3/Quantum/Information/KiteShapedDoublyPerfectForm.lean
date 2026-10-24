import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.KiteShapedDoublyPerfectForm
import Reg.Support.DependentFamily

/-! Source-bound audit of the residue criterion for binary kite forms. -/

namespace Reg.D5.S3.Quantum.Information.KiteShapedDoublyPerfectForm

open _root_.D5.S3.Quantum.Information.KiteShapedDoublyPerfectForm
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the size modulo three in the symplectic nondegeneracy criterion. -/
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
  realize signature (fun _ _ n => n % 3) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain symmetry, invertibility, and both complete nondegeneracy criteria. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ n : ℕ, 1 ≤ n →
    (kite n).IsSymm ∧
    (kite n).SeparatingRight ∧ (quadraticForm n).SeparatingRight ∧
    ((kite n * kite n - 1).SeparatingRight ↔ n % 3 ≠ 1) ∧
    ((quadraticForm n + Matrix.J (Fin n) (ZMod 2)).SeparatingRight ↔
      r.readout () () n ≠ 1)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hsep := (h 1 (by omega)).2.2.2.2.mpr (by decide)
  have hbad := (result 1 (by omega)).2.2.2.2.mp hsep
  norm_num at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change (0 : ℕ) % 3 ≠ 1 % 3
  norm_num

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
      (@_root_.D5.S3.Quantum.Information.KiteShapedDoublyPerfectForm.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.KiteShapedDoublyPerfectForm.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Information.KiteShapedDoublyPerfectForm.source_registration
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
    (realize signature (fun _ _ n => n % 3) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.KiteShapedDoublyPerfectForm
    definition := some {
      owner := `D5.S3.Quantum.Information.KiteShapedDoublyPerfectForm
      name := `D5.S3.Quantum.Information.KiteShapedDoublyPerfectForm.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "arg", "arg", "arg", "fn", "arg"]
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
end Reg.D5.S3.Quantum.Information.KiteShapedDoublyPerfectForm
