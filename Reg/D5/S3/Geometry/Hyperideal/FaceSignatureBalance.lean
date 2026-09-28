import D5.S3.Geometry.Hyperideal.FaceSignatureBalance
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Geometry.Hyperideal.FaceSignatureBalance

open _root_.D5.S3.Geometry.Hyperideal.FaceSignatureBalance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := Fin 6 → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fin 4 → ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ low => faceLowCount low) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ low : Fin 6 → Bool,
    (∀ i j : Fin 4, R.readout () () low i = R.readout () () low j) ↔
      low 0 = low 3 ∧ low 1 = low 4 ∧ low 2 = low 5

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let low : Fin 6 → Bool := fun i => decide (i = 0)
  have bad := (h low).mp (by simp [rejected, realize])
  have hneq : low 0 ≠ low 3 := by decide
  exact hneq bad.1

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ => false), (fun e => decide (e = 0)), ?_⟩
  intro h
  have point := congrFun h 2
  have hzero : (actual.readout i () (fun _ => false)) 2 = 0 := by
    cases i
    decide
  have hone : (actual.readout i () (fun e => decide (e = 0))) 2 = 1 := by
    cases i
    decide
  rw [hzero, hone] at point
  norm_num at point

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨equal_face_counts_iff_opposite_balance, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := dependence

register_information_theorem equal_face_counts_iff_opposite_balance in arena
  readout via (realize signature (fun _ _ low => faceLowCount low) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Geometry.Hyperideal.FaceSignatureBalance
    coordinates := #[]
    readouts := #[{ path := #["body", "fn", "arg", "body", "body",
      "fn", "arg", "fn"], stateBinder := 0 }] })
  escape continues (open)

open Lean in
run_meta do
  let env ← getEnv
  let sourceName : Lean.Name :=
    `D5.S3.Geometry.Hyperideal.FaceSignatureBalance.equal_face_counts_iff_opposite_balance
  let some row := TemplateBinding.records env |>.find? (fun row =>
      row.occurrence.key.theoremName == sourceName &&
      row.occurrence.key.registrationModule == env.header.mainModule)
    | throwError "Face-signature registration evidence is missing"
  match row.result with
  | .declaredValidated certificate =>
      unless row.escape.fromObject.isSome &&
          row.escape.continuation.any (fun continuation => continuation.kind == "open") &&
          row.escape.bridgeKind == "source-equivalence" &&
          certificate.sourceBinding.isSome do
        throwError "Face-signature registration lacks validated source-bound evidence"
  | .declaredUnresolved diagnostic =>
      throwError "Face-signature registration is unresolved: {diagnostic}"
  | .undeclared =>
      throwError "Face-signature registration is undeclared"

#print axioms registration

end Reg.D5.S3.Geometry.Hyperideal.FaceSignatureBalance
