import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.WassersteinMean
import Reg.Support.DependentFamily

/-! Source-bound determinant comparison through the second matrix operand. -/

open _root_.D5.S3.Quantum.Matrix.WassersteinMean
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Matrix.WassersteinMean
noncomputable section

abbrev signature : Signature where
  Params := Σ n : ℕ, Matrix (Fin n) (Fin n) ℂ
  State p := Matrix (Fin p.1) (Fin p.1) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (Fin p.1) (Fin p.1) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ B => B) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- The complete matrix dimension and both matrix operands remain in the law. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ},
    weakLogMajorization A (R.readout () ⟨n, A⟩ B) → A.det.re ≤ B.det.re

private theorem one_majorizes_one :
    weakLogMajorization (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 := by
  exact ⟨Matrix.isHermitian_one, Matrix.isHermitian_one, fun _ _ => le_rfl⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have bad := law (n := 1) (A := 1) (B := 0) one_majorizes_one
  norm_num at bad

def evidence : Registration arena (type_of% (@weakLogMajorization_det_le)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨weakLogMajorization_det_le, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨⟨1, 1⟩, 1, 0, ?_⟩
    intro same
    have bad := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℂ => M 0 0) same
    change (1 : ℂ) = 0 at bad
    exact one_ne_zero bad

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.WassersteinMean.weakLogMajorization_det_le)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `D5.S3.Quantum.Matrix.WassersteinMean.weakLogMajorization_det_le.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.WassersteinMean.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.WassersteinMean
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "domain", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms evidence
#print axioms registration

end
end Reg.D5.S3.Quantum.Matrix.WassersteinMean
