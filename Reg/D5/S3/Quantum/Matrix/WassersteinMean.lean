import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.WassersteinMean
import Reg.Support.DependentFamily

open _root_.D5.S3.Quantum.Matrix.WassersteinMean
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Matrix.WassersteinMean
noncomputable section
open Classical

abbrev signature : Signature where
  Params := Σ n : ℕ, Matrix (Fin n) (Fin n) ℂ
  State p := Matrix (Fin p.1) (Fin p.1) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p B => decide (weakLogMajorization p.2 B))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => true) (fun e => nomatch e)

/-- The complete matrix dimension and both matrix operands remain in the law. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ},
    R.readout () ⟨n, A⟩ B = true → A.det.re ≤ B.det.re

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have bad := law (n := 1) (A := 1) (B := 0) rfl
  norm_num at bad

private theorem one_majorizes_one :
    weakLogMajorization (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 := by
  exact ⟨Matrix.isHermitian_one, Matrix.isHermitian_one, fun _ _ => le_rfl⟩

private theorem not_one_majorizes_zero :
    ¬ weakLogMajorization (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 := by
  intro h
  have bad := weakLogMajorization_det_le h
  norm_num at bad

def evidence : Registration arena (type_of% (@weakLogMajorization_det_le)) where
  actual := actual
  bridge := by
    constructor
    · intro source n A B h
      exact source (of_decide_eq_true h)
    · intro law n A B h
      exact law (decide_eq_true h)
  variation := ⟨by
    intro n A B h
    exact weakLogMajorization_det_le (of_decide_eq_true h), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨⟨1, 1⟩, 1, 0, ?_⟩
    change decide (weakLogMajorization (1 : Matrix (Fin 1) (Fin 1) ℂ) 1) ≠
      decide (weakLogMajorization (1 : Matrix (Fin 1) (Fin 1) ℂ) 0)
    simp [one_majorizes_one, not_one_majorizes_zero]

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
      path := #["body", "body", "body", "domain"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms evidence
#print axioms registration

end
end Reg.D5.S3.Quantum.Matrix.WassersteinMean
