import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Classification
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.longLine false

noncomputable section

namespace Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Classification

open _root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix Module

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m₁ n₁ m₂ n₂ : ℕ}
    (A₁ A₂ : Matrix (Fin m₁) (Fin n₁) ℂ)
    (B₁ B₂ : Matrix (Fin m₂) (Fin n₂) ℂ)
    (hA : LinearIndependent ℂ ![A₁, A₂])
    (hB : LinearIndependent ℂ ![B₁, B₂]),
    R.readout () () (partialTranspose A₁ A₂ B₁ B₂).rank
      (2 * (tensorSum A₁ A₂ B₁ B₂).rank) ↔
      (vRank A₁ A₂ = 2 * hRank A₁ A₂ ∧ vRank B₁ B₂ = 2 * hRank B₁ B₂) ∨
      (hRank A₁ A₂ = 2 * vRank A₁ A₂ ∧ hRank B₁ B₂ = 2 * vRank B₁ B₂)

private def rowOne : Matrix (Fin 1) (Fin 2) ℂ := ![![1, 0]]
private def rowTwo : Matrix (Fin 1) (Fin 2) ℂ := ![![0, 1]]

private theorem rows_independent : LinearIndependent ℂ ![rowOne, rowTwo] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h₀ := congrFun (congrFun hc 0) 0
  have h₁ := congrFun (congrFun hc 0) 1
  simp [Fin.sum_univ_two, rowOne, rowTwo, Matrix.smul_apply] at h₀ h₁
  intro i
  fin_cases i <;> assumption

private theorem rows_vertical : vRank rowOne rowTwo = 2 * hRank rowOne rowTwo := by
  apply (joint_control_iff rowOne rowTwo).2
  intro y₁ _ y₂ _
  refine ⟨![y₁ 0, y₂ 0], ?_, ?_⟩ <;> ext i <;> fin_cases i <;>
    simp [rowOne, rowTwo, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h rowOne rowTwo rowOne rowTwo rows_independent rows_independent).mpr
    (Or.inl ⟨rows_vertical, rows_vertical⟩)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h : (1 : ℕ) = 0 := Eq.mp (congrFun he 0) rfl
  omega

def source_registration : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.result)
      (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.result.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Classification.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Classification
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Classification
