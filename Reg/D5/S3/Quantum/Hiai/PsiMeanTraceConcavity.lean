import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Hiai.PsiMeanTraceConcavity

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Hiai.PsiMeanTraceConcavity
open LeanInformationAudit Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace Reg.D5.S3.Quantum.Hiai.PsiMeanTraceConcavity
universe u
noncomputable section
open Classical

abbrev signature : Signature where
  Params := Type u
  State d := Matrix d d ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ A ↦ decide A.PosDef) (fun e ↦ nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ ↦ true) (fun e ↦ nomatch e)

/-- All original finite index types, typeclass premises and real exponents remain in the law. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {d : Type u} [Fintype d] [DecidableEq d] {A B : Matrix d d ℂ},
    R.readout () d A = true → B.PosDef → ∀ θ : ℝ,
      IsStrictlyPositive (geometricMean θ B A)

private theorem zero_not_posDef :
    ¬ (0 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ).PosDef := by
  intro h
  have h0 := h.diag_pos (i := ⟨()⟩)
  simpa using h0

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro law
  have bad := law (d := ULift.{u} Unit) (A := 0) (B := 1) rfl Matrix.PosDef.one 1
  have hz : geometricMean 1 (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) 0 = 0 := by
    simp [geometricMean, CFC.rpow_one]
  rw [hz] at bad
  exact zero_not_posDef bad.posDef

def evidence : Registration arena.{u} (type_of% (@mean_strict.{u})) where
  actual := actual
  bridge := by
    constructor
    · intro source d _ _ A B hA hB θ
      exact source (of_decide_eq_true hA) hB θ
    · intro law d _ _ A B hA hB θ
      exact law (decide_eq_true hA) hB θ
  variation := ⟨by
    intro d _ _ A B hA hB θ
    exact mean_strict (of_decide_eq_true hA) hB θ, rejected, rejected_law⟩
  sensitivity := ⟨fun i ↦ ⟨rejected,
    fun j hj ↦ (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun i ↦ nomatch i⟩
  dependence := by
    intro i
    refine ⟨ULift.{u} Unit, 0, 1, ?_⟩
    change decide (0 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ).PosDef ≠
      decide (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ).PosDef
    simp [zero_not_posDef, Matrix.PosDef.one]

noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Hiai.PsiMeanTraceConcavity.mean_strict.{u})
      (type_of% (realize signature.{u} actual.readout actual.anchor)) Unit Unit := {
  unitName := `D5.S3.Quantum.Hiai.PsiMeanTraceConcavity.mean_strict.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Hiai.PsiMeanTraceConcavity.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Hiai.PsiMeanTraceConcavity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "domain"]
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
end Reg.D5.S3.Quantum.Hiai.PsiMeanTraceConcavity
