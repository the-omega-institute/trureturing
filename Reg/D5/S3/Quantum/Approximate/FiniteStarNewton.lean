import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Approximate.FiniteStarNewton
import Mathlib.Analysis.CStarAlgebra.Matrix
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Approximate LeanInformationAudit
open scoped BigOperators TensorProduct Matrix.Norms.L2Operator

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v w

namespace Reg.D5.S3.Quantum.Approximate.FiniteStarNewton

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ a b => a ≤ b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {B : Type u} {A : Type v} {J : Type w}
    [CStarAlgebra B] [CStarAlgebra A] [Fintype J] [NormOneClass B],
    ∀ (D : FiniteDiagonal B J) (f : B →L[ℂ] A) {d : ℝ}
    (_hd : 0 ≤ d) (_hd' : d ≤ 1 / 32) (_hs : PreservesStar f)
    (_hg : DefectBound f d) (_hu : ‖f 1 - 1‖ ≤ 1 / 4),
    ∃ ρ : B →⋆ₐ[ℂ] A, ∀ x, R.readout () () ‖ρ x - f x‖ ((8 * d / 3) * ‖x‖)

private theorem actual_law : arena.{u,v,w}.Law actual := @exists_star_hom_close.{u,v,w}

private def scalarDiagonal :
    FiniteDiagonal (Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) (ULift.{w} Unit) where
  left _ := 1
  right _ := 1
  product := by simp
  central X := by
    simp only [mul_one, one_mul]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_ulift, Fintype.card_unit,
      one_smul]
    have hx : X = X ⟨()⟩ ⟨()⟩ • (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) := by
      ext i j
      have hi : i = ⟨()⟩ := Subsingleton.elim _ _
      have hj : j = ⟨()⟩ := Subsingleton.elim _ _
      simp [hi, hj]
    rw [hx]
    simp only [TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  budget := by simp

private theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  let A := PUnit.{v+1} →L[ℂ] PUnit.{v+1}
  have hA : (1 : A) = 0 := Subsingleton.elim _ _
  obtain ⟨ρ, hρ⟩ := h (A := A) scalarDiagonal (0 :
    Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ →L[ℂ] A)
    (d := 0) le_rfl (by norm_num)
    (by intro x; simp)
    (by intro x y; simp [defect])
    (by simp [hA])
  exact hρ 0

def family : Registration arena.{u,v,w} (type_of% (@exists_star_hom_close.{u,v,w})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (show j = i from Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hb : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) le_rfl
    norm_num at hb

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_star_hom_close.{u,v,w}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Approximate.FiniteStarNewton.correctorUnit
  realizationName := `Reg.D5.S3.Quantum.Approximate.FiniteStarNewton.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w}⟩
  objectArena := .source ⟨arena.{u,v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w} ⟨family.{u,v,w}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a b => a ≤ b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Approximate.FiniteStarNewton
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "arg", "body", "body",
        "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Approximate.FiniteStarNewton
