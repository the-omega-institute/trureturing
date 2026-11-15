import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Approximate.WeylStarCorrector
import Reg.D5.S3.Quantum.Approximate.FiniteStarNewton

/-! Full-telescope real comparison for full-matrix star correction. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Approximate LeanInformationAudit
open _root_.D5.S3.Quantum.Approximate.WeylStarCorrector
open Reg.D5.S3.Quantum.Approximate.FiniteStarNewton
open scoped Matrix.Norms.L2Operator

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

namespace Reg.D5.S3.Quantum.Approximate.WeylStarCorrector

def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) [NeZero n] {A : Type u} [CStarAlgebra A],
    ∀ (f : Matrix (Fin n) (Fin n) ℂ →L[ℂ] A) {d : ℝ}
    (_hd : 0 ≤ d) (_hd' : d ≤ 1 / 32) (_hs : PreservesStar f)
    (_hg : DefectBound f d) (_hu : ‖f 1 - 1‖ ≤ 1 / 4),
    ∃ ρ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ] A,
      ∀ X, R.readout () () ‖ρ X - f X‖ ((8 * d / 3) * ‖X‖)

private theorem actual_law : arena.{u}.Law actual := @exists_matrix_star_hom_close.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let A := PUnit.{u+1} →L[ℂ] PUnit.{u+1}
  have hA : (1 : A) = 0 := Subsingleton.elim _ _
  obtain ⟨ρ, hρ⟩ := h 1 (A := A) (0 : Matrix (Fin 1) (Fin 1) ℂ →L[ℂ] A)
    (d := 0) le_rfl (by norm_num) (by intro x; simp)
    (by intro x y; simp [defect]) (by simp [hA])
  exact hρ 0

def family : Registration arena.{u} (type_of% (@exists_matrix_star_hom_close.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hb : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) le_rfl
    norm_num at hb

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_matrix_star_hom_close.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Approximate.WeylStarCorrector.matrixUnit
  realizationName := `Reg.D5.S3.Quantum.Approximate.WeylStarCorrector.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a b => a ≤ b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Approximate.WeylStarCorrector
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Approximate.WeylStarCorrector
