import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuadraticForms.SerreG2MatrixTable
import Reg.Support.DependentFamily
import Mathlib.Tactic.NormNum

/-! Source-bound registration of the checked integral G2 bracket identities. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.QuadraticForms.SerreG2MatrixTable

open _root_.D5.S3.QuadraticForms.SerreG2MatrixTable
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
attribute [local instance 100] LieRing.ofAssociativeRing

abbrev signature : Signature where
  Params := Fin 14
  State _ := Fin 14
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Matrix (Fin 7) (Fin 7) ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ i j => ⁅basisMatrix i, basisMatrix j⁆) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ i j, R.readout () i j = ∑ t, coefficients i j t • basisMatrix t

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := congrArg (fun M : Matrix (Fin 7) (Fin 7) ℤ => M 0 0) (h 0 0)
  have hzero : (∑ t, coefficients (0 : Fin 14) 0 t • basisMatrix t) = 0 := by
    simp [coefficients, Fin.sum_univ_succ]
  change (1 : Matrix (Fin 7) (Fin 7) ℤ) 0 0 = _ at hh
  rw [hzero] at hh
  norm_num [Matrix.one_apply] at hh

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 2, ?_⟩
  intro h
  have hh := congrArg (fun M : Matrix (Fin 7) (Fin 7) ℤ => M 0 1) h
  norm_num [actual, realize, basisMatrix, Ring.lie_def,
    Matrix.mul_apply, Fin.sum_univ_succ] at hh

def source_registration : Registration arena
    (type_of% @_root_.D5.S3.QuadraticForms.SerreG2MatrixTable.bracket) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.QuadraticForms.SerreG2MatrixTable.bracket, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := dependence

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.QuadraticForms.SerreG2MatrixTable.bracket)
      (Realization signature) Type Unit := {
  unitName := `Reg.D5.S3.QuadraticForms.SerreG2MatrixTable.unit
  realizationName := `Reg.D5.S3.QuadraticForms.SerreG2MatrixTable.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ i j => ⁅basisMatrix i, basisMatrix j⁆)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (Fin 14)
  sourceSelection := some {
    owner := `D5.S3.QuadraticForms.SerreG2MatrixTable
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }


end Reg.D5.S3.QuadraticForms.SerreG2MatrixTable
