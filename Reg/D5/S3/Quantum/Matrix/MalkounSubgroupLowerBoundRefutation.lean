import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.MalkounSubgroupLowerBoundRefutation
import Reg.Support.DependentFamily

/-! Source-bound audit of the real diagonal-product bridge. -/

open scoped BigOperators
open _root_.D5.S3.Quantum.Matrix.MalkounSubgroupLowerBoundRefutation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Matrix.MalkounSubgroupLowerBoundRefutation

noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State n := Matrix (Fin n) (Fin n) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ H => ∏ i, H i i) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (_hH : H.IsHermitian),
    R.readout () n H = ((∏ i, (H i i).re : ℝ) : ℂ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := h (n := 1) 1 Matrix.isHermitian_one
  norm_num [rejected, realize] at bad

def evidence : Registration arena (type_of% (@diagonal_product_eq_real)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@diagonal_product_eq_real, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨1, (fun _ _ => (0 : ℂ)), (fun _ _ => (1 : ℂ)), ?_⟩
    norm_num [actual, realize]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.MalkounSubgroupLowerBoundRefutation.diagonal_product_eq_real)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `D5.S3.Quantum.Matrix.MalkounSubgroupLowerBoundRefutation.diagonal_product_eq_real.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.MalkounSubgroupLowerBoundRefutation.evidence
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
    owner := `D5.S3.Quantum.Matrix.MalkounSubgroupLowerBoundRefutation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Quantum.Matrix.MalkounSubgroupLowerBoundRefutation
