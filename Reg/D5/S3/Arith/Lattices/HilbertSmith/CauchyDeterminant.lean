import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Lattices.HilbertSmith.CauchyDeterminant
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift

/-! The determinant observes the full Cauchy matrix in each field and dimension. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.Lattices.HilbertSmith.CauchyDeterminant

open _root_.D5.S3.Arith.Lattices.HilbertSmith.CauchyDeterminant
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
universe u

abbrev signature : Signature where
  Params := Σ K : Type u, Σ _ : Field K, ℕ
  State p := Matrix (Fin p.2.2) (Fin p.2.2) p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p M => letI := p.2.1; M.det) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ p _ => letI := p.2.1; 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {K : Type u} [field : Field K] {k : ℕ} (x y : Fin k → K)
    (_hs : ∀ i j, x i + y j ≠ 0),
    R.readout () ⟨K, field, k⟩ (cauchyMatrix x y) =
      orderedDifferences x * orderedDifferences y / cauchyDenominator x y

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hzero := @h (ULift.{u} ℚ) inferInstance 0
    (fun _ => 0) (fun _ => 0) (fun i => Fin.elim0 i)
  simpa [rejected, realize, orderedDifferences, cauchyDenominator] using hzero

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  refine ⟨⟨ULift.{u} ℚ, inferInstance, 1⟩, 0, 1, ?_⟩
  change (0 : Matrix (Fin 1) (Fin 1) (ULift.{u} ℚ)).det ≠
    (1 : Matrix (Fin 1) (Fin 1) (ULift.{u} ℚ)).det
  rw [Matrix.det_zero, Matrix.det_one]
  exact zero_ne_one

def family : Registration arena.{u} (type_of% @det_cauchyMatrix.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨det_cauchyMatrix, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@det_cauchyMatrix.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `D5.S3.Arith.Lattices.HilbertSmith.CauchyDeterminant.det_cauchyMatrix.__information_unit
  realizationName := `Reg.D5.S3.Arith.Lattices.HilbertSmith.CauchyDeterminant.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ p M => letI := p.2.1; M.det) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Lattices.HilbertSmith.CauchyDeterminant
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Arith.Lattices.HilbertSmith.CauchyDeterminant
