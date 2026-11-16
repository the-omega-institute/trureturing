import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.SharpWeightedLin.Settlement
import Reg.Support.DependentFamily

open LeanInformationAudit Matrix
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Matrix.SharpWeightedLin
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
namespace Reg.D5.S3.Quantum.Matrix.SharpWeightedLin.Settlement

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
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private def rPositive {n : ℕ} (α p : ℝ) (A B : Matrix (Fin n) (Fin n) ℂ) :
    (hiaiRMean α p A B).PosSemidef := CFC.rpow_nonneg.posSemidef
private def aPositive {n : ℕ} (α q : ℝ) (A B : Matrix (Fin n) (Fin n) ℂ) :
    (hiaiArithmeticMean α q A B).PosSemidef := CFC.rpow_nonneg.posSemidef

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {α p q : ℝ},
    0 < α → α < 1 → 0 < p → α * (1 - α) * p ≤ q →
    ∀ (A B : Matrix (Fin n) (Fin n) ℂ), A.PosDef → B.PosDef →
    ∀ j : Fin (Fintype.card (Fin n)),
    R.readout () () ((rPositive α p A B).isHermitian.eigenvalues₀ j)
      ((aPositive α q A B).isHermitian.eigenvalues₀ j)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (n := 1) (α := 1/2) (p := 1) (q := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    1 1 Matrix.PosDef.one Matrix.PosDef.one 0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := congrFun h 0
  norm_num [actual, realize] at hh

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.SharpWeightedLin.result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.SharpWeightedLin.result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.SharpWeightedLin.result) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.SharpWeightedLin.result.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.SharpWeightedLin.Settlement.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.SharpWeightedLin.Settlement
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Matrix.SharpWeightedLin.Settlement
