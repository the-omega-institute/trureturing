import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.OriginalResidualPartialCellWeights
import Reg.Support.DependentFamily

noncomputable section
set_option autoImplicit false
open scoped BigOperators Matrix
open Finset
open _root_.D5.S3.Arith.Robin.OriginalResidualPartialCellWeights
open _root_.D5.S3.Arith.Robin.ActualRobinClockCovariance (g activationDensity)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.Robin.OriginalResidualPartialCellWeights

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ N => delta N) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ} {a b : ℝ}, 3 ≤ N → (N : ℝ) < a → a < b → b < 2*N →
    (∀ m : ℕ, omega a b m = if max a (m : ℝ) < min b (m+1) then
      g (max a (m : ℝ))-g (min b (m+1)) else 0) ∧
    0 < R.readout () () N ∧
    c N a b = (gram N)⁻¹ *ᵥ rhs N a b ∧
    gram N *ᵥ c N a b = rhs N a b ∧
    (∑ m ∈ Ico N (2*N), coeff N a b m) = 0 ∧
    (∑ m ∈ Ico N (2*N), (m : ℝ)*coeff N a b m) = 0 ∧
    datum N a b (2*N) = 0 ∧ residual N a b (2*N) = 0 ∧ coeff N a b (2*N) = 0 ∧
    variation N (coeff N a b) ≤ 2*Real.log N*activationDensity a +
      2*(|c N a b 0|+|c N a b 1|)/((N : ℝ)*(N+1)) ∧
    2*Real.log N*activationDensity a + 2*(|c N a b 0|+|c N a b 1|)/((N : ℝ)*(N+1)) ≤
      2*Real.log N*activationDensity N + 2*(|c N a b 0|+|c N a b 1|)/((N : ℝ)*(N+1)) ∧
    mass N (coeff N a b) ≤ Real.log N*(g a-g b)+
      |c N a b 0|/(2*(N : ℝ))+|c N a b 1| * _root_.D5.S3.Arith.Robin.OriginalResidualPartialCellWeights.harmonic N/N

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (N := 3) (a := 13/4) (b := 15/4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact (lt_irrefl (0 : ℝ)) hh.2.1

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 3, 4, ?_⟩
  change delta 3 ≠ delta 4
  norm_num [delta, gram, v, w, Finset.sum_Ico_succ_top]

def family : Registration arena (type_of% (@or6_partialCell_variation)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@or6_partialCell_variation, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@or6_partialCell_variation)
    (type_of% (realize signature (fun _ _ N => delta N) (fun e => nomatch e)))
    Type Unit where
  unitName :=
    `D5.S3.Arith.Robin.OriginalResidualPartialCellWeights.or6_partialCell_variation.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalResidualPartialCellWeights.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ N => delta N) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.OriginalResidualPartialCellWeights
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

end Reg.D5.S3.Arith.Robin.OriginalResidualPartialCellWeights
