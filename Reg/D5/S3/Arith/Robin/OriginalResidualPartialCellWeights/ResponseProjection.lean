/- Source-bound dependent-family registration for the original arithmetic owner.
Machine validation is supplied by the current scoped report, separately for each audit. -/

import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.OriginalResidualPartialCellWeights
import Reg.Support.DependentFamily

noncomputable section
set_option autoImplicit false
open scoped BigOperators Matrix
open _root_.D5.S3.Arith.Robin.OriginalResidualPartialCellWeights
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.Robin.OriginalResidualPartialCellWeights.ResponseProjection

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
  Law R := ∀ {N : ℕ}, 3 ≤ N →
    (gram N 0 0 = ∑ m ∈ Finset.Ico N (2 * N), w m ∧
      gram N 0 1 = ∑ m ∈ Finset.Ico N (2 * N), w m * ((m : ℝ) / N) ∧
      gram N 1 0 = gram N 0 1 ∧
      gram N 1 1 = ∑ m ∈ Finset.Ico N (2 * N), w m * ((m : ℝ) / N) ^ 2) ∧
    0 < R.readout () () N ∧
    (∀ a b : ℝ,
      (∑ m ∈ Finset.Ico N (2 * N), coeff N a b m) = 0 ∧
      (∑ m ∈ Finset.Ico N (2 * N), (m : ℝ) * coeff N a b m) = 0) ∧
    (∀ (a b : ℝ) (m : ℕ), m ∈ Finset.Ico N (2 * N) →
      coeff N a b m = Real.log (N : ℝ) * omega a b m - c N a b 0 * w m -
        c N a b 1 * (w m * ((m : ℝ) / N)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hfalse := (h (N := 3) (by norm_num)).2.1
  change (0 : ℝ) < 0 at hfalse
  exact (lt_irrefl (0 : ℝ)) hfalse

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 3, 4, ?_⟩
  change delta 3 ≠ delta 4
  norm_num [delta, gram, v, w, Finset.sum_Ico_succ_top]

def family : Registration arena (type_of% (@response_projection_interface)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@response_projection_interface, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@response_projection_interface) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.OriginalResidualPartialCellWeights.response_projection_interface.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalResidualPartialCellWeights.ResponseProjection.family
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
  -- UNVERIFIED static occurrence candidates; see audit/source-audit.json.
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.OriginalResidualPartialCellWeights
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Robin.OriginalResidualPartialCellWeights.ResponseProjection
