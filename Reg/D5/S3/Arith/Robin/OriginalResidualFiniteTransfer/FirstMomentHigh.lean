import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.OriginalResidualFiniteTransfer
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.FirstMomentHigh

open _root_.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset

noncomputable section

namespace WeightedFloorPrefix

abbrev signature : Signature where
  Params := Σ _ : ℕ, ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p m => ∑ k ∈ Ico p.1 (p.2 + 1), (k : ℝ) *
    (((m / k : ℕ) : ℝ) - ((m / (k + 1) : ℕ) : ℝ))) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p m =>
    (m : ℝ) * (1 + Real.log ((p.2 : ℝ) / p.1)) - p.2 + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {h j m : ℕ}, 0 < h → h ≤ j → j < m →
    R.readout () ⟨h,j⟩ m ≤ (m : ℝ) * (1 + Real.log ((j : ℝ) / h)) - j

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (h := 1) (j := 1) (m := 2) (by norm_num) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at he

def registration : Registration arena (type_of% @weighted_floor_prefix_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨weighted_floor_prefix_bound, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨1,1⟩, 2, 3, ?_⟩
    have hi : Ico 1 2 = {1} := by decide
    norm_num [actual, realize, hi]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@weighted_floor_prefix_bound) (Realization signature) Type Unit where
  unitName := `OriginalResidualFiniteTransfer.weighted_floor_prefix_bound.audit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.FirstMomentHigh.WeightedFloorPrefix.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p m => ∑ k ∈ Ico p.1 (p.2 + 1), (k : ℝ) *
    (((m / k : ℕ) : ℝ) - ((m / (k + 1) : ℕ) : ℝ))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.OriginalResidualFiniteTransfer
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms audit

end WeightedFloorPrefix

namespace FirstMomentVariation

abbrev signature : Signature where
  Params := Σ _ : ℕ, ℕ
  State _ := ℕ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p a => weightedVariation p.1 p.2 a) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p a => firstAbsoluteMoment p.1 a *
    (Real.log ((p.1 : ℝ) / p.2) + Real.log ((p.1 : ℝ) / p.2) ^ 2 / 2) + 1)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N h : ℕ}, 0 < h → h ≤ N → ∀ (a : ℕ → ℝ),
    (∑ m ∈ Ico N (2 * N), (m : ℝ) * a m) = 0 →
    R.readout () ⟨N,h⟩ a ≤ firstAbsoluteMoment N a *
      (Real.log ((N : ℝ) / h) + Real.log ((N : ℝ) / h) ^ 2 / 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (N := 1) (h := 1) (by norm_num) (by norm_num)
    (fun _ => 0) (by simp)
  norm_num [rejected, realize] at he

def registration : Registration arena (type_of% @weightedVariation_firstMoment_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨weightedVariation_firstMoment_bound, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨2,1⟩, (fun _ => 0), (fun m => if m = 2 then 1 else 0), ?_⟩
    have hi : Ico 1 2 = {1} := by decide
    have hm : Ico 2 4 = {2,3} := by decide
    have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    norm_num [actual, realize, weightedVariation, logDifference, logPair, floorPair,
      hi, hm, abs_mul, abs_of_pos hl]
    linarith

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@weightedVariation_firstMoment_bound) (Realization signature) Type Unit where
  unitName := `OriginalResidualFiniteTransfer.weightedVariation_firstMoment_bound.audit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.FirstMomentHigh.FirstMomentVariation.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p a => weightedVariation p.1 p.2 a)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.OriginalResidualFiniteTransfer
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms audit

end FirstMomentVariation

end
end Reg.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.FirstMomentHigh
