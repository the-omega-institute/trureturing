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

namespace EnergyBound

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
  realize signature (fun _ _ N =>
    (1 + 1 / Real.log (N : ℝ)) ^ 2 / (8 * (N : ℝ))) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ} {a b : ℝ}, 3 ≤ N → (N : ℝ) ≤ a → a ≤ b →
    (∑ m ∈ Ico N (2 * N), (coeff N a b m) ^ 2 / w m) ≤
      R.readout () () N

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (N := 3) (a := 3) (b := 3)
    (by norm_num) (by norm_num) (by norm_num)
  change (∑ m ∈ Ico 3 (2 * 3), (coeff 3 3 3 m) ^ 2 / w m) ≤ -1 at he
  have hn : 0 ≤ ∑ m ∈ Ico 3 (2 * 3), (coeff 3 3 3 m) ^ 2 / w m := by
    apply Finset.sum_nonneg
    intro m _
    exact div_nonneg (sq_nonneg _) (by unfold w; positivity)
  linarith

def family : Registration arena (type_of% (@or6_partialCell_energy_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@or6_partialCell_energy_bound, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 3, 4, ?_⟩
    change (1 + 1 / Real.log (3 : ℝ)) ^ 2 / (8 * (3 : ℝ)) ≠
      (1 + 1 / Real.log (4 : ℝ)) ^ 2 / (8 * (4 : ℝ))
    have h3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
    have h4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
    have hlog : Real.log (3 : ℝ) ≤ Real.log (4 : ℝ) :=
      Real.log_le_log (by norm_num) (by norm_num)
    have hinv : 1 / Real.log (4 : ℝ) ≤ 1 / Real.log (3 : ℝ) :=
      one_div_le_one_div_of_le h3 hlog
    have hpos : 0 < 1 + 1 / Real.log (4 : ℝ) := by positivity
    have hs : (1 + 1 / Real.log (4 : ℝ)) ^ 2 ≤
        (1 + 1 / Real.log (3 : ℝ)) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hinv)
        (show 0 ≤ (1 + 1 / Real.log (4 : ℝ)) +
          (1 + 1 / Real.log (3 : ℝ)) by positivity)]
    apply ne_of_gt
    apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 8 * 4)
      (by norm_num : (0 : ℝ) < 8 * 3)).mpr
    nlinarith [sq_pos_of_pos hpos]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@or6_partialCell_energy_bound) (Realization signature) Type Unit where
  unitName := `OriginalResidualPartialCellWeights.or6_partialCell_energy_bound.audit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalResidualPartialCellWeights.EnergyBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ N =>
    (1 + 1 / Real.log (N : ℝ)) ^ 2 / (8 * (N : ℝ))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.OriginalResidualPartialCellWeights
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end EnergyBound

end Reg.D5.S3.Arith.Robin.OriginalResidualPartialCellWeights
