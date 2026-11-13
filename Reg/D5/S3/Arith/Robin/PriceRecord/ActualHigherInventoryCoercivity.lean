import D5.S3.Arith.Robin.PriceRecord.ActualHigherInventoryCoercivity
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The higher-inventory readout keeps every real scale and natural state.
The law retains the original telescope, local defect and both conclusion clauses. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Arith.Robin.PriceRecord.ActualHigherInventoryCoercivity

open Real Finset
open _root_.D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
open _root_.D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask
open _root_.D5.S3.Arith.Robin.ActualTwoPriceDefect
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual
open _root_.D5.S3.Arith.Robin.PriceRecord.CompleteHigherInventoryDuality
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualHigherInventoryCoercivity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

/-- Finite roles and anchors retain all real scales and natural states. -/
abbrev signature : Signature where
  Params := ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ X n => higherInventoryMismatch X n) (fun e => nomatch e)

/-- The complete telescope, local let and both conclusion clauses are unchanged. -/
abbrev arena : Arena where
  signature := signature
  Law W := ∀ {X : ℝ} (hX : exp 2 ≤ X) (n : ℕ) (hn : 1 ≤ n),
    let R := actualDefect X n - completeFirstLayerLoss X n
    0 ≤ R ∧
    W.readout () X n ≤
      1000 * (X ^ (3 / 4 : ℝ) * log X * sqrt R + X * log X * R + log X ^ 2)

private theorem source_bridge :
    (type_of% (@actual_complete_higher_inventory_coercivity)) ↔ arena.Law actual :=
  Iff.rfl

/-- A whole-family intervention on the actual numeric observation. -/
private def rejected : Realization signature :=
  realize signature (fun _ X n =>
    let R := actualDefect X n - completeFirstLayerLoss X n
    1000 * (X ^ (3 / 4 : ℝ) * log X * sqrt R + X * log X * R + log X ^ 2) + 1)
    (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hbad
  have h := (hbad (X := exp 2) le_rfl 1 le_rfl).2
  change
    1000 * ((exp 2) ^ (3 / 4 : ℝ) * log (exp 2) *
      sqrt (actualDefect (exp 2) 1 - completeFirstLayerLoss (exp 2) 1) +
      exp 2 * log (exp 2) *
        (actualDefect (exp 2) 1 - completeFirstLayerLoss (exp 2) 1) +
      log (exp 2) ^ 2) + 1 ≤
    1000 * ((exp 2) ^ (3 / 4 : ℝ) * log (exp 2) *
      sqrt (actualDefect (exp 2) 1 - completeFirstLayerLoss (exp 2) 1) +
      exp 2 * log (exp 2) *
        (actualDefect (exp 2) 1 - completeFirstLayerLoss (exp 2) 1) +
      log (exp 2) ^ 2) at h
  linarith only [h]

private theorem mismatch_weight_nonnegative (X : ℝ) (n : ℕ) (c : ℕ × ℕ)
    (hc : c ∈ (coordinates n \ coordinates (strictInteger (referencePrice X))) ∪
      (coordinates (strictInteger (referencePrice X)) \ coordinates n)) :
    0 ≤ coordinateWeight c := by
  rcases mem_union.mp hc with hc | hc <;>
    exact (mem_coordinates.mp (mem_sdiff.mp hc).1).1.log_pos.le

/-- Dependence is witnessed in the original domain without assuming positive
canonical mass: a power of two has a coordinate beyond the canonical valuation. -/
private theorem mismatch_changes {X : ℝ} (hX : exp 2 ≤ X) :
    ∃ N n : ℕ, 1 ≤ N ∧ 1 ≤ n ∧
      higherInventoryMismatch X N ≠ higherInventoryMismatch X n := by
  classical
  have hX0 : 0 < X := (exp_pos 2).trans_le hX
  have hL : 2 ≤ log X := (le_log_iff_exp_le hX0).mpr hX
  have hlam : 0 < referencePrice X :=
    one_div_pos.mpr (mul_pos hX0 (by linarith : 0 < log X))
  let N := strictInteger (referencePrice X)
  let k := N.factorization 2 + 2
  let n := 2 ^ k
  have hfac : n.factorization 2 = k := by
    dsimp only [n]
    rw [Nat.factorization_pow_self Nat.prime_two]
  have hin : (2, k) ∈ coordinates n := by
    apply mem_coordinates.mpr
    refine ⟨Nat.prime_two, ?_, ?_⟩
    · dsimp only [k]
      omega
    · rw [hfac]
  have hout : (2, k) ∉ coordinates N := by
    intro hc
    have hv := (mem_coordinates.mp hc).2.2
    dsimp only [k] at hv
    omega
  have hmem : (2, k) ∈ (coordinates n \ coordinates N) ∪
      (coordinates N \ coordinates n) :=
    mem_union_left _ (mem_sdiff.mpr ⟨hin, hout⟩)
  have hsingle : coordinateWeight (2, k) ≤ higherInventoryMismatch X n := by
    unfold higherInventoryMismatch
    exact single_le_sum (fun c hc => mismatch_weight_nonnegative X n c hc) hmem
  have hpos : 0 < higherInventoryMismatch X n := by
    have hlog : 0 < coordinateWeight (2, k) := by
      change 0 < log (2 : ℝ)
      exact log_pos (by norm_num)
    exact hlog.trans_le hsingle
  have hzero : higherInventoryMismatch X N = 0 := by
    simp [higherInventoryMismatch, N]
  have hn : 1 ≤ n := by
    have hnpos : 0 < n := by
      dsimp only [n]
      exact pow_pos (by norm_num : 0 < (2 : ℕ)) k
    omega
  refine ⟨N, n, strictInteger_pos hlam, hn, ?_⟩
  rw [hzero]
  exact ne_of_lt hpos

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨N, n, _, _, hne⟩ := mismatch_changes (X := exp 2) le_rfl
  exact ⟨exp 2, N, n, hne⟩

def family : Registration arena (type_of% (@actual_complete_higher_inventory_coercivity)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨@actual_complete_higher_inventory_coercivity, rejected, rejected_law⟩
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
    (@actual_complete_higher_inventory_coercivity) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.ActualHigherInventoryCoercivity.actual_complete_higher_inventory_coercivity.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.ActualHigherInventoryCoercivity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ X n => higherInventoryMismatch X n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.ActualHigherInventoryCoercivity
    definition := none
    coordinates := #[0]
    readouts := #[{
      -- Four original Pi bodies, the original R let body, And's right clause,
      -- and the left operand of LE.le.
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Robin.PriceRecord.ActualHigherInventoryCoercivity
