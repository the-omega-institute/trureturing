import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.ActualBalancedExtremizer
import D5.S3.Arith.Robin.ActualBalancedExtremizer
import D5.S3.Arith.Robin.PriceRecord.FullPrimePowerArithmeticSurplus
import Reg.Support.DependentFamily

/-! Source-bound full-telescope audit attempt. Producer status is determined
by the current scoped report, never by this comment or kernel success alone. -/
noncomputable section
set_option autoImplicit false
namespace Reg.D5.S3.Arith.Robin.ActualBalancedExtremizer
open _root_.D5.S3.Arith.Robin.ActualBalancedExtremizer
open _root_.D5.S3.Weil.GronwallLowerEnvelope
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
open _root_.D5.S3.Arith.Robin.ActualTwoPriceDefect
open _root_.D5.S3.Arith.Robin.ActualGlobalBracketing
open _root_.D5.S3.Arith.Robin.ActualRobinInterval
open _root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail
open _root_.D5.S3.Arith.Robin.PriceRecord.FullPrimePowerArithmeticSurplus
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Filter
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
  realize signature (fun _ _ n => robinLogMargin n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => -(n : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := (∃ n : ℕ, 5040 < n ∧ (R.readout () ()) n ≤ 0) →
    ∃ N : ℕ, 55440 < N ∧ (R.readout () ()) N ≤ 0 ∧
      (∀ m : ℕ, 5040 < m → (R.readout () ()) N ≤ (R.readout () ()) m) ∧
      0 < price (Real.log N) ∧ price (Real.log N) < boundaryPrice ∧
      IsGoldenResourceOptimal (price (Real.log N)) N ∧
      (∀ m : ℕ, 1 ≤ m → m ≠ N →
        goldenResourceObjective (price (Real.log N)) m <
          goldenResourceObjective (price (Real.log N)) N) ∧
      N = strictInteger (price (Real.log N)) ∧
      N = maximalInteger (price (Real.log N)) ∧
      (∀ p k : ℕ, p.Prime → 1 ≤ k →
        price (Real.log N) ≠ goldenLayerMarginal p k)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hf : ∃ n : ℕ, 5040 < n ∧ rejected.readout () () n ≤ 0 :=
    ⟨5041, by norm_num, by change -(5041 : ℝ) ≤ 0; norm_num⟩
  obtain ⟨N, hN, _, hmin, _⟩ := h hf
  have hb := hmin (N + 1) (by omega)
  change -(N : ℝ) ≤ -((N + 1 : ℕ) : ℝ) at hb
  push_cast at hb
  linarith only [hb]

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  by_contra h
  push Not at h
  have hc : robinLogMargin = fun _ : ℕ => Real.eulerMascheroniConstant := by
    funext n
    have he := h () n 0
    change robinLogMargin n = robinLogMargin 0 at he
    simpa [robinLogMargin] using he
  have hl := robin_log_margin_liminf
  rw [hc] at hl
  simp only [liminf_const] at hl
  linarith [Real.one_half_lt_eulerMascheroniConstant]

def family : Registration arena (type_of% (@failure_has_unique_internal_optimizer)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@failure_has_unique_internal_optimizer, rejected, rejected_law⟩
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
    (@failure_has_unique_internal_optimizer)
    (type_of% (realize signature (fun _ _ n => robinLogMargin n) (fun e => nomatch e))) Type Unit where
  unitName := `D5.S3.Arith.Robin.ActualBalancedExtremizer.failure_has_unique_internal_optimizer.audit
  realizationName := `Reg.D5.S3.Arith.Robin.ActualBalancedExtremizer.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => robinLogMargin n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.ActualBalancedExtremizer
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Arith.Robin.ActualBalancedExtremizer
