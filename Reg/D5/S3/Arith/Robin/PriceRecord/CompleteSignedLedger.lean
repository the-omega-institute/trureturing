import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.PriceRecord.CompleteSignedLedger
import D5.S3.Arith.Robin.PriceRecord.ActualBalancedExtremizer
import D5.S3.Arith.Robin.PriceRecord.FullPrimePowerArithmeticSurplus
import Reg.Support.DependentFamily

/-! Source-bound full-telescope audit attempt. Producer status is determined
by the current scoped report, never by this comment or kernel success alone. -/
noncomputable section
set_option autoImplicit false
namespace Reg.D5.S3.Arith.Robin.PriceRecord.CompleteSignedLedger
open _root_.D5.S3.Arith.Robin.PriceRecord.CompleteSignedLedger
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
  Params := ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => tail n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => tail n + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {z : ℝ}, 4 ≤ z → ∀ {N : ℕ}, 0 < N →
    N.primeFactors = Nat.primesLE ⌊z⌋₊ →
    let M := Real.log (N : ℝ) - z
    robinLogMargin N =
      _root_.D5.S3.Weil.Mertens.WeightedTailTransport.weightedTail
        _root_.D5.S3.Arith.Robin.CompleteMertensPeak.psiErrorKernel z +
      (R.readout () z N + (Real.log (N : ℝ) - Chebyshev.psi z) / (z * Real.log z) -
        fullPrimePowerResidual z) -
      (Real.log (Real.log z) + M / (z * Real.log z) -
        Real.log (Real.log (z + M)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs : (6 : ℕ).primeFactors = Nat.primesLE ⌊(4 : ℝ)⌋₊ := by
    rw [Nat.primeFactors_mul (by norm_num : (2 : ℕ) ≠ 0) (by norm_num : (3 : ℕ) ≠ 0)]
    norm_num [Nat.primesLE, Nat.primesBelow, Finset.range_add_one,
      Nat.prime_two.primeFactors, Nat.prime_three.primeFactors] <;> decide
  have hb := h (z := 4) (by norm_num) (N := 6) (by norm_num) hs
  have ha := robin_margin_eq_complete_signed_ledger (z := 4) (by norm_num)
    (N := 6) (by norm_num) hs
  dsimp only [rejected, realize, Realization.readout] at hb
  dsimp only at ha hb
  linarith only [hb, ha]
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  have hOne : tail 1 = 0 := by simp [tail]
  have hTwo : tail 2 = -Real.log (3 / 4 : ℝ) := by
    norm_num [tail, layerTail, Nat.prime_two.primeFactors, Nat.prime_two.factorization]
  refine ⟨(4 : ℝ), 1, 2, ?_⟩
  change tail 1 ≠ tail 2
  rw [hOne, hTwo]
  exact ne_of_lt (neg_pos.mpr (Real.log_neg (by norm_num) (by norm_num)))

def family : Registration arena (type_of% (@robin_margin_eq_complete_signed_ledger)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@robin_margin_eq_complete_signed_ledger, rejected, rejected_law⟩
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
    (@robin_margin_eq_complete_signed_ledger)
    (type_of% (realize signature (fun _ _ n => tail n) (fun e => nomatch e))) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.CompleteSignedLedger.robin_margin_eq_complete_signed_ledger.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.CompleteSignedLedger.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => tail n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.CompleteSignedLedger
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Arith.Robin.PriceRecord.CompleteSignedLedger
