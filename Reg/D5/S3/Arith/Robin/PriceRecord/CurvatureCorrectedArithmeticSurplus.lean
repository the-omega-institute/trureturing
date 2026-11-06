import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.PriceRecord.CurvatureCorrectedArithmeticSurplus
import D5.S3.Arith.Robin.PriceRecord.ActualBalancedExtremizer
import D5.S3.Arith.Robin.PriceRecord.FullPrimePowerArithmeticSurplus
import Reg.Support.DependentFamily

/-! Source-bound full-telescope audit attempt. Producer status is determined
by the current scoped report, never by this comment or kernel success alone. -/
noncomputable section
set_option autoImplicit false
namespace Reg.D5.S3.Arith.Robin.PriceRecord.CurvatureCorrectedArithmeticSurplus
open _root_.D5.S3.Arith.Robin.PriceRecord.CurvatureCorrectedArithmeticSurplus
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
  Params := ℝ × ℝ
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
  realize signature (fun _ p n => fullPrimePowerResidual p.1 -
    (Real.log (n : ℝ) - Chebyshev.psi p.1) / (p.1 * Real.log p.1) +
    (Real.log (Real.log p.1) + p.2 / (p.1 * Real.log p.1) -
      Real.log (Real.log (p.1 + p.2))) +
    Real.log 2 / (12 * p.1 * Real.log p.1)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {z M : ℝ}, 11 < z → 0 < M → M < 1 / 2 →
    ∀ {n : ℕ}, 0 < n → n.primeFactors = Nat.primesLE ⌊z⌋₊ →
    let K := Real.log (Real.log z) + M / (z * Real.log z) -
      Real.log (Real.log (z + M))
    0 < K ∧ K < (Real.log z + 1) / (8 * z ^ 2 * (Real.log z) ^ 2) ∧
      Real.log 2 / (12 * z * Real.log z) <
        R.readout () (z, M) n +
          (Real.log (n : ℝ) - Chebyshev.psi z) / (z * Real.log z) -
            fullPrimePowerResidual z - K

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs : (2310 : ℕ).primeFactors = Nat.primesLE ⌊(12 : ℝ)⌋₊ := by
    rw [Nat.primeFactors_mul (by norm_num : (210 : ℕ) ≠ 0) (by norm_num : (11 : ℕ) ≠ 0)]
    rw [Nat.primeFactors_mul (by norm_num : (30 : ℕ) ≠ 0) (by norm_num : (7 : ℕ) ≠ 0)]
    rw [Nat.primeFactors_mul (by norm_num : (6 : ℕ) ≠ 0) (by norm_num : (5 : ℕ) ≠ 0)]
    rw [Nat.primeFactors_mul (by norm_num : (2 : ℕ) ≠ 0) (by norm_num : (3 : ℕ) ≠ 0)]
    norm_num [Nat.primesLE, Nat.primesBelow, Finset.range_add_one, (by norm_num : Nat.Prime 2).primeFactors, (by norm_num : Nat.Prime 3).primeFactors, (by norm_num : Nat.Prime 5).primeFactors, (by norm_num : Nat.Prime 7).primeFactors, (by norm_num : Nat.Prime 11).primeFactors] <;> decide
  have hb := (h (z := 12) (M := 1/4) (by norm_num) (by norm_num)
    (by norm_num) (n := 2310) (by norm_num) hs).2.2
  dsimp only [rejected, realize, Realization.readout] at hb
  linarith only [hb]
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  have hOne : tail 1 = 0 := by simp [tail]
  have hTwo : tail 2 = -Real.log (3 / 4 : ℝ) := by
    norm_num [tail, layerTail, Nat.prime_two.primeFactors, Nat.prime_two.factorization]
  refine ⟨((12 : ℝ), (1/4 : ℝ)), 1, 2, ?_⟩
  change tail 1 ≠ tail 2
  rw [hOne, hTwo]
  exact ne_of_lt (neg_pos.mpr (Real.log_neg (by norm_num) (by norm_num)))

def family : Registration arena (type_of% (@arithmetic_surplus_dominates_loglog_curvature)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@arithmetic_surplus_dominates_loglog_curvature, rejected, rejected_law⟩
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
    (@arithmetic_surplus_dominates_loglog_curvature)
    (type_of% (realize signature (fun _ _ n => tail n) (fun e => nomatch e))) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.CurvatureCorrectedArithmeticSurplus.arithmetic_surplus_dominates_loglog_curvature.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.CurvatureCorrectedArithmeticSurplus.family
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
    owner := `D5.S3.Arith.Robin.PriceRecord.CurvatureCorrectedArithmeticSurplus
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Arith.Robin.PriceRecord.CurvatureCorrectedArithmeticSurplus
