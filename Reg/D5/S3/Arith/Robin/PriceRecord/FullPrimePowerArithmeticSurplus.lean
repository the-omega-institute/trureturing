import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.PriceRecord.FullPrimePowerArithmeticSurplus
import D5.S3.Arith.Robin.ActualBalancedExtremizer
import D5.S3.Arith.Robin.PriceRecord.FullPrimePowerArithmeticSurplus
import Reg.Support.DependentFamily

/-! Source-bound full-telescope audit attempt. Producer status is determined
by the current scoped report, never by this comment or kernel success alone. -/
noncomputable section
set_option autoImplicit false
namespace Reg.D5.S3.Arith.Robin.PriceRecord.FullPrimePowerArithmeticSurplus
open _root_.D5.S3.Arith.Robin.PriceRecord.FullPrimePowerArithmeticSurplus
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
  realize signature (fun _ z n => fullPrimePowerResidual z -
    (Real.log (n : ℝ) - Chebyshev.psi z) / (z * Real.log z) +
    Real.log 2 / (6 * z * Real.log z)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {z : ℝ}, 4 ≤ z → ∀ {n : ℕ}, 0 < n →
    n.primeFactors = Nat.primesLE ⌊z⌋₊ →
    Real.log 2 / (6 * z * Real.log z) <
      R.readout () z n + (Real.log (n : ℝ) - Chebyshev.psi z) /
        (z * Real.log z) - fullPrimePowerResidual z

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs : (6 : ℕ).primeFactors = Nat.primesLE ⌊(4 : ℝ)⌋₊ := by
    rw [Nat.primeFactors_mul (by norm_num : (2 : ℕ) ≠ 0) (by norm_num : (3 : ℕ) ≠ 0)]
    norm_num [Nat.primesLE, Nat.primesBelow, Finset.range_succ, (by norm_num : Nat.Prime 2).primeFactors, (by norm_num : Nat.Prime 3).primeFactors]
  have hb := h (z := 4) (by norm_num) (n := 6) (by norm_num) hs
  change Real.log 2 / (6 * 4 * Real.log 4) <
    (fullPrimePowerResidual 4 - (Real.log (6 : ℝ) - Chebyshev.psi 4) /
      (4 * Real.log 4) + Real.log 2 / (6 * 4 * Real.log 4)) +
      (Real.log (6 : ℝ) - Chebyshev.psi 4) / (4 * Real.log 4) -
      fullPrimePowerResidual 4 at hb
  linarith only [hb]
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  have hOne : tail 1 = 0 := by simp [tail]
  have hTwo : tail 2 = -Real.log (3 / 4 : ℝ) := by
    norm_num [tail, layerTail, Nat.prime_two.primeFactors, Nat.prime_two.factorization]
  refine ⟨(4 : ℝ), 1, 2, ?_⟩
  change tail 1 ≠ tail 2
  rw [hOne, hTwo]
  exact ne_of_lt (neg_pos.mpr (Real.log_neg (by norm_num) (by norm_num)))

def family : Registration arena (type_of% (@full_prime_power_arithmetic_surplus)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@full_prime_power_arithmetic_surplus, rejected, rejected_law⟩
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
    (@full_prime_power_arithmetic_surplus)
    (type_of% (realize signature (fun _ _ n => tail n) (fun e => nomatch e))) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.FullPrimePowerArithmeticSurplus.full_prime_power_arithmetic_surplus.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.FullPrimePowerArithmeticSurplus.family
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
    owner := `D5.S3.Arith.Robin.PriceRecord.FullPrimePowerArithmeticSurplus
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Arith.Robin.PriceRecord.FullPrimePowerArithmeticSurplus
