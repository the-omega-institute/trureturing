import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure

open _root_.D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure
open _root_.D5.S3.Arith.Robin.ActualTwoPriceDefect
open _root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Chebyshev

noncomputable section

abbrev divisorSignature : Signature where
  Params := ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def divisorActual : Realization divisorSignature :=
  realize divisorSignature (fun _ _ m => m) (fun e => nomatch e)

def divisorRejected : Realization divisorSignature :=
  realize divisorSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev divisorArena : Arena where
  signature := divisorSignature
  Law R := ∀ {m : ℕ}, 0 < m → ∀ {lam : ℝ}, 0 < lam →
    (∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective lam n < goldenResourceObjective lam m) →
    R.readout () lam m ∣ strictInteger lam

private theorem divisor_rejected : ¬ divisorArena.Law divisorRejected := by
  intro h
  have hh := h (m := 1) (by norm_num) (lam := 1) (by norm_num)
    (fun n hn hlt => by omega)
  change 0 ∣ strictInteger 1 at hh
  have hz := zero_dvd_iff.mp hh
  have hp := strictInteger_pos (by norm_num : (0 : ℝ) < 1)
  omega

private theorem divisor_dependence : ObservationalDependence divisorSignature divisorActual := by
  intro i
  exact ⟨1, 1, 2, by norm_num [divisorActual, realize]⟩

def divisorFamily : Registration divisorArena (type_of% @price_record_divides_strictInteger) where
  actual := divisorActual
  bridge := Iff.rfl
  variation := ⟨price_record_divides_strictInteger, divisorRejected, divisor_rejected⟩
  sensitivity := ⟨fun i => ⟨divisorRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, divisor_rejected⟩,
    fun i => nomatch i⟩
  dependence := divisor_dependence

def divisorAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@price_record_divides_strictInteger) (Realization divisorSignature) Type Unit where
  unitName := `D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure.price_record_divides_strictInteger.audit
  realizationName := `Reg.D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure.divisorFamily
  realizationSource := none
  generated := false
  arena := .source ⟨divisorArena⟩
  objectArena := .source ⟨divisorArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source divisorArena ⟨divisorFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize divisorSignature divisorActual.readout divisorActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

/-- Exact complete source telescopes retain the price record and same-m outputs. -/
abbrev confinementScope := type_of% price_record_prime_confinement
abbrev localizationScope := type_of% price_record_largest_prime_localization

theorem source_confinement : confinementScope := price_record_prime_confinement
theorem source_localization : localizationScope := price_record_largest_prime_localization

abbrev primeSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def primeActual : Realization primeSignature :=
  realize primeSignature (fun _ _ m => (largestPrime m : ℝ)) (fun e => nomatch e)

def massActual : Realization primeSignature :=
  realize primeSignature (fun _ _ m =>
    ∑ p ∈ m.primeFactors, ((m.factorization p - 1 : ℕ) : ℝ) * Real.log p)
    (fun e => nomatch e)

abbrev confinementArena : Arena where
  signature := primeSignature
  Law R := ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 3 ≤ m →
    let X := Real.log (m : ℝ)
    let lam0 := 1 / (40 * X * Real.log X)
    (∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective lam0 n < goldenResourceObjective lam0 m) →
    (∀ p q : ℕ, p.Prime → q.Prime → p < q →
      m.factorization q ≤ m.factorization p) ∧
    m.primeFactors = Nat.primesLE (largestPrime m) ∧
    X = Chebyshev.theta (largestPrime m) + R.readout () () m ∧
    0 ≤ R.readout () () m ∧
    R.readout () () m ≤
      2 * Chebyshev.theta (Real.sqrt (80 * X)) +
        2 * (Chebyshev.psi (40 * X) - Chebyshev.theta (40 * X)) ∧
    2 * Chebyshev.theta (Real.sqrt (80 * X)) +
        2 * (Chebyshev.psi (40 * X) - Chebyshev.theta (40 * X)) ≤ K * Real.sqrt X ∧
    X - K * Real.sqrt X ≤ Chebyshev.theta (largestPrime m) ∧
    Chebyshev.theta (largestPrime m) ≤ X ∧
    m ∣ strictInteger (1 / (40 * X * Real.log (40 * X))) ∧
    (∀ p k : ℕ, p.Prime → 1 ≤ k → k ≤ m.factorization p →
      (p : ℝ) ^ k < 40 * (k : ℝ) * X)

theorem confinement_source_bridge : confinementScope ↔ confinementArena.Law massActual := Iff.rfl

theorem confinement_actual_law : confinementArena.Law massActual := price_record_prime_confinement

abbrev localizationArena : Arena where
  signature := primeSignature
  Law R := ∀ epsilon : ℝ, 0 < epsilon → ∃ A : ℝ, 0 < A ∧
    ∀ m : ℕ, 3 ≤ m → A ≤ Real.log (m : ℝ) →
    (∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective (1 / (40 * Real.log m * Real.log (Real.log m))) n <
        goldenResourceObjective (1 / (40 * Real.log m * Real.log (Real.log m))) m) →
    |R.readout () () m / Real.log m - 1| < epsilon

theorem localization_source_bridge : localizationScope ↔ localizationArena.Law primeActual := Iff.rfl

theorem localization_actual_law : localizationArena.Law primeActual :=
  price_record_largest_prime_localization

/- The localization law retains the record even for a rejected realization.
   A constant-zero rejection needs arbitrarily large integers satisfying this
   exact self-price record, which is not supplied by the conditional theorem.
   No variation/sensitivity proof or declared_validated registration is asserted
   for localization or the complete confinement telescope. -/

#print axioms divisorFamily
#print axioms localization_actual_law

end Reg.D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure
