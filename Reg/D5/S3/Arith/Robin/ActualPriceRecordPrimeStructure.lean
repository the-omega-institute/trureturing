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

private theorem four_price_record :
    ∀ n : ℕ, 0 < n → n < 4 →
      goldenResourceObjective (1 / (40 * Real.log 4 * Real.log (Real.log 4))) n <
        goldenResourceObjective (1 / (40 * Real.log 4 * Real.log (Real.log 4))) 4 := by
  let X : ℝ := Real.log 4
  let lam : ℝ := 1 / (40 * X * Real.log X)
  have hlog4 : X = 2 * Real.log 2 := by
    have hh := Real.log_pow (2 : ℝ) 2
    norm_num only [pow_two, show (2 : ℝ) * 2 = 4 by norm_num, Nat.cast_ofNat] at hh
    exact hh
  have hXlo : 4 / 3 < X := by rw [hlog4]; linarith [Real.log_two_gt_d9]
  have hXhi : X < 7 / 5 := by rw [hlog4]; linarith [Real.log_two_lt_d9]
  have hX0 : 0 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hXL : 1 / 3 < X * Real.log X := by
    have hh := Real.one_sub_inv_le_log_of_pos hX0
    have hx := mul_le_mul_of_nonneg_left hh hX0.le
    have hid : X * (1 - X⁻¹) = X - 1 := by field_simp; ring
    rw [hid] at hx
    linarith
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have hlam1 : lam < 1 / 10 := by
    dsimp [lam]
    apply (div_lt_iff₀ (by positivity : 0 < 40 * X * Real.log X)).mpr
    nlinarith
  have hcost : lam * X < 7 / 50 := by nlinarith
  have hgain : 1 / 7 ≤ Real.log (7 / 6 : ℝ) := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 7 / 6)
    norm_num at hh ⊢
    exact hh
  have hlogdiff : Real.log (7 / 4 : ℝ) - Real.log (3 / 2 : ℝ) =
      Real.log (7 / 6 : ℝ) := by
    rw [← Real.log_div (by norm_num : (7 / 4 : ℝ) ≠ 0) (by norm_num : (3 / 2 : ℝ) ≠ 0)]
    congr 1
    norm_num
  have hscore : Real.log (3 / 2 : ℝ) < Real.log (7 / 4 : ℝ) - lam * X := by
    linarith
  intro n hn hlt
  have hratio : (ArithmeticFunction.sigma 1 n : ℝ) / n ≤ 3 / 2 := by
    interval_cases n <;> norm_num [ArithmeticFunction.sigma] at *
  have hrpos : 0 < (ArithmeticFunction.sigma 1 n : ℝ) / n :=
    div_pos (by exact_mod_cast ArithmeticFunction.sigma_pos 1 n hn.ne')
      (by exact_mod_cast hn)
  have hlog := Real.log_le_log hrpos hratio
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hleft := mul_nonneg hlam.le hlogn
  rw [golden_resource_sigma_identity _ (by omega : 1 ≤ n),
    golden_resource_sigma_identity _ (by norm_num : 1 ≤ (4 : ℕ))]
  have hs : (ArithmeticFunction.sigma 1 4 : ℝ) = 7 := by norm_num [ArithmeticFunction.sigma]
  rw [hs]
  change Real.log ((ArithmeticFunction.sigma 1 n : ℝ) / n) - lam * Real.log n <
    Real.log (7 / 4 : ℝ) - lam * X
  linarith

def massRejected : Realization primeSignature :=
  realize primeSignature (fun _ _ _ => -1) (fun e => nomatch e)

private theorem confinement_rejected : ¬ confinementArena.Law massRejected := by
  rintro ⟨K, hK, hbad⟩
  have hh := hbad 4 (by norm_num) four_price_record
  have hn := hh.2.2.2.1
  change (0 : ℝ) ≤ -1 at hn
  norm_num at hn

private theorem mass_dependence : ObservationalDependence primeSignature massActual := by
  intro i
  refine ⟨(), 1, 4, ?_⟩
  change (∑ p ∈ (1 : ℕ).primeFactors,
      (((1 : ℕ).factorization p - 1 : ℕ) : ℝ) * Real.log p) ≠
    ∑ p ∈ (4 : ℕ).primeFactors,
      (((4 : ℕ).factorization p - 1 : ℕ) : ℝ) * Real.log p
  have hfour : (4 : ℕ).primeFactors = {2} := by
    change ((2 : ℕ) ^ 2).primeFactors = {2}
    exact Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two
  have hval : (4 : ℕ).factorization 2 = 2 := by
    change ((2 : ℕ) ^ 2).factorization 2 = 2
    exact Nat.factorization_pow_self Nat.prime_two
  simp only [Nat.primeFactors_one, Finset.sum_empty, hfour, Finset.sum_singleton, hval]
  norm_num
  exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne

def confinementFamily : Registration confinementArena confinementScope where
  actual := massActual
  bridge := confinement_source_bridge
  variation := ⟨confinement_actual_law, massRejected, confinement_rejected⟩
  sensitivity := ⟨fun i => ⟨massRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, confinement_rejected⟩,
    fun i => nomatch i⟩
  dependence := mass_dependence

def confinementAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@price_record_prime_confinement) (Realization primeSignature) Type Unit where
  unitName := `D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure.price_record_prime_confinement.audit
  realizationName := `Reg.D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure.confinementFamily
  realizationSource := none
  generated := false
  arena := .source ⟨confinementArena⟩
  objectArena := .source ⟨confinementArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source confinementArena ⟨confinementFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize primeSignature massActual.readout massActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "arg", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["arg", "body", "arg", "body", "body", "body", "body", "body", "arg", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["arg", "body", "arg", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

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
   for localization. The confinement family supplies these obligations; its outer
   source binding is checked separately. -/

#print axioms divisorFamily
#print axioms localization_actual_law

end Reg.D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure
