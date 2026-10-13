import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.FibonacciPrimeSupport
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Robin.FibonacciPrimeSupport

open _root_.D5.S3.Arith.Robin.FibonacciPrimeSupport
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

/-- One role: the divisor sum of a natural number. -/
abbrev sigmaSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- One role: the outer logarithm of the Robin capacity `exp γ · log (log n)`. -/
abbrev robinSignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- The bound with the divisor sum varied; the Fibonacci support and the constant stay. -/
abbrev sigmaArena : Arena where
  signature := sigmaSignature
  Law R := ∀ {n : ℕ}, n ≠ 0 → (∀ p ∈ n.primeFactors, ∃ k, Nat.fib k = p) →
    ((R.readout () () n : ℕ) : ℝ) / n < 241 / 50

/-- Robin's inequality with the outer logarithm of the capacity varied. -/
abbrev robinArena : Arena where
  signature := robinSignature
  Law R := ∀ {n : ℕ}, 5040 < n → (∀ p ∈ n.primeFactors, ∃ k, Nat.fib k = p) →
    (ArithmeticFunction.sigma 1 n : ℝ) / n <
      Real.exp Real.eulerMascheroniConstant * R.readout () () (Real.log (n : ℝ))

def sigmaActual : Realization sigmaSignature :=
  realize sigmaSignature (fun _ _ m => ArithmeticFunction.sigma 1 m) (fun e => nomatch e)

def robinActual : Realization robinSignature :=
  realize robinSignature (fun _ _ x => Real.log x) (fun e => nomatch e)

/-- The constant readout `5` replaces the divisor sum. -/
def sigmaRejected : Realization sigmaSignature :=
  realize sigmaSignature (fun _ _ _ => 5) (fun e => nomatch e)

/-- The constant readout `0` replaces the outer logarithm. -/
def robinRejected : Realization robinSignature :=
  realize robinSignature (fun _ _ _ => 0) (fun e => nomatch e)

/-- At `n = 1`, which has no prime factors, the constant `5` exceeds `241/50`. -/
theorem sigma_rejected_law : ¬ sigmaArena.Law sigmaRejected := by
  intro h
  have hbad := h (n := 1) one_ne_zero (by simp)
  change ((5 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) < 241 / 50 at hbad
  norm_num at hbad

private theorem fib_support_8192 : ∀ p ∈ (8192 : ℕ).primeFactors, ∃ k, Nat.fib k = p := by
  intro p hp
  rw [show (8192 : ℕ) = 2 ^ 13 by norm_num, Nat.primeFactors_prime_pow (by norm_num)
    Nat.prime_two, Finset.mem_singleton] at hp
  exact ⟨3, by rw [hp]; decide⟩

/-- At `n = 2^13`, whose only prime is the Fibonacci number `2`, the zero readout would make a
nonnegative ratio negative. -/
theorem robin_rejected_law : ¬ robinArena.Law robinRejected := by
  intro h
  have hbad := h (n := 8192) (by norm_num) fib_support_8192
  change (ArithmeticFunction.sigma 1 8192 : ℝ) / (8192 : ℕ) <
    Real.exp Real.eulerMascheroniConstant * (0 : ℝ) at hbad
  rw [mul_zero] at hbad
  exact absurd hbad (not_lt.mpr (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))

private theorem sigma_dependence : ObservationalDependence sigmaSignature sigmaActual := by
  intro i
  cases i
  refine ⟨(), 0, 1, ?_⟩
  change ArithmeticFunction.sigma 1 0 ≠ ArithmeticFunction.sigma 1 1
  simp

private theorem robin_dependence : ObservationalDependence robinSignature robinActual := by
  intro i
  cases i
  refine ⟨(), 1, 2, ?_⟩
  change Real.log 1 ≠ Real.log 2
  rw [Real.log_one]
  exact (Real.log_pos (by norm_num)).ne

def sigmaRegistration : Registration sigmaArena
    (∀ {n : ℕ}, n ≠ 0 → (∀ p ∈ n.primeFactors, ∃ k, Nat.fib k = p) →
      (ArithmeticFunction.sigma 1 n : ℝ) / n < 241 / 50) where
  actual := sigmaActual
  bridge := Iff.rfl
  variation := ⟨sigma_div_lt_of_fibonacci_primeFactors, sigmaRejected, sigma_rejected_law⟩
  sensitivity := ⟨fun i => ⟨sigmaRejected, fun j h => (h (Subsingleton.elim j i)).elim,
    funext (fun e => nomatch e), sigma_rejected_law⟩, fun i => nomatch i⟩
  dependence := sigma_dependence

def robinRegistration : Registration robinArena
    (∀ {n : ℕ}, 5040 < n → (∀ p ∈ n.primeFactors, ∃ k, Nat.fib k = p) →
      (ArithmeticFunction.sigma 1 n : ℝ) / n <
        Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ))) where
  actual := robinActual
  bridge := Iff.rfl
  variation := ⟨robin_of_fibonacci_primeFactors, robinRejected, robin_rejected_law⟩
  sensitivity := ⟨fun i => ⟨robinRejected, fun j h => (h (Subsingleton.elim j i)).elim,
    funext (fun e => nomatch e), robin_rejected_law⟩, fun i => nomatch i⟩
  dependence := robin_dependence

/-- The bound's record binds the divisor sum `σ 1 n` through its raw source path. -/
def sigmaAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sigma_div_lt_of_fibonacci_primeFactors)
    (type_of% (realize.{0, 0, 0, 0, 0} sigmaSignature
      (fun _ _ m => ArithmeticFunction.sigma 1 m) (fun e => nomatch e))) Unit Unit where
  unitName :=
    `D5.S3.Arith.Robin.FibonacciPrimeSupport.sigma_div_lt_of_fibonacci_primeFactors.audit
  realizationName := `Reg.D5.S3.Arith.Robin.FibonacciPrimeSupport.sigmaRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨sigmaArena⟩
  objectArena := .source ⟨sigmaArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sigmaArena ⟨sigmaRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0, 0, 0, 0, 0} sigmaSignature
    (fun _ _ m => ArithmeticFunction.sigma 1 m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.FibonacciPrimeSupport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

/-- The Robin record binds the outer logarithm of the capacity through its raw source path. -/
def robinAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@robin_of_fibonacci_primeFactors)
    (type_of% (realize.{0, 0, 0, 0, 0} robinSignature (fun _ _ x => Real.log x)
      (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Arith.Robin.FibonacciPrimeSupport.robin_of_fibonacci_primeFactors.audit
  realizationName := `Reg.D5.S3.Arith.Robin.FibonacciPrimeSupport.robinRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨robinArena⟩
  objectArena := .source ⟨robinArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source robinArena ⟨robinRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0, 0, 0, 0, 0} robinSignature (fun _ _ x => Real.log x)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.FibonacciPrimeSupport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

/-- The same divisor-sum readout, for the general support Euler-product bound. -/
abbrev ratioArena : Arena where
  signature := sigmaSignature
  Law R := ∀ n : ℕ, n ≠ 0 → ((R.readout () () n : ℕ) : ℝ) / n ≤
    ∏ p ∈ n.primeFactors, (p : ℝ) / ((p : ℝ) - 1)

/-- At one, the empty Euler product is one and the replacement divisor sum is five. -/
theorem ratio_rejected_law : ¬ ratioArena.Law sigmaRejected := by
  intro h
  have hbad := h 1 one_ne_zero
  change ((5 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) ≤
    ∏ p ∈ (1 : ℕ).primeFactors, (p : ℝ) / ((p : ℝ) - 1) at hbad
  norm_num at hbad

def ratioRegistration : Registration ratioArena (type_of% ratio_le_prod) where
  actual := sigmaActual
  bridge := Iff.rfl
  variation := ⟨ratio_le_prod, sigmaRejected, ratio_rejected_law⟩
  sensitivity := ⟨fun i => ⟨sigmaRejected, fun j h => (h (Subsingleton.elim j i)).elim,
    funext (fun e => nomatch e), ratio_rejected_law⟩, fun i => nomatch i⟩
  dependence := sigma_dependence

def ratioAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@ratio_le_prod)
    (type_of% (realize.{0, 0, 0, 0, 0} sigmaSignature
      (fun _ _ m => ArithmeticFunction.sigma 1 m) (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Arith.Robin.FibonacciPrimeSupport.ratio_le_prod.audit
  realizationName := `Reg.D5.S3.Arith.Robin.FibonacciPrimeSupport.ratioRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨ratioArena⟩
  objectArena := .source ⟨ratioArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source ratioArena ⟨ratioRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0, 0, 0, 0, 0} sigmaSignature
    (fun _ _ m => ArithmeticFunction.sigma 1 m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.FibonacciPrimeSupport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Arith.Robin.FibonacciPrimeSupport
