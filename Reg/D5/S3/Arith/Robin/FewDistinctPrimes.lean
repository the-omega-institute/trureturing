import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.FewDistinctPrimes
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Robin.FewDistinctPrimes

open _root_.D5.S3.Arith.Robin.FewDistinctPrimes
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

/-- One role: the outer logarithm of the Robin capacity `exp γ · log (log n)`. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- The capacity's outer logarithm varies; the divisor ratio and the inner logarithm stay. -/
abbrev eightArena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ}, 5040 < n → n.primeFactors.card ≤ 8 →
    (ArithmeticFunction.sigma 1 n : ℝ) / n <
      Real.exp Real.eulerMascheroniConstant * R.readout () () (Real.log (n : ℝ))

abbrev rangeArena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ}, 5040 < n → n < 223092870 →
    (ArithmeticFunction.sigma 1 n : ℝ) / n <
      Real.exp Real.eulerMascheroniConstant * R.readout () () (Real.log (n : ℝ))

def actual : Realization signature :=
  realize signature (fun _ _ x => Real.log x) (fun e => nomatch e)

/-- The constant readout `0` replaces the outer logarithm. -/
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem ratio_nonneg (n : ℕ) : 0 ≤ (ArithmeticFunction.sigma 1 n : ℝ) / n :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

private theorem card_8192 : (Nat.primeFactors 8192).card ≤ 8 := by
  rw [show (8192 : ℕ) = 2 ^ 13 by norm_num, Nat.primeFactors_prime_pow (by norm_num)
    Nat.prime_two, Finset.card_singleton]
  norm_num

/-- At `n = 2^13` the zero readout would make a nonnegative ratio negative. -/
theorem rejected_eight_law : ¬ eightArena.Law rejected := by
  intro h
  have hbad := h (n := 8192) (by norm_num) card_8192
  change (ArithmeticFunction.sigma 1 8192 : ℝ) / (8192 : ℕ) <
    Real.exp Real.eulerMascheroniConstant * 0 at hbad
  rw [mul_zero] at hbad
  exact absurd hbad (not_lt.mpr (ratio_nonneg 8192))

theorem rejected_range_law : ¬ rangeArena.Law rejected := by
  intro h
  have hbad := h (n := 8192) (by norm_num) (by norm_num)
  change (ArithmeticFunction.sigma 1 8192 : ℝ) / (8192 : ℕ) <
    Real.exp Real.eulerMascheroniConstant * 0 at hbad
  rw [mul_zero] at hbad
  exact absurd hbad (not_lt.mpr (ratio_nonneg 8192))

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 1, 2, ?_⟩
  change Real.log 1 ≠ Real.log 2
  rw [Real.log_one]
  exact (Real.log_pos (by norm_num)).ne

def eightRegistration : Registration eightArena
    (∀ {n : ℕ}, 5040 < n → n.primeFactors.card ≤ 8 →
      (ArithmeticFunction.sigma 1 n : ℝ) / n <
        Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨robin_of_card_primeFactors_le_eight, rejected, rejected_eight_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    funext (fun e => nomatch e), rejected_eight_law⟩, fun i => nomatch i⟩
  dependence := actual_dependence

def rangeRegistration : Registration rangeArena
    (∀ {n : ℕ}, 5040 < n → n < 223092870 →
      (ArithmeticFunction.sigma 1 n : ℝ) / n <
        Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨robin_lt_223092870, rejected, rejected_range_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    funext (fun e => nomatch e), rejected_range_law⟩, fun i => nomatch i⟩
  dependence := actual_dependence

/-- Each record binds the outer logarithm of the capacity through its raw source path, with the
dependent-family law and its four kernel obligations. -/
def eightAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@robin_of_card_primeFactors_le_eight)
    (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => Real.log x)
      (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Arith.Robin.FewDistinctPrimes.robin_of_card_primeFactors_le_eight.audit
  realizationName := `Reg.D5.S3.Arith.Robin.FewDistinctPrimes.eightRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨eightArena⟩
  objectArena := .source ⟨eightArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source eightArena ⟨eightRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => Real.log x)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.FewDistinctPrimes
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

def rangeAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@robin_lt_223092870)
    (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => Real.log x)
      (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Arith.Robin.FewDistinctPrimes.robin_lt_223092870.audit
  realizationName := `Reg.D5.S3.Arith.Robin.FewDistinctPrimes.rangeRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨rangeArena⟩
  objectArena := .source ⟨rangeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rangeArena ⟨rangeRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => Real.log x)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.FewDistinctPrimes
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

/-- One role: the product of a list of natural numbers. -/
abbrev listSignature : Signature where
  Params := Unit
  State _ := List ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- The factor representation with the divisor sum varied; the exponent lists stay. -/
abbrev reprArena : Arena where
  signature := sigmaSignature
  Law R := ∀ {ps : List ℕ}, (∀ p ∈ ps, p.Prime) → ps.Nodup → ∀ {n : ℕ}, n ≠ 0 →
    n.primeFactors ⊆ ps.toFinset →
      powProd ps (ps.map n.factorization) = n ∧
        geomProd ps (ps.map n.factorization) = R.readout () () n

/-- The geometric-sum bound with the product of the primes varied. -/
abbrev boundArena : Arena where
  signature := listSignature
  Law R := ∀ (ps es : List ℕ), (∀ p ∈ ps, 2 ≤ p) → es.length = ps.length →
    geomProd ps es * (ps.map (· - 1)).prod ≤ powProd ps es * R.readout () () ps

def reprActual : Realization sigmaSignature :=
  realize sigmaSignature (fun _ _ m => ArithmeticFunction.sigma 1 m) (fun e => nomatch e)

def boundActual : Realization listSignature :=
  realize listSignature (fun _ _ l => l.prod) (fun e => nomatch e)

/-- The constant readout `0` replaces the divisor sum. -/
def reprRejected : Realization sigmaSignature :=
  realize sigmaSignature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The constant readout `0` replaces the product of the primes. -/
def boundRejected : Realization listSignature :=
  realize listSignature (fun _ _ _ => 0) (fun e => nomatch e)

/-- With no primes and `n = 1`, the empty geometric product is `1`, not `0`. -/
theorem repr_rejected_law : ¬ reprArena.Law reprRejected := by
  intro h
  have hbad := (h (ps := []) (by simp) List.nodup_nil (n := 1) one_ne_zero (by simp)).2
  change geomProd [] ([].map (Nat.factorization 1)) = (0 : ℕ) at hbad
  simp [geomProd] at hbad

/-- For the single prime `2` with exponent `0`, the left side is `1` and the zero readout makes
the right side `0`. -/
theorem bound_rejected_law : ¬ boundArena.Law boundRejected := by
  intro h
  have hbad := h [2] [0] (by simp) rfl
  change geomProd [2] [0] * ([2].map (· - 1)).prod ≤ powProd [2] [0] * (0 : ℕ) at hbad
  revert hbad
  decide

private theorem repr_dependence : ObservationalDependence sigmaSignature reprActual := by
  intro i
  cases i
  refine ⟨(), 0, 1, ?_⟩
  change ArithmeticFunction.sigma 1 0 ≠ ArithmeticFunction.sigma 1 1
  simp

private theorem bound_dependence : ObservationalDependence listSignature boundActual := by
  intro i
  cases i
  refine ⟨(), [], [2], ?_⟩
  change ([] : List ℕ).prod ≠ [2].prod
  simp

def reprRegistration : Registration reprArena
    (∀ {ps : List ℕ}, (∀ p ∈ ps, p.Prime) → ps.Nodup → ∀ {n : ℕ}, n ≠ 0 →
      n.primeFactors ⊆ ps.toFinset →
        powProd ps (ps.map n.factorization) = n ∧
          geomProd ps (ps.map n.factorization) = ArithmeticFunction.sigma 1 n) where
  actual := reprActual
  bridge := Iff.rfl
  variation := ⟨factor_repr, reprRejected, repr_rejected_law⟩
  sensitivity := ⟨fun i => ⟨reprRejected, fun j h => (h (Subsingleton.elim j i)).elim,
    funext (fun e => nomatch e), repr_rejected_law⟩, fun i => nomatch i⟩
  dependence := repr_dependence

def boundRegistration : Registration boundArena
    (∀ (ps es : List ℕ), (∀ p ∈ ps, 2 ≤ p) → es.length = ps.length →
      geomProd ps es * (ps.map (· - 1)).prod ≤ powProd ps es * ps.prod) where
  actual := boundActual
  bridge := Iff.rfl
  variation := ⟨geomProd_le, boundRejected, bound_rejected_law⟩
  sensitivity := ⟨fun i => ⟨boundRejected, fun j h => (h (Subsingleton.elim j i)).elim,
    funext (fun e => nomatch e), bound_rejected_law⟩, fun i => nomatch i⟩
  dependence := bound_dependence

/-- The representation record binds the divisor sum `σ 1 n` through its raw source path. -/
def reprAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@factor_repr)
    (type_of% (realize.{0, 0, 0, 0, 0} sigmaSignature
      (fun _ _ m => ArithmeticFunction.sigma 1 m) (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Arith.Robin.FewDistinctPrimes.factor_repr.audit
  realizationName := `Reg.D5.S3.Arith.Robin.FewDistinctPrimes.reprRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨reprArena⟩
  objectArena := .source ⟨reprArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source reprArena ⟨reprRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0, 0, 0, 0, 0} sigmaSignature
    (fun _ _ m => ArithmeticFunction.sigma 1 m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.FewDistinctPrimes
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

/-- The bound record binds the product of the primes through its raw source path. -/
def boundAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@geomProd_le)
    (type_of% (realize.{0, 0, 0, 0, 0} listSignature (fun _ _ l => l.prod)
      (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Arith.Robin.FewDistinctPrimes.geomProd_le.audit
  realizationName := `Reg.D5.S3.Arith.Robin.FewDistinctPrimes.boundRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨boundArena⟩
  objectArena := .source ⟨boundArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source boundArena ⟨boundRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0, 0, 0, 0, 0} listSignature (fun _ _ l => l.prod)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.FewDistinctPrimes
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Arith.Robin.FewDistinctPrimes
