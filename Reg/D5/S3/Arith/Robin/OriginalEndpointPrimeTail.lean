import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.OriginalEndpointPrimeTail
import Reg.Support.DependentFamily

/- Candidate only: not compiled or declared_validated. All source clauses
are retained. The selected observation is the actual tail(N) in the FIRST
price lower bound. Other occurrences remain unchanged, as in the source.
The complete-family bad readout depends on real q and natural N; no finite
or artificial state carrier or desired-tail hypothesis is introduced. -/

noncomputable section
set_option autoImplicit false

namespace Reg.D5.S3.Arith.Robin.OriginalEndpointPrimeTail

open Finset
open _root_.D5.S3.Arith.Robin.ActualTwoPriceDefect
open _root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail
open _root_.D5.S3.Weil.GronwallLowerEnvelope
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

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
  realize signature (fun _ _ N => tail N) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature
    (fun _ q N => (∑ p ∈ N.primeFactors, lowerPrice q p) - 1)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {q : ℝ}, 0 < q → ∀ {N : ℕ},
    (N = strictInteger q ∨ N = maximalInteger q) →
    (∑ p ∈ N.primeFactors, lowerPrice q p) ≤ R.readout () q N ∧
      tail N ≤ (∑ p ∈ N.primeFactors, upperPrice q p) ∧
      0 ≤ tail N ∧ tail N ≤ (7 / 2 : ℝ) / Real.sqrt (largestPrime N) ∧
      robinLogMargin N = _root_.Mertens.E₃ (largestPrime N) + tail N +
        Real.log (Real.log (Real.log N)) - Real.log (Real.log (largestPrime N))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h (q := 1) (by norm_num) (N := strictInteger 1) (Or.inl rfl)).1
  change (∑ p ∈ (strictInteger 1).primeFactors, lowerPrice 1 p) ≤
    (∑ p ∈ (strictInteger 1).primeFactors, lowerPrice 1 p) - 1 at hbad
  linarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  have hOne : tail 1 = 0 := by simp [tail]
  have hTwo : tail 2 = -Real.log (3 / 4 : ℝ) := by
    norm_num [tail, layerTail, Nat.prime_two.primeFactors, Nat.prime_two.factorization]
  refine ⟨(1 : ℝ), 1, 2, ?_⟩
  change tail 1 ≠ tail 2
  rw [hOne, hTwo]
  exact ne_of_lt (neg_pos.mpr (Real.log_neg (by norm_num) (by norm_num)))

def family : Registration arena (type_of% (@original_endpoint_prime_tail_supply)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@original_endpoint_prime_tail_supply, rejected, rejected_law⟩
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
    (@original_endpoint_prime_tail_supply)
    (type_of% (realize signature (fun _ _ N => tail N) (fun e => nomatch e)))
    Type Unit where
  unitName := `D5.S3.Arith.Robin.OriginalEndpointPrimeTail.original_endpoint_prime_tail_supply.audit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalEndpointPrimeTail.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ N => tail N) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  -- Exact source state carrier, present in the original telescope/readout.
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.OriginalEndpointPrimeTail
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

/-
Finite theorem registration attempt (unfinished by design).  The exact source
telescope is

  @finite_min_tail_robin_bound : ∀ {m : ℕ}, 0 < m →
    m.primeFactors = Nat.primesLE (largestPrime m) →
    1 < Chebyshev.theta (largestPrime m) →
    (finite min-cost bound) ∧ (Mertens.E₃/robinLogMargin bound).

The mathematical declaration is compiled in the owner module.  A faithful
DependentFamily registration still needs a dependent state carrying m together
with these three premises, an enrolled readout for the conjunction, and a
current sourceSelection path for both consumed output components.  No
Contract.Registration is asserted here, so this attempt is explicitly not
declared_validated and does not claim an audit pass.
-/

end Reg.D5.S3.Arith.Robin.OriginalEndpointPrimeTail
