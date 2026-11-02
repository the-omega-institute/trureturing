import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.FinitePrimeValuationEnvelopes
import Reg.Support.SingleDependentReadout
import Reg.D5.S3.Arith.Robin.GA2ForcedPrimeSource

set_option autoImplicit false

set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Weil.FinitePrimeValuationEnvelopes

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.FinitePrimeValuationEnvelopes
open _root_.D5.S3.Arith.Robin.PaddingRatio (robinRatio)
open LeanInformationAudit
open scoped BigOperators

abbrev signature := _root_.Reg.D5.S3.Arith.Robin.GA2ForcedPrimeSource.signature
abbrev actual := _root_.Reg.D5.S3.Arith.Robin.GA2ForcedPrimeSource.actual

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (2 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (S : Finset ℕ), (∀ p ∈ S, p.Prime) →
    ∀ (A : ℕ → ℕ) (ε : ℝ), 0 < ε →
      ∃ N ≥ 5041, ∀ n ≥ N, (∀ p ∈ S, n.factorization p ≤ A p) →
        R.readout () () n ≤ (∏ p ∈ S, (1 - (p : ℝ)⁻¹ ^ (A p + 1))) + ε

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨N, _, hN⟩ := h ∅ (by simp) (fun _ => 0) (1 / 2) (by norm_num)
  have hbad := hN N le_rfl (by simp)
  change (2 : ℝ) ≤ 1 + (1 / 2 : ℝ) at hbad
  norm_num at hbad

def family : Registration arena
    (type_of%
      @_root_.D5.S3.Weil.FinitePrimeValuationEnvelopes.bounded_finite_prime_valuation_robin_ratio) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨
    _root_.D5.S3.Weil.FinitePrimeValuationEnvelopes.bounded_finite_prime_valuation_robin_ratio,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := _root_.Reg.D5.S3.Arith.Robin.GA2ForcedPrimeSource.actual_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Weil.FinitePrimeValuationEnvelopes.bounded_finite_prime_valuation_robin_ratio
    )
    (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Weil.FinitePrimeValuationEnvelopes.bounded_finite_prime_valuation_robin_ratio.__information_unit
  realizationName := `Reg.D5.S3.Weil.FinitePrimeValuationEnvelopes.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => robinRatio n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.FinitePrimeValuationEnvelopes
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms rejected_law
#print axioms family
#print axioms audit

end Reg.D5.S3.Weil.FinitePrimeValuationEnvelopes
