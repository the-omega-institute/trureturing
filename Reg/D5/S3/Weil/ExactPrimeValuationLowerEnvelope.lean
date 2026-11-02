import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ExactPrimeValuationLowerEnvelope
import Reg.Support.SingleDependentReadout
import Reg.D5.S3.Arith.Robin.GA2ForcedPrimeSource

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Weil.ExactPrimeValuationLowerEnvelope

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.ExactPrimeValuationLowerEnvelope
open LeanInformationAudit
open scoped BigOperators

abbrev signature := _root_.Reg.D5.S3.Arith.Robin.GA2ForcedPrimeSource.signature
abbrev actual := _root_.Reg.D5.S3.Arith.Robin.GA2ForcedPrimeSource.actual

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (S : Finset ℕ), (∀ p ∈ S, p.Prime) →
    ∀ (A : ℕ → ℕ) (ε : ℝ), 0 < ε → ∀ N : ℕ,
      ∃ m ≥ max N 5041, (∀ p ∈ S, m.factorization p = A p) ∧
        (∏ p ∈ S, (1 - (p : ℝ)⁻¹ ^ (A p + 1))) - ε ≤ R.readout () () m

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨m, _, _, hm⟩ := h ∅ (by simp) (fun _ => 0) (1 / 2) (by norm_num) 0
  norm_num [rejected, realize] at hm

def family : Registration arena
    (type_of% @_root_.D5.S3.Weil.ExactPrimeValuationLowerEnvelope.exact_finite_prime_valuation_robin_lower_envelope) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨
    _root_.D5.S3.Weil.ExactPrimeValuationLowerEnvelope.exact_finite_prime_valuation_robin_lower_envelope,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := _root_.Reg.D5.S3.Arith.Robin.GA2ForcedPrimeSource.actual_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Weil.ExactPrimeValuationLowerEnvelope.exact_finite_prime_valuation_robin_lower_envelope)
    (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Weil.ExactPrimeValuationLowerEnvelope.exact_finite_prime_valuation_robin_lower_envelope.__information_unit
  realizationName := `Reg.D5.S3.Weil.ExactPrimeValuationLowerEnvelope.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ExactPrimeValuationLowerEnvelope
    definition := none
    coordinates := #[]
    readouts := #[{
      -- Six source foralls, the existential witness lambda, the two right
      -- conjunction clauses, then the inequality's actual right operand.
      path := #["body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "arg", "arg"]
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

end Reg.D5.S3.Weil.ExactPrimeValuationLowerEnvelope
