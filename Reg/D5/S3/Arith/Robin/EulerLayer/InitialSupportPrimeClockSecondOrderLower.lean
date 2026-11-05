import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.EulerLayer.InitialSupportPrimeClockSecondOrderLower
import Reg.Support.DependentFamily

/-! The threshold observation preserves the full uniform P-clock telescope. -/

set_option autoImplicit false

namespace Reg.D5.S3.Arith.Robin.EulerLayer.InitialSupportPrimeClockSecondOrderLower

open _root_.D5.S3.Arith.Robin
open _root_.D5.S3.Arith.Robin.EulerLayer.InitialSupportPrimeClockSecondOrderLower
open _root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped Chebyshev

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ P₀ => P₀) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev scope := type_of% (@initial_support_prime_clock_second_order_lower)

abbrev arena : Arena where
  signature := signature
  Law R :=
    ∀ ε : ℝ, 0 < ε →
      ∃ P₀ : ℝ, 1 < R.readout () () P₀ ∧
        ∀ m P : ℕ, 0 < m →
          P = largestPrime m →
          m.primeFactors = Nat.primesLE P →
          1 < Chebyshev.theta (P : ℝ) →
          P₀ ≤ (P : ℝ) →
          Real.log (P : ℝ) *
              (Real.sqrt (P : ℝ) * Real.log (P : ℝ) *
                  (OriginalEndpointPrimeTail.tail m +
                    Real.log (Real.log (Real.log (m : ℝ))) -
                    Real.log (Real.log (Chebyshev.theta (P : ℝ)))) -
                2 * Real.sqrt 2) +
              Real.sqrt 2 * (2 + Real.log 2) > -ε

theorem source_bridge : scope ↔ arena.Law actual := Iff.rfl

theorem actual_law : arena.Law actual := @initial_support_prime_clock_second_order_lower

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨P₀, hP₀, _⟩ := h 1 (by norm_num)
  norm_num [rejected, realize] at hP₀

def family : Registration arena scope where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@initial_support_prime_clock_second_order_lower) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.EulerLayer.InitialSupportPrimeClockSecondOrderLower.initial_support_prime_clock_second_order_lower.audit
  realizationName := `Reg.D5.S3.Arith.Robin.EulerLayer.InitialSupportPrimeClockSecondOrderLower.family
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
    owner := `D5.S3.Arith.Robin.EulerLayer.InitialSupportPrimeClockSecondOrderLower
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end
end Reg.D5.S3.Arith.Robin.EulerLayer.InitialSupportPrimeClockSecondOrderLower
