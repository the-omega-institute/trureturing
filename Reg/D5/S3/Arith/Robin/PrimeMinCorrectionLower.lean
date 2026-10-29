import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.PrimeMinCorrectionLower
import Reg.Support.DependentFamily

/-! The threshold observation keeps the complete uniform integer telescope. -/

set_option autoImplicit false

namespace Reg.D5.S3.Arith.Robin.PrimeMinCorrectionLower

open _root_.D5.S3.Arith.Robin.PrimeMinCorrectionLower
open _root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail
open _root_.D5.S3.Weil.GronwallLowerEnvelope
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
  realize signature (fun _ _ A => A) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev scope := type_of% (@uniform_min_tail_robin_lower)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ε c : ℝ}, 0 < ε → 0 < c → ∃ A : ℝ,
    1 < R.readout () () A ∧ ∀ m : ℕ, 0 < m →
      m.primeFactors = Nat.primesLE (largestPrime m) →
      1 < θ (largestPrime m) → A ≤ Real.log (m : ℝ) →
      c * Real.log (m : ℝ) ≤ largestPrime m →
      (2 * Real.sqrt 2 - ε) /
          (Real.sqrt (Real.log (m : ℝ)) * Real.log (Real.log (m : ℝ))) <
        tail m + Real.log (Real.log (Real.log (m : ℝ))) -
          Real.log (Real.log (θ (largestPrime m))) ∧
      (2 * Real.sqrt 2 - ε) /
          (Real.sqrt (Real.log (m : ℝ)) * Real.log (Real.log (m : ℝ))) +
          Mertens.E₃ (largestPrime m) + Real.log (Real.log (θ (largestPrime m))) -
          Real.log (Real.log (largestPrime m)) < robinLogMargin m

theorem source_bridge : scope ↔ arena.Law actual := Iff.rfl

theorem actual_law : arena.Law actual := @uniform_min_tail_robin_lower

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨A, hA, _⟩ := h (ε := 1) (c := 1) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hA

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
    (@uniform_min_tail_robin_lower) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PrimeMinCorrectionLower.uniform_min_tail_robin_lower.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PrimeMinCorrectionLower.family
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
    owner := `D5.S3.Arith.Robin.PrimeMinCorrectionLower
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Arith.Robin.PrimeMinCorrectionLower
