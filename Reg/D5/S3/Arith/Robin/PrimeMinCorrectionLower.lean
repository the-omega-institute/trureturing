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
  Law R := ∀ {ε : ℝ}, 0 < ε → ∃ A : ℝ,
    1 < R.readout () () A ∧ ∀ m : ℕ, 0 < m →
      m.primeFactors = Nat.primesLE (largestPrime m) →
      1 < θ (largestPrime m) → A ≤ Real.log (m : ℝ) →
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
  obtain ⟨A, hA, _⟩ := h (ε := 1) (by norm_num)
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
      path := #["body", "body", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

namespace ConsumedPrimeWeight

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
  realize signature (fun _ _ x => x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev scope := type_of% (@prime_weight_lower)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {X U D : ℝ}, 1 < X → 0 < D → X * Real.log X ≤ D →
    U^2 * Real.log U ≤ D → ∀ {p : ℕ}, p.Prime → (p:ℝ) ≤ U →
    Real.log p / D ≤ R.readout () ()
      (min (Real.log p / (X*Real.log X)) (-Real.log (1-(p:ℝ)⁻¹^2)))

theorem source_bridge : scope ↔ arena.Law actual := Iff.rfl

theorem actual_law : arena.Law actual := @prime_weight_lower

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hh := h (X := 2) (U := 2) (D := 4*Real.log 2) (by norm_num)
    (by positivity) (by nlinarith) (by norm_num) (p := 2) (by norm_num) (by norm_num)
  change Real.log (2:ℝ)/(4*Real.log 2) ≤ -1 at hh
  have hn : 0 ≤ Real.log (2:ℝ)/(4*Real.log 2) := by positivity
  linarith

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
    (@prime_weight_lower) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PrimeMinCorrectionLower.prime_weight_lower.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PrimeMinCorrectionLower.ConsumedPrimeWeight.family
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
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := some #[]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end ConsumedPrimeWeight

end Reg.D5.S3.Arith.Robin.PrimeMinCorrectionLower
