import Reg.Support.FibonacciOriginalSourceWitness.LowChoices
import Reg.Support.FibonacciOriginalSourceWitness.Source106
import Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit
import Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open Bilateral MemoryGraph SpectralBoundary InteriorRoot ActualCountRateBridge ResetFactors
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Filter Topology
open scoped ENNReal NNReal

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit
noncomputable section

open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit (budget budget_interval budgetLower budgetUpper)

abbrev rootSignature : Signature where
  Params := Σ _ : Ownership, Σ _ : ℝ, Σ _ : ℕ, Σ _ : MemorySide, ℕ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def rootActual : Realization rootSignature := realize rootSignature
  (fun _ p z => weightedRadius p.2.2.2.1 p.2.2.2.2 p.2.2.1
    ((lam-p.2.1)/g^2/chi^p.2.2.1) z) (fun e => nomatch e)
def rootRejected : Realization rootSignature := realize rootSignature
  (fun _ _ _ => 0) (fun e => nomatch e)

abbrev rootArena : Arena where
  signature := rootSignature
  Law R := ∀ (o : Ownership) (b : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K))),
    (1:ℝ) / 58 ≤ eta_b K b ∧
    Monotone (fun n => weightedFactorRate
      (MemoryLanguage .lower n K ((lam - b) / g ^ 2 / chi ^ K))) ∧
    (∀ epsilon : ℝ, 0 < epsilon → ∃ n0 : ℕ, K ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → eta_b K b - epsilon < weightedFactorRate
        (MemoryLanguage .lower n K ((lam - b) / g ^ 2 / chi ^ K)) ∧
        weightedFactorRate (MemoryLanguage .lower n K ((lam - b) / g ^ 2 / chi ^ K)) ≤ eta_b K b) ∧
    Tendsto (fun n => weightedFactorRate
      (MemoryLanguage .lower n K ((lam - b) / g ^ 2 / chi ^ K))) atTop (𝓝 (eta_b K b)) ∧
    ∃ roots : MemorySide → ℕ → ℝ,
      (∀ side n, K ≤ n → 0 < roots side n ∧ roots side n < 1 ∧
        R.readout () ⟨o, ⟨b, ⟨K, ⟨side, n⟩⟩⟩⟩ (roots side n) = 1 ∧
        weightedFactorRate (MemoryLanguage side n K ((lam - b) / g ^ 2 / chi ^ K)) =
          -Real.logb 2 (roots side n)) ∧
      (∀ n, K ≤ n →
        -Real.logb 2 (roots .lower n) ≤ eta_b K b ∧
        eta_b K b ≤ -Real.logb 2 (roots .upper n)) ∧
      MonotoneOn (fun n => -Real.logb 2 (roots .lower n)) (Set.Ici K) ∧
      AntitoneOn (fun n => -Real.logb 2 (roots .upper n)) (Set.Ici K) ∧
      Tendsto (fun n => -Real.logb 2 (roots .upper n)) atTop (𝓝 (eta_b K b)) ∧
      Tendsto (fun n => -Real.logb 2 (roots .lower (n + K))) atTop (𝓝 (eta_b K b)) ∧
      (∀ model strict,
        actualRate model K ((lam - b) / g ^ 2 / chi ^ K) strict = eta_b K b)

theorem root_rejected_law : ¬ rootArena.Law rootRejected := by
  intro h
  have hh := h (fun _ => false) budget 2 (by omega)
    budget_interval.1 budget_interval.2
  obtain ⟨roots, properties, rest⟩ := hh.2.2.2.2
  have eq := (properties .upper 2 le_rfl).2.2.1
  norm_num [rootRejected, realize] at eq

def rootRegistration : Registration rootArena (rootArena.Law rootActual) where
  actual := rootActual
  bridge := Iff.rfl
  variation := ⟨D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit.original_lower_rate_limit, rootRejected, root_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rootRejected, ?_, rfl, root_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨(fun _ => false), ⟨0, ⟨2, ⟨.upper, 2⟩⟩⟩⟩, 0, 1, ?_⟩
    change weightedRadius .upper 2 2 ((lam-0)/g^2/chi^2) 0 ≠
      weightedRadius .upper 2 2 ((lam-0)/g^2/chi^2) 1
    have zero := (original_adjacency_zero_continuous .upper 2 2 ((lam-0)/g^2/chi^2)).1
    have positive := original_spectral_positive .upper 2 2 ((lam-0)/g^2/chi^2) 1 (by norm_num)
    intro eq
    simp only [weightedRadius, zero, spectrum.spectralRadius_zero] at eq
    unfold weightedRadius at positive
    rw [← eq] at positive
    norm_num at positive

def original_lower_rate_limit_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit.original_lower_rate_limit)
      (type_of% (realize.{0,0,0,0,0} rootSignature (fun _ p z => weightedRadius p.2.2.2.1 p.2.2.2.2 p.2.2.1 ((lam-p.2.1)/g^2/chi^p.2.2.1) z) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit.original_lower_rate_limit_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit.rootRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨rootArena⟩
  objectArena := .source ⟨rootArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rootArena ⟨rootRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} rootSignature (fun _ p z => weightedRadius p.2.2.2.1 p.2.2.2.2 p.2.2.1 ((lam-p.2.1)/g^2/chi^p.2.2.1) z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit
    definition := none
    coordinates := #[0, 1, 2, 7, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg", "body", "fn", "arg", "body", "body", "body", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms rootRegistration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit.ExactOriginal105
noncomputable section

open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.RateReadout
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit
  (budget budget_interval)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (model : Model) (o : Ownership) (b : ℝ)
    (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K))) (strict : Bool),
    (1:ℝ) / 58 ≤ r.readout () model K ((lam - b) / g ^ 2 / chi ^ K) strict

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have bound := h .original (fun _ => false) budget 2 le_rfl budget_interval.1 budget_interval.2 false
  change (1 : ℝ) / 58 ≤ 0 at bound
  norm_num at bound

def evidence : Registration sourceArena (type_of% @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit.actual_rate_positive) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit.actual_rate_positive, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def actual_rate_positive_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit.actual_rate_positive)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ model K => actualRate model K) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit.ExactOriginal105.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit.ExactOriginal105.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ model K => actualRate model K) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms actual_rate_positive_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit.ExactOriginal105

namespace Reg.Support.FibonacciOriginalSourceWitness.Source106
noncomputable section

def original_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit.original_count_codebook_approximation)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ R => R.r) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.Support.FibonacciOriginalSourceWitness.Source106.original_unit
  realizationName := `Reg.Support.FibonacciOriginalSourceWitness.Source106.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ R => R.r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_registration
end
end Reg.Support.FibonacciOriginalSourceWitness.Source106

open Reg.Support.FibonacciOriginalSourceWitness.LowChoices in
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit.actual_low_choice_count_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0} (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit.actual_low_choice_count)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ q z => _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit.lowChoices (q := q) z) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit.actual_low_choice_count_registration_unit, realizationName := `Reg.Support.FibonacciOriginalSourceWitness.LowChoices.evidence,
  realizationSource := none, generated := false, arena := .source ⟨sourceArena⟩,
  objectArena := .source ⟨sourceArena⟩, catalog := Lean.Name.anonymous, localNames := false,
  realization := .source sourceArena ⟨evidence⟩, correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize.{0,0,0,0,0} observationSignature (fun _ q z => _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit.lowChoices (q := q) z) (fun e => nomatch e)), variation := .absent,
  sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit, definition := none, coordinates := #[7], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
