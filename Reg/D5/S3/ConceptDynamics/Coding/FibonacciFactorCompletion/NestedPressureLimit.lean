import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open Bilateral MemoryGraph SpectralBoundary InteriorRoot ActualCountRateBridge ResetFactors
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Filter Topology
open scoped ENNReal NNReal

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit
noncomputable section

def budgetLower : ℝ := lam - g^2 * chi^2 * hSide .high
def budgetUpper : ℝ := lam - g^2 * chi^2 * (aSide .high / (1-rho*chi^2))
def budget : ℝ := (budgetLower + budgetUpper) / 2

theorem budget_interval : budgetLower < budget ∧ budget < budgetUpper := by
  have gp : 0 < g := TailGeometry.tail_arithmetic.2.2.2.1
  have g1 : g < 1 := TailGeometry.tail_arithmetic.2.2.2.2.1
  have rp : 0 < rho := by dsimp [rho]; positivity
  have r1 : rho < 1 := by
    dsimp [rho]
    exact pow_lt_one₀ gp.le g1 (by decide : (6 : ℕ) ≠ 0)
  have cp : 0 < chi := by dsimp [chi]; positivity
  have c1 : chi < 1 := by
    dsimp [chi]
    exact pow_lt_one₀ gp.le g1 (by decide : (20 : ℕ) ≠ 0)
  have c2 : chi^2 < 1 := pow_lt_one₀ cp.le c1 (by decide : (2 : ℕ) ≠ 0)
  have den : 0 < 1-rho*chi^2 := by nlinarith [sq_nonneg chi]
  have hs : 0 < hSide .high := by dsimp [hSide]; linarith
  have quotient : aSide .high / (1-rho*chi^2) < hSide .high := by
    apply (div_lt_iff₀ den).mpr
    dsimp [aSide]
    nlinarith [mul_pos rp hs, mul_lt_mul_of_pos_left c2 (mul_pos rp hs)]
  have coef : 0 < g^2*chi^2 := by positivity
  have hmul := mul_lt_mul_of_pos_left quotient coef
  dsimp [budgetLower, budgetUpper, budget]
  constructor <;> linarith

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
    (hqb : lam - g^2 * chi^K * hSide .high < b)
    (hbp : b < lam - g^2 * chi^K * (aSide .high / (1-rho*chi^K))),
    ∃ roots : MemorySide → ℕ → ℝ,
      (∀ side n, K ≤ n → 0 < roots side n ∧ roots side n < 1 ∧
        R.readout () ⟨o, ⟨b, ⟨K, ⟨side, n⟩⟩⟩⟩ (roots side n) = 1 ∧
        weightedFactorRate (MemoryLanguage side n K ((lam-b)/g^2/chi^K)) =
          -Real.logb 2 (roots side n)) ∧
      (∀ n, K ≤ n → -Real.logb 2 (roots .lower n) ≤ eta_b K b ∧
        eta_b K b ≤ -Real.logb 2 (roots .upper n)) ∧
      MonotoneOn (fun n => -Real.logb 2 (roots .lower n)) (Set.Ici K) ∧
      AntitoneOn (fun n => -Real.logb 2 (roots .upper n)) (Set.Ici K) ∧
      Tendsto (fun n => -Real.logb 2 (roots .upper n)) atTop (𝓝 (eta_b K b)) ∧
      (∀ model strict, actualRate model K ((lam-b)/g^2/chi^K) strict = eta_b K b)

theorem root_rejected_law : ¬ rootArena.Law rootRejected := by
  intro h
  have hh := h (fun _ => false) budget 2 (by omega)
    budget_interval.1 budget_interval.2
  obtain ⟨roots, properties, rest⟩ := hh
  have eq := (properties .upper 2 le_rfl).2.2.1
  norm_num [rootRejected, realize] at eq

def rootRegistration : Registration rootArena (rootArena.Law rootActual) where
  actual := rootActual
  bridge := Iff.rfl
  variation := ⟨D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.original_upper_root_limit, rootRejected, root_rejected_law⟩
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

def original_upper_root_limit_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.original_upper_root_limit)
      (type_of% (realize.{0,0,0,0,0} rootSignature (fun _ p z => weightedRadius p.2.2.2.1 p.2.2.2.2 p.2.2.1 ((lam-p.2.1)/g^2/chi^p.2.2.1) z) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.original_upper_root_limit_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.rootRegistration
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
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit
    definition := none
    coordinates := #[0, 1, 2, 7, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "fn", "arg", "body", "body", "body", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms rootRegistration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit
