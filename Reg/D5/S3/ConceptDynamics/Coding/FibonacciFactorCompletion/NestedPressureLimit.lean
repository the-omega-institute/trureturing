import Reg.Support.SingleDependentReadout
import Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook
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

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.ExactOriginal117
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Set (ℤ → CuLetter)
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature := realize.{0,0,0,0,0} observationSignature (fun _ X s => pressure X s) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ X s => pressure X s + 1) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ {X Y : Set (ℤ → CuLetter)} (occupiedX : X.Nonempty) (occupiedY : Y.Nonempty) (incl : X ⊆ Y) (θ : ℝ), r.readout () X θ ≤ pressure Y θ

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := h (X := Set.univ) (Y := Set.univ)
    ⟨(fun _ => .c), Set.mem_univ _⟩ ⟨(fun _ => .c), Set.mem_univ _⟩ (fun _ h => h) 0
  change pressure Set.univ 0 + 1 ≤ pressure Set.univ 0 at impossible
  linarith

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.pressure_mono) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.pressure_mono, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨Set.univ, 0, 1, ?_⟩
    exact ne_of_gt (pressure_strictAnti Set.univ ⟨(fun _ => .c), Set.mem_univ _⟩ (by norm_num : (0 : ℝ) < 1))

def pressure_mono_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.pressure_mono)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ X s => pressure X s) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.ExactOriginal117.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.ExactOriginal117.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature (fun _ X s => pressure X s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms pressure_mono_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.ExactOriginal117

open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.SetWitness

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit


open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open Bilateral ResetFactors ResetCodebook MemoryGraph SpectralBoundary InteriorRoot WordWeightRegrouping
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Filter Topology
open scoped ENNReal NNReal

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.ExactOriginal115
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => List CuLetter
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => Set (ℤ → CuLetter)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature := realize.{0,0,0,0,0} observationSignature (fun _ _ w => anchoredCylinder w) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => ∅) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (Y : ℕ → Set (ℤ → CuLetter))
    (compact : ∀ j, IsCompact (Y j)) (decreasing : Antitone Y)
    (shift : ∀ j (ω : ℤ → CuLetter), ω ∈ Y j → ∀ a : ℤ,
      (fun i => ω (i + a)) ∈ Y j) (w : List CuLetter) (persistent : ∀ j, ∃ ω ∈ Y j, Occurs ω w),
    ∃ ω ∈ ⋂ j, Y j, ω ∈ r.readout () () w

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  let Y : ℕ → Set (ℤ → CuLetter) := fun _ => {fun _ => CuLetter.u}
  have compact : ∀ j, IsCompact (Y j) := fun _ => isCompact_singleton
  have decreasing : Antitone Y := fun _ _ _ => Set.Subset.rfl
  have shift : ∀ j (ω : ℤ → CuLetter), ω ∈ Y j → ∀ a : ℤ,
      (fun i => ω (i + a)) ∈ Y j := by
    intro j ω hω a
    change ω = (fun _ => CuLetter.u) at hω
    subst ω
    rfl
  have persistent : ∀ j, ∃ ω ∈ Y j, Occurs ω [] := by
    intro j
    exact ⟨fun _ => CuLetter.u, rfl, 0, fun k => Fin.elim0 k⟩
  obtain ⟨ω, _, impossible⟩ := h Y compact decreasing shift [] persistent
  exact impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.persistent_word_intersection) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.persistent_word_intersection, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), [], [CuLetter.c], ?_⟩
    change anchoredCylinder [] ≠ anchoredCylinder [CuLetter.c]
    have yes : (fun _ : ℤ => CuLetter.u) ∈ anchoredCylinder [] := fun k => Fin.elim0 k
    intro eq
    have bad := (eq ▸ yes) ⟨0, by norm_num⟩
    cases bad

def persistent_word_intersection_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.persistent_word_intersection)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ _ w => anchoredCylinder w) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.ExactOriginal115.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.ExactOriginal115.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature (fun _ _ w => anchoredCylinder w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms persistent_word_intersection_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.ExactOriginal115


open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open Bilateral ResetFactors ResetCodebook MemoryGraph SpectralBoundary InteriorRoot WordWeightRegrouping
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Filter Topology
open scoped ENNReal NNReal

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.ExactOriginal116
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := ℕ → Set (ℤ → CuLetter)
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => Set (ℤ → CuLetter)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature := realize.{0,0,0,0,0} observationSignature (fun _ Y j => Y j) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => ∅) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (Y : ℕ → Set (ℤ → CuLetter))
    (compact : ∀ j, IsCompact (Y j)) (decreasing : Antitone Y)
    (shift : ∀ j (ω : ℤ → CuLetter), ω ∈ Y j → ∀ a : ℤ,
      (fun i => ω (i + a)) ∈ Y j) (k : ℕ), ∃ J : ℕ, ∀ j ≥ J, ∀ w : List CuLetter, w.length = k →
    ((∃ ω ∈ r.readout () Y j, Occurs ω w) ↔ (∃ ω ∈ ⋂ m, Y m, Occurs ω w))

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  let Y : ℕ → Set (ℤ → CuLetter) := fun _ => {fun _ => CuLetter.u}
  have compact : ∀ j, IsCompact (Y j) := fun _ => isCompact_singleton
  have decreasing : Antitone Y := fun _ _ _ => Set.Subset.rfl
  have shift : ∀ j (ω : ℤ → CuLetter), ω ∈ Y j → ∀ a : ℤ,
      (fun i => ω (i + a)) ∈ Y j := by
    intro j ω hω a
    change ω = (fun _ => CuLetter.u) at hω
    subst ω
    rfl
  obtain ⟨J, eventual⟩ := h Y compact decreasing shift 0
  have yes : ∃ ω ∈ ⋂ m, Y m, Occurs ω [] :=
    ⟨fun _ => CuLetter.u, Set.mem_iInter.mpr (fun _ => rfl), 0, fun k => Fin.elim0 k⟩
  obtain ⟨ω, impossible, _⟩ := (eventual J le_rfl [] rfl).mpr yes
  exact impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.nested_language_stabilization) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.nested_language_stabilization, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(fun j => if j = 0 then {fun _ : ℤ => CuLetter.u} else ∅), 0, 1, ?_⟩
    simp [actual, realize]

def nested_language_stabilization_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.nested_language_stabilization)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ Y j => Y j) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.ExactOriginal116.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.ExactOriginal116.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature (fun _ Y j => Y j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "body", "body", "body", "body", "fn", "arg", "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms nested_language_stabilization_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.ExactOriginal116


open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open Bilateral ResetFactors ResetCodebook MemoryGraph SpectralBoundary InteriorRoot WordWeightRegrouping
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Filter Topology
open scoped ENNReal NNReal

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.ExactOriginal120
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Σ _ : ℕ, ℝ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => Set (ℤ → CuLetter)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature := realize.{0,0,0,0,0} observationSignature (fun _ p K => MemoryLanguage .upper p.1 K p.2) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => ∅) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (n K : ℕ) (d : ℝ) (positive : 1 ≤ K),
    (r.readout () ⟨n,d⟩ K).Nonempty ∧
    IsClosed (MemoryLanguage .upper n K d) ∧
    IsCompact (MemoryLanguage .upper n K d) ∧
    (∀ (ω : ℤ → CuLetter), ω ∈ MemoryLanguage .upper n K d → ∀ a : ℤ,
      (fun i => ω (i+a)) ∈ MemoryLanguage .upper n K d)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  obtain ⟨ω, impossible⟩ := (h 0 1 0 le_rfl).1
  exact impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.upper_memory_subshift) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.upper_memory_subshift, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    exact ⟨⟨0, hSide .high + 1⟩, 1, 2, upper_separation⟩

def upper_memory_subshift_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.upper_memory_subshift)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ p K => MemoryLanguage .upper p.1 K p.2) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.ExactOriginal120.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.ExactOriginal120.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature (fun _ p K => MemoryLanguage .upper p.1 K p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms upper_memory_subshift_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.ExactOriginal120

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.LimitSources
noncomputable section
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
abbrev observationSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature (ℕ → Set (ℤ → CuLetter)) (fun _ => ℕ) (fun _ => Set (ℤ → CuLetter))
def actual : Realization observationSignature :=
  realize observationSignature (fun _ Y j => Y j) (fun e => nomatch e)
theorem dependence : ObservationalDependence observationSignature actual := by
  intro i
  refine ⟨(fun j => if j = 0 then {fun _ : ℤ => CuLetter.u} else ∅), 0, 1, ?_⟩
  simp [actual, realize]
def singletonSequence : ℕ → Set (ℤ → CuLetter) := fun _ => {fun _ => CuLetter.u}
theorem singleton_shift : ∀ j (ω : ℤ → CuLetter), ω ∈ singletonSequence j → ∀ a : ℤ,
    (fun i => ω (i + a)) ∈ singletonSequence j := by
  intro j ω hω a
  change ω = (fun _ => CuLetter.u) at hω
  subst ω; rfl
abbrev pressureArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (Y : ℕ → Set (ℤ → CuLetter))
    (compact : ∀ j, IsCompact (Y j)) (occupied : ∀ j, (Y j).Nonempty)
    (decreasing : Antitone Y)
    (shift : ∀ j (ω : ℤ → CuLetter), ω ∈ Y j → ∀ a : ℤ, (fun i => ω (i + a)) ∈ Y j) (θ : ℝ),
    (⋂ j, r.readout () Y j).Nonempty ∧ Antitone (fun j => pressure (Y j) θ) ∧
    (⨅ j, pressure (Y j) θ) = pressure (⋂ j, Y j) θ ∧
    Tendsto (fun j => pressure (Y j) θ) atTop (𝓝 (pressure (⋂ j, Y j) θ))
def emptyRejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => ∅) (fun e => nomatch e)
theorem pressure_rejected_law : ¬ pressureArena.Law emptyRejected := by
  intro law
  obtain ⟨ω, hω⟩ := (law singletonSequence (fun _ => isCompact_singleton)
    (fun _ => ⟨fun _ => CuLetter.u, rfl⟩) (fun _ _ _ => Set.Subset.rfl) singleton_shift 0).1
  exact Set.mem_iInter.mp hω 0
def pressureEvidence : Registration pressureArena (type_of% @nested_pressure_limit) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@nested_pressure_limit, emptyRejected, pressure_rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity pressureArena.Law actual emptyRejected pressure_rejected_law
  dependence := dependence
theorem empty_rate : weightedFactorRate (∅ : Set (ℤ → CuLetter)) = 0 := by
  have counts (T : ℕ) : factorCount (∅ : Set (ℤ → CuLetter)) T = 0 := by
    letI : IsEmpty (FactorDictionary (∅ : Set (ℤ → CuLetter)) T) :=
      ⟨fun w => by obtain ⟨ω, hω, _⟩ := w.property.1; exact hω⟩
    exact Nat.card_of_isEmpty
  simp [weightedFactorRate, counts]
def rateRejected : Realization observationSignature :=
  realize observationSignature (fun _ _ j => if j = 0 then ∅ else MemoryLanguage .upper 0 2 0) (fun e => nomatch e)
abbrev rateArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (Y : ℕ → Set (ℤ → CuLetter))
    (compact : ∀ j, IsCompact (Y j)) (occupied : ∀ j, (Y j).Nonempty)
    (decreasing : Antitone Y)
    (shift : ∀ j (ω : ℤ → CuLetter), ω ∈ Y j → ∀ a : ℤ, (fun i => ω (i + a)) ∈ Y j),
    Antitone (fun j => weightedFactorRate (r.readout () Y j)) ∧
    Tendsto (fun j => weightedFactorRate (Y j)) atTop (𝓝 (weightedFactorRate (⋂ j, Y j)))
theorem rate_rejected_law : ¬ rateArena.Law rateRejected := by
  intro law
  have bad := (law singletonSequence (fun _ => isCompact_singleton)
    (fun _ => ⟨fun _ => CuLetter.u, rfl⟩) (fun _ _ _ => Set.Subset.rfl) singleton_shift).1
    (show (0 : ℕ) ≤ 1 by decide)
  change weightedFactorRate (MemoryLanguage .upper 0 2 0) ≤ weightedFactorRate (∅ : Set (ℤ → CuLetter)) at bad
  rw [empty_rate] at bad
  have pos := original_positive_weighted_rate .upper 0 2 0 le_rfl
  linarith
def rateEvidence : Registration rateArena (type_of% @nested_rate_limit) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@nested_rate_limit, rateRejected, rate_rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity rateArena.Law actual rateRejected rate_rejected_law
  dependence := dependence
abbrev upperSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℝ → Set (ℤ → CuLetter))
def upperActual : Realization upperSignature :=
  realize upperSignature (fun _ n K => MemoryLanguage .upper n K) (fun e => nomatch e)
abbrev upperArena : Arena.{0,0,0,0,0} where
  signature := upperSignature
  Law r := ∀ (K : ℕ) (d : ℝ) (positive : 1 ≤ K),
    Antitone (fun n => weightedFactorRate (r.readout () n K d)) ∧
    Tendsto (fun n => weightedFactorRate (MemoryLanguage .upper n K d)) atTop
      (𝓝 (weightedFactorRate (AuxiliaryLanguage K d)))
def upperRejected : Realization upperSignature :=
  realize _ (fun _ n _ _ => if n = 0 then ∅ else MemoryLanguage .upper 0 2 0) (fun e => nomatch e)
theorem upper_rejected_law : ¬ upperArena.Law upperRejected := by
  intro law
  have bad := (law 1 0 le_rfl).1 (show (0 : ℕ) ≤ 1 by decide)
  change weightedFactorRate (MemoryLanguage .upper 0 2 0) ≤ weightedFactorRate (∅ : Set (ℤ → CuLetter)) at bad
  rw [empty_rate] at bad
  have pos := original_positive_weighted_rate .upper 0 2 0 le_rfl
  linarith
def upperEvidence : Registration upperArena (type_of% @original_upper_rate_limit) where
  actual := upperActual
  bridge := Iff.rfl
  variation := ⟨@original_upper_rate_limit, upperRejected, upper_rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity upperArena.Law
    upperActual upperRejected upper_rejected_law
  dependence := by
    intro i
    refine ⟨0, 1, 2, ?_⟩
    intro eq
    exact Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.SetWitness.upper_separation
      (congrFun eq (hSide .high + 1))
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.LimitSources

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.LimitSources.Pressure
noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.nested_pressure_limit)
    (type_of% Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.LimitSources.actual) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.LimitSources.Pressure.unit, realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.LimitSources.pressureEvidence, realizationSource := none, generated := false,
  arena := .source ⟨Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.LimitSources.pressureArena⟩, objectArena := .source ⟨Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.LimitSources.pressureArena⟩, catalog := Lean.Name.anonymous, localNames := false,
  realization := .source Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.LimitSources.pressureArena ⟨Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.LimitSources.pressureEvidence⟩, correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize.{0,0,0,0,0} Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.LimitSources.observationSignature (fun _ Y j => Y j) (fun e => nomatch e)), variation := .absent, sensitivity := .absent,
  partialSensitivity := none, escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "arg", "body", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.LimitSources.Pressure

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.LimitSources.Rate
noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.nested_rate_limit)
    (type_of% Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.LimitSources.actual) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.LimitSources.Rate.unit, realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.LimitSources.rateEvidence, realizationSource := none, generated := false,
  arena := .source ⟨Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.LimitSources.rateArena⟩, objectArena := .source ⟨Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.LimitSources.rateArena⟩, catalog := Lean.Name.anonymous, localNames := false,
  realization := .source Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.LimitSources.rateArena ⟨Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.LimitSources.rateEvidence⟩, correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize.{0,0,0,0,0} Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.LimitSources.observationSignature (fun _ Y j => Y j) (fun e => nomatch e)), variation := .absent, sensitivity := .absent,
  partialSensitivity := none, escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "fn", "arg", "arg", "body", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.LimitSources.Rate

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.LimitSources.UpperRate
noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.original_upper_rate_limit)
    (type_of% upperActual) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.LimitSources.UpperRate.unit, realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.LimitSources.upperEvidence, realizationSource := none, generated := false,
  arena := .source ⟨Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.LimitSources.upperArena⟩, objectArena := .source ⟨Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.LimitSources.upperArena⟩, catalog := Lean.Name.anonymous, localNames := false,
  realization := .source Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.LimitSources.upperArena ⟨Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.LimitSources.upperEvidence⟩, correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize.{0,0,0,0,0} Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.LimitSources.upperSignature (fun _ n K => MemoryLanguage .upper n K) (fun e => nomatch e)), variation := .absent, sensitivity := .absent,
  partialSensitivity := none, escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit, definition := none, coordinates := #[3], readouts := #[{ path := #["body", "body", "body", "fn", "arg", "arg", "body", "arg", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit.LimitSources.UpperRate
