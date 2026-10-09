import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics
import Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open EvenLengthAsymptotics LowerRateLimit ActualCountRateBridge
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit
  (budget budget_interval budgetLower budgetUpper)
open Filter Topology

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics
noncomputable section

abbrev evenSignature : Signature where
  Params := Σ _ : Ownership, Σ _ : ℝ, Σ _ : ℕ, Σ _ : Model, Bool
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def evenActual : Realization evenSignature := realize evenSignature
  (fun _ p v => Real.logb 2 (actualCount p.2.2.2.1 p.2.2.1 ((lam-p.2.1)/g^2/chi^p.2.2.1) p.2.2.2.2 (2*v) : ℝ) / ((2*v : ℕ) : ℝ)) (fun e => nomatch e)
def evenRejected : Realization evenSignature := realize evenSignature
  (fun _ _ _ => 0) (fun e => nomatch e)

abbrev evenArena : Arena where
  signature := evenSignature
  Law R := ∀ (o : Ownership) (b : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K))),
    ∀ (model : Model) (strict : Bool),
      Tendsto (fun v : ℕ => R.readout () ⟨o, ⟨b, ⟨K, ⟨model, strict⟩⟩⟩⟩ v) atTop (𝓝 (eta_b K b)) ∧
      Asymptotics.IsLittleO atTop
        (fun v : ℕ => Real.logb 2
          (actualCount model K ((lam - b) / g ^ 2 / chi ^ K) strict (2 * v) : ℝ) -
          eta_b K b * ((2 * v : ℕ) : ℝ))
        (fun v : ℕ => ((2 * v : ℕ) : ℝ))

theorem even_rejected_law : ¬ evenArena.Law evenRejected := by
  intro h
  have hh := (h (fun _ => false) budget 2 (by omega)
    budget_interval.1 budget_interval.2 .original false).1
  have zero : (0 : ℝ) = eta_b 2 budget :=
    tendsto_nhds_unique tendsto_const_nhds hh
  have lower := (original_lower_rate_limit (fun _ => false) budget 2 (by omega)
    budget_interval.1 budget_interval.2).1
  rw [← zero] at lower
  norm_num at lower

def evenRegistration : Registration evenArena (evenArena.Law evenActual) where
  actual := evenActual
  bridge := Iff.rfl
  variation := ⟨D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.actual_even_raw_asymptotics, evenRejected, even_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨evenRejected, ?_, rfl, even_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨(fun _ => false), ⟨budget, ⟨2, ⟨.original, false⟩⟩⟩⟩, 0, ?_⟩
    by_contra! same
    have zero : ∀ v : ℕ, evenActual.readout i
        ⟨(fun _ => false), ⟨budget, ⟨2, ⟨.original, false⟩⟩⟩⟩ v = 0 := by
      intro v
      rw [← same v]
      simp [evenActual, realize]
    have limit := (actual_even_raw_asymptotics (fun _ => false) budget 2 (by omega)
      budget_interval.1 budget_interval.2 .original false).1
    have limitZero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (eta_b 2 budget)) := by
      convert limit using 1
      funext v
      exact (zero v).symm
    have eq : (0 : ℝ) = eta_b 2 budget :=
      tendsto_nhds_unique tendsto_const_nhds limitZero
    have lower := (original_lower_rate_limit (fun _ => false) budget 2 (by omega)
      budget_interval.1 budget_interval.2).1
    rw [← eq] at lower
    norm_num at lower

def actual_even_raw_asymptotics_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.actual_even_raw_asymptotics)
      (type_of% (realize.{0,0,0,0,0} evenSignature (fun _ p v => Real.logb 2 (actualCount p.2.2.2.1 p.2.2.1 ((lam-p.2.1)/g^2/chi^p.2.2.1) p.2.2.2.2 (2*v) : ℝ) / ((2*v : ℕ) : ℝ)) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.actual_even_raw_asymptotics_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.evenRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨evenArena⟩
  objectArena := .source ⟨evenArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source evenArena ⟨evenRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} evenSignature (fun _ p v => Real.logb 2 (actualCount p.2.2.2.1 p.2.2.1 ((lam-p.2.1)/g^2/chi^p.2.2.1) p.2.2.2.2 (2*v) : ℝ) / ((2*v : ℕ) : ℝ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics
    definition := none
    coordinates := #[0, 1, 2, 6, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evenRegistration

abbrev lengthSignature : Signature where
  Params := Σ _ : Ownership, Σ _ : ℝ, Σ _ : ℕ, Σ _ : Model, Contract
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def lengthActual : Realization lengthSignature := realize lengthSignature
  (fun _ p v => historyImageCount p.2.2.2.1 p.1 p.2.1 p.2.2.2.2 v) (fun e => nomatch e)
def lengthRejected : Realization lengthSignature := realize lengthSignature
  (fun _ _ _ => 1) (fun e => nomatch e)

abbrev lengthArena : Arena where
  signature := lengthSignature
  Law R := ∀ (o : Ownership) (b : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K))),
    ∀ (model : Model) (contract : Contract),
      (∀ Nobs : ℕ, Odd Nobs →
        R.readout () ⟨o, ⟨b, ⟨K, ⟨model, contract⟩⟩⟩⟩ Nobs = 0 ∧
        (∀ side : Side, sourceImageCount side model o b contract Nobs = 0) ∧
        sourcePairImageCount model o b contract Nobs = 0) ∧
      (∀ T : ℕ,
        historyImageCount model o b contract (observationOffset model + T) =
          contractCount model o b contract T ∧
        (∀ side : Side, sourceImageCount side model o b contract (observationOffset model + T) =
          contractCount model o b contract T) ∧
        sourcePairImageCount model o b contract (observationOffset model + T) =
          contractCount model o b contract T) ∧
      (∀ T : ℕ, Even T → 78 ≤ T →
        0 < historyImageCount model o b contract (observationOffset model + T) ∧
        (∀ side : Side, 0 < sourceImageCount side model o b contract (observationOffset model + T)) ∧
        0 < sourcePairImageCount model o b contract (observationOffset model + T)) ∧
      Tendsto (fun v : ℕ => Real.logb 2 (historyImageCount model o b contract (2 * v) : ℝ) /
        ((2 * v : ℕ) : ℝ)) atTop (𝓝 (eta_b K b)) ∧
      Asymptotics.IsLittleO atTop
        (fun v : ℕ => Real.logb 2 (historyImageCount model o b contract (2 * v) : ℝ) -
          eta_b K b * ((2 * v : ℕ) : ℝ))
        (fun v : ℕ => ((2 * v : ℕ) : ℝ)) ∧
      (∀ side : Side,
        Tendsto (fun v : ℕ => Real.logb 2 (sourceImageCount side model o b contract (2 * v) : ℝ) /
          ((2 * v : ℕ) : ℝ)) atTop (𝓝 (eta_b K b)) ∧
        Asymptotics.IsLittleO atTop
          (fun v : ℕ => Real.logb 2 (sourceImageCount side model o b contract (2 * v) : ℝ) -
            eta_b K b * ((2 * v : ℕ) : ℝ))
          (fun v : ℕ => ((2 * v : ℕ) : ℝ))) ∧
      Tendsto (fun v : ℕ => Real.logb 2 (sourcePairImageCount model o b contract (2 * v) : ℝ) /
        ((2 * v : ℕ) : ℝ)) atTop (𝓝 (eta_b K b)) ∧
      Asymptotics.IsLittleO atTop
        (fun v : ℕ => Real.logb 2 (sourcePairImageCount model o b contract (2 * v) : ℝ) -
          eta_b K b * ((2 * v : ℕ) : ℝ))
        (fun v : ℕ => ((2 * v : ℕ) : ℝ))

theorem length_rejected_law : ¬ lengthArena.Law lengthRejected := by
  intro h
  have hh := ((h (fun _ => false) budget 2 (by omega)
    budget_interval.1 budget_interval.2 .original .strict).1 1 (by decide)).1
  norm_num [lengthRejected, realize] at hh

def lengthRegistration : Registration lengthArena (lengthArena.Law lengthActual) where
  actual := lengthActual
  bridge := Iff.rfl
  variation := ⟨D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.actual_observation_length_asymptotics, lengthRejected, length_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨lengthRejected, ?_, rfl, length_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨(fun _ => false), ⟨budget, ⟨2, ⟨.original, .strict⟩⟩⟩⟩,
      1, observationOffset .original + 78, ?_⟩
    have all := actual_observation_length_asymptotics (fun _ => false) budget 2
      (by omega) budget_interval.1 budget_interval.2 .original .strict
    have zero := (all.1 1 (by decide)).1
    have positive := (all.2.2.1 78 (by decide) le_rfl).1
    change historyImageCount .original (fun _ => false) budget .strict 1 ≠
      historyImageCount .original (fun _ => false) budget .strict
        (observationOffset .original + 78)
    rw [zero]
    exact Nat.ne_of_lt positive

def actual_observation_length_asymptotics_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.actual_observation_length_asymptotics)
      (type_of% (realize.{0,0,0,0,0} lengthSignature (fun _ p v => historyImageCount p.2.2.2.1 p.1 p.2.1 p.2.2.2.2 v) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.actual_observation_length_asymptotics_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.lengthRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨lengthArena⟩
  objectArena := .source ⟨lengthArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source lengthArena ⟨lengthRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} lengthSignature (fun _ p v => historyImageCount p.2.2.2.1 p.1 p.2.1 p.2.2.2.2 v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics
    definition := none
    coordinates := #[0, 1, 2, 6, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms lengthRegistration

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics
