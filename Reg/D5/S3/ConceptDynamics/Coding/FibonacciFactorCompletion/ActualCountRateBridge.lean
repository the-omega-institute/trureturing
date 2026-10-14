import Reg.Support.FibonacciFactorCompletion.CountBoundsReadouts
import Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit
import Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit
import Reg.Support.SingleDependentReadout
import Reg.Support.FibonacciFactorWitnesses
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal31
noncomputable section

open Reg.Support.FibonacciFactorWitnesses

def actual_dictionary_bound_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.actual_dictionary_bound)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ N => 3^(N+1)) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal31.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal31.evidence
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
    (fun _ _ N => 3^(N+1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms actual_dictionary_bound_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal31

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal33
noncomputable section

open Reg.Support.FibonacciFactorWitnesses

def no_c_factor_card_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.no_c_factor_card)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ q N => Nat.card (NoCFactor q.1 q.2 N)) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal33.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal33.evidence
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
    (fun _ q N => Nat.card (NoCFactor q.1 q.2 N)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms no_c_factor_card_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal33

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal39
noncomputable section

open Reg.Support.FibonacciFactorWitnesses
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal31

def contract_count_correspondence_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.contract_count_correspondence)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ N => N) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal39.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal39.evidence
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
    (fun _ _ N => N) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms contract_count_correspondence_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal39

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.RateReadout
noncomputable section

open Reg.Support.SingleDependentReadout
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit
  (budget budget_interval)

abbrev observationSignature : Signature.{0,0,0,0,0} :=
  signature Model (fun _ => ℕ) (fun _ => ℝ → Bool → ℝ)

def actual : Realization observationSignature :=
  realize observationSignature (fun _ model K => actualRate model K) (fun e => nomatch e)

def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ _ _ => 0) (fun e => nomatch e)

/-- At cutoff zero every admissible execution is empty, for every weight and guard. -/
theorem cutoff_zero_rate (model : Model) (d : ℝ) (strict : Bool) :
    actualRate model 0 d strict = 0 := by
  have empty (N : ℕ) (xs : ActualDictionary model 0 d strict N) : xs.val = [] := by
    have guard := xs.property.1
    cases h : xs.val with
    | nil => rfl
    | cons a rest =>
      rw [h] at guard
      have bound : a.r ≤ 0 := guard.1
      have positive := a.r_pos
      omega
  have rates : actualLogRate model 0 d strict = fun _ => 0 := by
    funext N
    letI : Subsingleton (ActualDictionary model 0 d strict N) :=
      ⟨fun xs ys => Subtype.ext ((empty N xs).trans (empty N ys).symm)⟩
    have bound : actualCount model 0 d strict N ≤ 1 := by
      simpa [actualCount] using
        (Nat.card_le_card_of_injective (fun _ : ActualDictionary model 0 d strict N => ())
          (fun _ _ _ => Subsingleton.elim _ _))
    simp [actualLogRate, max_eq_left bound]
  rw [actualRate, rates, Filter.limsup_const]

theorem dependence : ObservationalDependence observationSignature actual := by
  intro i
  refine ⟨.original, 0, 2, ?_⟩
  intro eq
  have values := congrFun (congrFun eq ((lam - budget) / g ^ 2 / chi ^ 2)) false
  change actualRate .original 0 _ false = actualRate .original 2 _ false at values
  rw [cutoff_zero_rate] at values
  have positive :=
    _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit.actual_rate_positive
      .original (fun _ => false) budget 2 le_rfl budget_interval.1 budget_interval.2 false
  linarith

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.RateReadout

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal37
noncomputable section

open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.RateReadout
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit
  (budget budget_interval)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (o : Ownership) (b : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K)))
    (src dst : Model),
    r.readout () src K ((lam - b) / g ^ 2 / chi ^ K) false =
      actualRate dst K ((lam - b) / g ^ 2 / chi ^ K) true

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have eq := h (fun _ => false) budget 2 le_rfl budget_interval.1 budget_interval.2 .original .original
  change 0 = actualRate .original 2 ((lam - budget) / g ^ 2 / chi ^ 2) true at eq
  have positive :=
    _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit.actual_rate_positive
      .original (fun _ => false) budget 2 le_rfl budget_interval.1 budget_interval.2 true
  linarith

def evidence : Registration sourceArena (type_of% @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.actual_rates_equal) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.actual_rates_equal, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def actual_rates_equal_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.actual_rates_equal)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ model K => actualRate model K) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal37.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal37.evidence
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
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge
    definition := none
    coordinates := #[6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms actual_rates_equal_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal37

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal38
noncomputable section

open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.RateReadout
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit
  (budget budget_interval)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (o : Ownership) (b : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K)))
    (model : Model) (strict : Bool),
    r.readout () model K ((lam - b) / g ^ 2 / chi ^ K) strict =
      weightedFactorRate (AuxiliaryLanguage K ((lam - b) / g ^ 2 / chi ^ K))

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have eq := h (fun _ => false) budget 2 le_rfl budget_interval.1 budget_interval.2 .original false
  change 0 = weightedFactorRate (AuxiliaryLanguage 2 ((lam - budget) / g ^ 2 / chi ^ 2)) at eq
  have bridge := actual_auxiliary_rate_bridge (fun _ => false) budget 2 le_rfl
    budget_interval.1 budget_interval.2 .original false
  have positive :=
    _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit.actual_rate_positive
      .original (fun _ => false) budget 2 le_rfl budget_interval.1 budget_interval.2 false
  linarith

def evidence : Registration sourceArena (type_of% @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.actual_auxiliary_rate_bridge) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.actual_auxiliary_rate_bridge, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def actual_auxiliary_rate_bridge_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.actual_auxiliary_rate_bridge)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ model K => actualRate model K) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal38.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal38.evidence
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
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge
    definition := none
    coordinates := #[6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms actual_auxiliary_rate_bridge_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal38

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal40
noncomputable section

open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.RateReadout
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit
  (budget budget_interval)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (o : Ownership) (b : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K))),
    weightedFactorRate (AuxiliaryLanguage K ((lam - b) / g ^ 2 / chi ^ K)) = eta_b K b ∧
    (∀ (model : Model) (strict : Bool),
      r.readout () model K ((lam - b) / g ^ 2 / chi ^ K) strict = eta_b K b) ∧
    (∀ (model : Model) (contract : Contract), contractRate model o b contract = eta_b K b)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have eq := (h (fun _ => false) budget 2 le_rfl budget_interval.1 budget_interval.2).2.1 .original false
  change 0 = actualRate .original 2 ((lam - budget) / g ^ 2 / chi ^ 2) false at eq
  have positive :=
    _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit.actual_rate_positive
      .original (fun _ => false) budget 2 le_rfl budget_interval.1 budget_interval.2 false
  linarith

def evidence : Registration sourceArena (type_of% @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.original_actual_count_rate_bridge) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.original_actual_count_rate_bridge, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def original_actual_count_rate_bridge_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.original_actual_count_rate_bridge)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ model K => actualRate model K) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal40.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal40.evidence
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
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge
    definition := none
    coordinates := #[6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "body", "body", "fn", "arg", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_actual_count_rate_bridge_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal40

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal30
noncomputable section

/-- The state is the exact type of the literal original data operand. -/
abbrev FunctionState := type_of% @actualToFactor
abbrev Parameters := Σ _ : Model, Σ _ : ℕ, Σ _ : ℝ, Σ _ : Bool, ℕ

abbrev observationSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature Parameters (fun _ => FunctionState)
    (fun p => ∀ (_ : 1 ≤ p.2.1),
      ActualDictionary p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 →
        FactorDictionary (AuxiliaryLanguage p.2.1 p.2.2.1) p.2.2.2.2)

def actual : Realization observationSignature :=
  realize observationSignature
    (fun _ p f => f p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
    (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (model : Model) (K : ℕ) (d : ℝ) (strict : Bool) (N : ℕ)
    (hK : 1 ≤ K),
    Function.Injective ((r.readout () ⟨model, K, d, strict, N⟩ actualToFactor) hK)

private def smallReturn : Return := ⟨1, 1, by decide, by decide⟩
private def largeReturn : Return := ⟨2, 2, by decide, by decide⟩

/-- The two lists inhabit the complete dictionary for every threshold and model. -/
private def doubleDictionary (model : Model) (d : ℝ) (strict : Bool) :
    ActualDictionary model 3 d strict 52 :=
  ⟨[smallReturn, smallReturn], by
    constructor
    · simp [GuardTrace, smallReturn]
    · norm_num [listWeight, smallReturn]⟩

private def singleDictionary (model : Model) (d : ℝ) (strict : Bool) :
    ActualDictionary model 3 d strict 52 :=
  ⟨[largeReturn], by
    constructor
    · simp [GuardTrace, largeReturn]
    · norm_num [listWeight, largeReturn]⟩

private theorem dictionaries_distinct (model : Model) (d : ℝ) (strict : Bool) :
    doubleDictionary model d strict ≠ singleDictionary model d strict := by
  intro h
  have lengths := congrArg (fun x : ActualDictionary model 3 d strict 52 => x.val.length) h
  norm_num [doubleDictionary, singleDictionary] at lengths

/-- Collapse only an explicitly inhabited fiber; identity handles every other fiber. -/
private def collapse (model : Model) (K : ℕ) (d : ℝ) (strict : Bool) (N : ℕ)
    (x : ActualDictionary model K d strict N) : ActualDictionary model K d strict N :=
  if hK : K = 3 then
    if hN : N = 52 then by
      subst K N
      exact doubleDictionary model d strict
    else x
  else x

private def collapsedFunction : FunctionState :=
  fun model K d strict N hK x =>
    actualToFactor model K d strict N hK (collapse model K d strict N x)

private def rejected : Realization observationSignature :=
  realize observationSignature
    (fun _ p _ => collapsedFunction p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
    (fun e => nomatch e)

private theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have inj := h .original 3 0 false 52 (by decide)
  apply dictionaries_distinct .original 0 false
  apply inj
  simp [rejected, realize, collapsedFunction, collapse]

private theorem dependence : ObservationalDependence observationSignature actual := by
  intro i
  refine ⟨⟨.original, 3, 0, false, 52⟩, actualToFactor, collapsedFunction, ?_⟩
  intro h
  have eq := congrFun (congrFun h (by decide : 1 ≤ 3))
    (singleDictionary .original 0 false)
  change actualToFactor .original 3 0 false 52 (by decide) (singleDictionary .original 0 false) =
    actualToFactor .original 3 0 false 52 (by decide)
      (collapse .original 3 0 false 52 (singleDictionary .original 0 false)) at eq
  have same := actual_to_factor_injective .original 3 0 false 52 (by decide) eq
  simp only [collapse, dif_pos rfl] at same
  exact dictionaries_distinct .original 0 false same.symm

def evidence : Registration sourceArena (type_of% @actual_to_factor_injective) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_to_factor_injective, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def actual_to_factor_injective_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.actual_to_factor_injective)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ p f => f p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
        (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal30.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal30.evidence
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
    (fun _ p f => f p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "fn", "fn", "fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms actual_to_factor_injective_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal30

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal35
noncomputable section
open Filter

abbrev observationSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature Model (fun _ => ℕ)
    (fun _ => ℝ → Bool → ℕ → ℝ)

def actual : Realization observationSignature :=
  realize observationSignature (fun _ model K => actualLogRate model K) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

/-- The first log-rate occurrence is observed; the eventual upper-bound clause
retains its original sequence. -/
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (model : Model) (K : ℕ) (d : ℝ) (strict : Bool) (hK : 1 ≤ K),
    (∀ N, 0 ≤ r.readout () model K d strict N) ∧
    IsBoundedUnder (· ≤ ·) atTop (actualLogRate model K d strict)

private theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have bad := (h .original 1 0 false (by decide)).1 0
  norm_num [rejected, realize] at bad

/-- Equal log-rate functions give equal defining limsup rates, so the existing
actual rate nonconstancy witnesses nonconstancy of the original log-rate data. -/
private theorem dependence : ObservationalDependence observationSignature actual := by
  intro i
  obtain ⟨model, K, L, different⟩ := Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.RateReadout.dependence ()
  refine ⟨model, K, L, ?_⟩
  intro same
  apply different
  change actualRate model K = actualRate model L
  funext d strict
  change limsup (actualLogRate model K d strict) atTop =
    limsup (actualLogRate model L d strict) atTop
  apply congrArg (fun f : ℕ → ℝ => limsup f atTop)
  exact congrFun (congrFun same d) strict

def evidence : Registration sourceArena
    (type_of% @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.actual_log_rate_bounds) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.actual_log_rate_bounds, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def actual_log_rate_bounds_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.actual_log_rate_bounds)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ model K => actualLogRate model K) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal35.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal35.evidence
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
    (fun _ model K => actualLogRate model K) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "body", "arg", "fn", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms actual_log_rate_bounds_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal35

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal36
noncomputable section
open Filter
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.RateReadout
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit
  (budget budget_interval)

/-- Only the original rate on the right of the limsup equality is observed.
Both shifted normalized sequences and their eventual bound are retained. -/
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (model : Model) (K : ℕ) (d : ℝ) (strict : Bool) (hK : 1 ≤ K) (C : ℕ),
    IsBoundedUnder (· ≤ ·) atTop (fun N : ℕ =>
      Real.logb 2 ((max 1 (actualCount model K d strict (N + C)) : ℕ) : ℝ) / (N : ℝ)) ∧
    limsup (fun N : ℕ =>
      Real.logb 2 ((max 1 (actualCount model K d strict (N + C)) : ℕ) : ℝ) / (N : ℝ)) atTop =
      r.readout () model K d strict

private theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  let d : ℝ := (lam - budget) / g ^ 2 / chi ^ 2
  have bad := (h .original 2 d false (by decide) 0).2
  have original := (_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.actual_fixed_shift_rate
    .original 2 d false (by decide) 0).2
  have positive :=
    _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit.actual_rate_positive
      .original (fun _ => false) budget 2 le_rfl budget_interval.1 budget_interval.2 false
  change _ = (0 : ℝ) at bad
  rw [original] at bad
  change (1 : ℝ) / 58 ≤ actualRate .original 2 d false at positive
  linarith

def evidence : Registration sourceArena
    (type_of% @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.actual_fixed_shift_rate) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.actual_fixed_shift_rate, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def actual_fixed_shift_rate_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.actual_fixed_shift_rate)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ model K => actualRate model K) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal36.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal36.evidence
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
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms actual_fixed_shift_rate_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal36

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ResetBudgetReadout
noncomputable section

open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal150
  (observationSignature actual)
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit
  (budgetLower)
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply

/-- A whole-family intervention in the one selected lexical budget occurrence. -/
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => budgetLower) (fun e => nomatch e)

/-- The selected threshold reaches H, above every possible reset floor.
The original budget premises are kept separately in each complete law. -/
theorem reset_floor_rejected (R : Return) :
    ¬ max (max (xSide .high) (ySide .high))
        ((lam - budgetLower) / g ^ 2 / chi ^ 2) <
      hSide .high - rho ^ R.m * (hSide .high - chi * aSide .high) := by
  have gp : 0 < g := tail_arithmetic.2.2.2.1
  have cp : 0 < chi := pow_pos gp 20
  have rp : 0 < rho := pow_pos gp 6
  have cancel : (lam - budgetLower) / g ^ 2 / chi ^ 2 = hSide .high := by
    dsimp [budgetLower]
    field_simp [ne_of_gt gp, ne_of_gt cp]
    <;> ring
  have geometry := actual_complete_boundary_geometry .original []
  have lower := (geometry.1 .high 0).1
  have upper := (geometry.2.2.1 .high 0 1 R.m).2.1
  simp only [List.take_nil, execute, initial, pow_one] at lower upper
  have compare := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left lower.le cp.le) (pow_pos rp R.m).le
  have floor_upper : hSide .high - rho ^ R.m * (hSide .high - chi * aSide .high) <
      hSide .high := by nlinarith only [compare, upper]
  have ceiling := le_max_right (max (xSide .high) (ySide .high))
    ((lam - budgetLower) / g ^ 2 / chi ^ 2)
  rw [cancel] at ceiling ⊢
  exact not_lt_of_ge (floor_upper.le.trans ceiling)

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ResetBudgetReadout

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal32
noncomputable section
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal150
  (observationSignature actual)
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ResetBudgetReadout
  (rejected reset_floor_rejected)
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit
  (budget budget_interval)
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply

/-- The complete original law observes only b in the mandatory reset threshold. -/
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (o : Ownership) (b : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K))),
    ∃ R : Return, R.r = 1 ∧
      max (max (xSide .high) (ySide .high)) ((lam - r.readout () () b) / g ^ 2 / chi ^ K) <
        hSide .high - rho ^ R.m * (hSide .high - chi * aSide .high) ∧
      (∀ (src dst : Model) (xs : List Return),
        GuardTrace K ((lam - b) / g ^ 2 / chi ^ K) false .high xs (initial .high src) →
        ActualPairSupply dst o b .strict (R :: xs)) ∧
      (∀ (model : Model) (w : List CuLetter),
        AuxiliaryFactor K ((lam - b) / g ^ 2 / chi ^ K) w → CuLetter.c ∈ w →
        ∃ (a : ℕ) (first : Return) (rest : List Return),
          (if w.getLast? = some CuLetter.c then w ++ [CuLetter.u] else w) =
            List.replicate a CuLetter.u ++ executionWord (first :: rest) ∧
          ActualPairSupply model o b .strict (completedList R a first rest) ∧
          listWeight (completedList R a first rest) = wordWeight w + (20 + 6 * R.m) +
            (if w.getLast? = some CuLetter.c then 12 else 6))

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  obtain ⟨R, _, floor, _⟩ :=
    h (fun _ => false) budget 2 le_rfl budget_interval.1 budget_interval.2
  exact reset_floor_rejected R floor

def evidence : Registration sourceArena (type_of% @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.same_reset_completion) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.same_reset_completion, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal150.evidence.dependence

def same_reset_completion_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.same_reset_completion)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ state => state) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal32.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal32.evidence
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
    (fun _ _ state => state) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "fn", "arg", "fn", "arg", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms same_reset_completion_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal32

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal34
noncomputable section
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal150
  (observationSignature actual)
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ResetBudgetReadout
  (rejected reset_floor_rejected)
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit
  (budget budget_interval)
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply

/-- The complete original law observes only b in the mandatory reset threshold. -/
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (o : Ownership) (b : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K))),
    ∃ R : Return, R.r = 1 ∧
      max (max (xSide .high) (ySide .high)) ((lam - r.readout () () b) / g ^ 2 / chi ^ K) <
        hSide .high - rho ^ R.m * (hSide .high - chi * aSide .high) ∧
      (∀ (src dst : Model) (N : ℕ),
        actualCount src K ((lam - b) / g ^ 2 / chi ^ K) false N ≤
          actualCount dst K ((lam - b) / g ^ 2 / chi ^ K) true (N + (20 + 6 * R.m))) ∧
      (∀ (model : Model) (N : ℕ),
        factorCount (AuxiliaryLanguage K ((lam - b) / g ^ 2 / chi ^ K)) N ≤
          actualCount model K ((lam - b) / g ^ 2 / chi ^ K) true (N + (20 + 6 * R.m) + 6) +
          actualCount model K ((lam - b) / g ^ 2 / chi ^ K) true (N + (20 + 6 * R.m) + 12) + 1)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  obtain ⟨R, _, floor, _⟩ :=
    h (fun _ => false) budget 2 le_rfl budget_interval.1 budget_interval.2
  exact reset_floor_rejected R floor

def evidence : Registration sourceArena (type_of% @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.same_reset_count_comparison) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.same_reset_count_comparison, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal150.evidence.dependence

def same_reset_count_comparison_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.same_reset_count_comparison)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ state => state) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal34.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal34.evidence
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
    (fun _ _ state => state) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "fn", "arg", "fn", "arg", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms same_reset_count_comparison_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal34
