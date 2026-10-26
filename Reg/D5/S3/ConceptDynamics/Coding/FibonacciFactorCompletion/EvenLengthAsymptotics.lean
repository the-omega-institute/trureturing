import Reg.Support.FibonacciFactorCompletion.ResetExecutionWord
import Reg.Support.FibonacciOriginalSourceWitness.EvenLimits
import Reg.Support.FibonacciObservationCountWitness
import Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge
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

abbrev weightSignature : Signature where
  Params := Unit
  State _ := List Return
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def weightActual : Realization weightSignature :=
  realize.{0,0,0,0,0} weightSignature (fun _ _ xs => listWeight xs) (fun e => nomatch e)
def weightRejected : Realization weightSignature := realize.{0,0,0,0,0} weightSignature
  (fun _ _ _ => 1) (fun e => nomatch e)

abbrev weightArena : Arena where
  signature := weightSignature
  Law R := ∀ (xs : List Return), Even (R.readout () () xs)

theorem weight_rejected_law : ¬ weightArena.Law weightRejected := by
  intro h
  exact (by decide : ¬ Even (1 : ℕ)) (h [])

def weightRegistration : Registration weightArena
    (type_of% (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.actual_list_weight_even)) where
  actual := weightActual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.actual_list_weight_even,
    weightRejected, weight_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨weightRejected, ?_, rfl, weight_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), [], [⟨1, 1, Nat.zero_lt_one, Nat.zero_lt_one⟩], ?_⟩
    change (0 : ℕ) ≠ 26
    decide

def actual_list_weight_even_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.actual_list_weight_even)
      (type_of% (realize.{0,0,0,0,0} weightSignature (fun _ _ xs => listWeight xs) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.actual_list_weight_even_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.weightRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨weightArena⟩
  objectArena := .source ⟨weightArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source weightArena ⟨weightRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} weightSignature (fun _ _ xs => listWeight xs) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms weightRegistration

abbrev fillerSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def fillerActual : Realization fillerSignature :=
  realize.{0,0,0,0,0} fillerSignature (fun _ _ F => fillerJ F) (fun e => nomatch e)
def fillerRejected : Realization fillerSignature := realize.{0,0,0,0,0} fillerSignature
  (fun _ _ _ => 0) (fun e => nomatch e)

abbrev fillerArena : Arena where
  signature := fillerSignature
  Law R := ∀ (F : ℕ) (even : Even F) (large : 78 ≤ F),
    1 ≤ R.readout () () F ∧ fillerJ F ≤ 3 ∧
    (∀ i : ℕ, 1 ≤ i → i ≤ 3 → F / 2 % 3 = i % 3 → i = fillerJ F) ∧
    F / 2 % 3 = fillerJ F % 3 ∧ 13 * fillerJ F ≤ F / 2 ∧
    3 ∣ F / 2 - 13 * fillerJ F ∧
    26 * fillerJ F + 6 * fillerQ F = F ∧
    listWeight (lowFiller F) = F ∧
    (∀ a ∈ lowFiller F, a.r = 1) ∧
    (∀ (K : ℕ), 2 ≤ K → ∀ (d : ℝ) (strict : Bool) (j : Side) (D : ℝ),
      GuardTrace K d strict j (lowFiller F) D)

theorem filler_rejected_law : ¬ fillerArena.Law fillerRejected := by
  intro h
  have impossible := (h 78 ⟨39, rfl⟩ le_rfl).1
  change 1 ≤ (0 : ℕ) at impossible
  omega

def fillerRegistration : Registration fillerArena
    (type_of% (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.low_filler_geometry)) where
  actual := fillerActual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.low_filler_geometry,
    fillerRejected, filler_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨fillerRejected, ?_, rfl, filler_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 78, 80, ?_⟩
    change fillerJ 78 ≠ fillerJ 80
    decide

def low_filler_geometry_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.low_filler_geometry)
      (type_of% (realize.{0,0,0,0,0} fillerSignature (fun _ _ F => fillerJ F) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.low_filler_geometry_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.fillerRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨fillerArena⟩
  objectArena := .source ⟨fillerArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source fillerArena ⟨fillerRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} fillerSignature (fun _ _ F => fillerJ F) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms fillerRegistration

abbrev paddingSignature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def paddingActual : Realization paddingSignature :=
  realize.{0,0,0,0,0} paddingSignature (fun _ L T => paddingWeight L T) (fun e => nomatch e)
def paddingRejected : Realization paddingSignature := realize.{0,0,0,0,0} paddingSignature
  (fun _ _ _ => 1) (fun e => nomatch e)

abbrev paddingArena : Arena where
  signature := paddingSignature
  Law R := ∀ (L : ℕ) (positive : 0 < L) (evenL : Even L)
    (T : ℕ) (large : 78 ≤ T) (evenT : Even T),
    Even (R.readout () L T) ∧ 78 ≤ paddingWeight L T ∧
    paddingWeight L T < 78 + L ∧
    paddingCopies L T * L + paddingWeight L T = T

theorem padding_rejected_law : ¬ paddingArena.Law paddingRejected := by
  intro h
  exact (by decide : ¬ Even (1 : ℕ))
    (h 2 (Nat.zero_lt_succ 1) ⟨1, rfl⟩ 78 le_rfl ⟨39, rfl⟩).1

def paddingRegistration : Registration paddingArena
    (type_of% (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.even_padding_arithmetic)) where
  actual := paddingActual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.even_padding_arithmetic,
    paddingRejected, padding_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨paddingRejected, ?_, rfl, padding_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨4, 78, 80, ?_⟩
    change paddingWeight 4 78 ≠ paddingWeight 4 80
    decide

def even_padding_arithmetic_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.even_padding_arithmetic)
      (type_of% (realize.{0,0,0,0,0} paddingSignature (fun _ L T => paddingWeight L T) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.even_padding_arithmetic_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.paddingRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨paddingArena⟩
  objectArena := .source ⟨paddingArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source paddingArena ⟨paddingRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} paddingSignature (fun _ L T => paddingWeight L T) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms paddingRegistration

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.ExactOriginal62
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Σ _ : Model, Σ _ : ℕ, Σ _ : ℝ, Bool
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ p T => actualCount p.1 p.2.1 p.2.2.1 p.2.2.2 T) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (T : ℕ) (odd : Odd T),
    (∀ (model : Model) (K : ℕ) (d : ℝ) (strict : Bool),
      r.readout () ⟨model, K, d, strict⟩ T = 0) ∧
    (∀ (model : Model) (o : Ownership) (b : ℝ) (contract : Contract),
      contractCount model o b contract T = 0)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := (h 1 (by decide)).1 .original 2 0 false
  exact (by decide : (1 : ℕ) ≠ 0) impossible

def evidence : Registration sourceArena
    (type_of% (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.odd_actual_counts)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.odd_actual_counts, rejected, rejected_law⟩
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
    refine ⟨⟨Model.original, 2, 0, false⟩, 0, 1, ?_⟩
    change actualCount .original 2 0 false 0 ≠ actualCount .original 2 0 false 1
    rw [(odd_actual_counts 1 (by decide)).1]
    exact Nat.ne_of_gt
      (Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal31.zero_count_positive
        .original 2 0 false (by decide))

def odd_actual_counts_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.odd_actual_counts)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ p T => actualCount p.1 p.2.1 p.2.2.1 p.2.2.2 T) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.ExactOriginal62.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.ExactOriginal62.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature (fun _ p T => actualCount p.1 p.2.1 p.2.2.1 p.2.2.2 T) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics
    definition := none
    coordinates := #[2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms odd_actual_counts_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.ExactOriginal62

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.ExactOriginal63
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ T => T) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (o : Ownership) (b : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K)))
    (T : ℕ) (even : Even T) (large : 78 ≤ T) ,
    listWeight (lowFiller T) = r.readout () () T ∧
    (∀ (model : Model) (contract : Contract),
      ActualPairSupply model o b contract (lowFiller T) ∧
      0 < contractCount model o b contract T) ∧
    (∀ (model : Model) (strict : Bool),
      0 < actualCount model K ((lam - b) / g ^ 2 / chi ^ K) strict T ∧
      actualLogRate model K ((lam - b) / g ^ 2 / chi ^ K) strict T =
        Real.logb 2 (actualCount model K ((lam - b) / g ^ 2 / chi ^ K) strict T : ℝ) / (T : ℝ))


theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have weight := (low_filler_geometry 78 ⟨39, by decide⟩ (by decide)).2.2.2.2.2.2.2.1
  have impossible := (h (fun _ => false) budget 2 (by decide)
    budget_interval.1 budget_interval.2 78 ⟨39, by decide⟩ (by decide)).1
  change listWeight (lowFiller 78) = 0 at impossible
  omega

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.even_actual_positivity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.even_actual_positivity, rejected, rejected_law⟩
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
    exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def even_actual_positivity_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.even_actual_positivity)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ T => T) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.ExactOriginal63.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.ExactOriginal63.evidence
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
    (fun _ _ T => T) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms even_actual_positivity_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.ExactOriginal63

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.ExactOriginal61
noncomputable section

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
  (resetConcatenation)

open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal150
  (observationSignature actual)
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ResetBudgetReadout
  (rejected reset_floor_rejected)

/-- The complete source law observes the one budget occurrence in the reset threshold. -/
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (o : Ownership) (b : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K))),
    ∃ R : Return, R.r = 1 ∧
    max (max (xSide .high) (ySide .high)) ((lam - r.readout () () b) / g ^ 2 / chi ^ K) <
      hSide .high - rho ^ R.m * (hSide .high - chi * aSide .high) ∧
    ∀ (sourceModel : Model) (N : ℕ), 0 < N →
      1 ≤ actualCount sourceModel K ((lam - b) / g ^ 2 / chi ^ K) false N →
    let d := (lam - b) / g ^ 2 / chi ^ K
    let delta := hSide .high - rho ^ R.m * (hSide .high - chi * aSide .high) -
      initial .high sourceModel
    let gamma := delta * g ^ N
    let eps := min (b - actualAutomaticCost K) (g ^ 2 * chi ^ K * gamma) / 2
    let V := {xs : List Return //
      GuardTrace K d false .high xs (initial .high sourceModel) ∧ listWeight xs = N}
    let L := N + 20 + 6 * R.m
    Even N ∧ Even L ∧ 0 < L ∧ 0 < delta ∧ 0 < gamma ∧ 0 < eps ∧
    ∀ (targetModel : Model) (T : ℕ), 78 ≤ T → Even T →
    let k := paddingCopies L T
    let F := paddingWeight L T
    Even F ∧ 78 ≤ F ∧ F < 78 + L ∧ k * L + F = T ∧
    Function.Injective (fun z : Fin k → V =>
      paddedExecution R (List.ofFn (fun i => (z i).val)) F) ∧
    (∀ z : Fin k → V,
      let execution := paddedExecution R (List.ofFn (fun i => (z i).val)) F
      listWeight execution = T ∧
      GuardTrace K (d + gamma) false .high execution (initial .high targetModel) ∧
      ActualPairSupply targetModel o (b - eps) .strict execution ∧
      (∀ contract : Contract, ActualPairSupply targetModel o b contract execution) ∧
      (∀ (before : List Return) (a : Return) (after : List Return),
        execution = before ++ a :: after → a.r = K →
        ∃ rest, resetConcatenation R (List.ofFn (fun i => (z i).val)) =
          before ++ a :: rest) ∧
      (∀ side : Side, externalWord side execution =
        externalWord side (lowFiller F) ++
          externalWord side (resetConcatenation R (List.ofFn (fun i => (z i).val))))) ∧
    (∀ strict : Bool,
      actualCount sourceModel K d false N ^ k ≤ actualCount targetModel K d strict T) ∧
    (∀ contract : Contract,
      actualCount sourceModel K d false N ^ k ≤ contractCount targetModel o b contract T) ∧
    Function.Injective (fun z : Fin k → V =>
      history targetModel (paddedExecution R (List.ofFn (fun i => (z i).val)) F)) ∧
    (∀ side : Side, Function.Injective (fun z : Fin k → V =>
      source side targetModel (paddedExecution R (List.ofFn (fun i => (z i).val)) F)))

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  obtain ⟨R, _, floor, _⟩ :=
    h (fun _ => false) budget 2 le_rfl budget_interval.1 budget_interval.2
  exact reset_floor_rejected R floor

def evidence : Registration sourceArena
    (type_of% @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.same_reset_all_even_counts) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.same_reset_all_even_counts, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal150.evidence.dependence

def same_reset_all_even_counts_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.same_reset_all_even_counts)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ state => state) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.ExactOriginal61.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.ExactOriginal61.evidence
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
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics
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
#print axioms same_reset_all_even_counts_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.ExactOriginal61


namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.ExactOriginal65
noncomputable section

open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal150
  (observationSignature actual)
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ResetBudgetReadout
  (rejected reset_floor_rejected)

/-- The complete source law observes the one budget occurrence in the reset threshold. -/
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (o : Ownership) (b : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K))),
    (∀ (T : ℕ), Odd T →
      (∀ (model : Model) (strict : Bool),
        actualCount model K ((lam - b) / g ^ 2 / chi ^ K) strict T = 0) ∧
      (∀ (model : Model) (contract : Contract), contractCount model o b contract T = 0)) ∧
    (∀ (T : ℕ), Even T → 78 ≤ T →
      listWeight (lowFiller T) = T ∧
      (∀ (model : Model) (contract : Contract),
        ActualPairSupply model o b contract (lowFiller T) ∧
        0 < contractCount model o b contract T) ∧
      (∀ (model : Model) (strict : Bool),
        0 < actualCount model K ((lam - b) / g ^ 2 / chi ^ K) strict T ∧
        actualLogRate model K ((lam - b) / g ^ 2 / chi ^ K) strict T =
          Real.logb 2 (actualCount model K ((lam - b) / g ^ 2 / chi ^ K) strict T : ℝ) / (T : ℝ))) ∧
    ∃ R : Return, R.r = 1 ∧
    max (max (xSide .high) (ySide .high)) ((lam - r.readout () () b) / g ^ 2 / chi ^ K) <
      hSide .high - rho ^ R.m * (hSide .high - chi * aSide .high) ∧
    ∀ (sourceModel : Model) (N : ℕ), 0 < N →
      1 ≤ actualCount sourceModel K ((lam - b) / g ^ 2 / chi ^ K) false N →
    let d := (lam - b) / g ^ 2 / chi ^ K
    let a := actualCount sourceModel K d false N
    let L := N + 20 + 6 * R.m
    Even N ∧ Even L ∧ 0 < L ∧
    (∀ (targetModel : Model) (T : ℕ), 78 ≤ T → Even T →
      (∀ strict : Bool, a ^ paddingCopies L T ≤ actualCount targetModel K d strict T) ∧
      ∀ contract : Contract, a ^ paddingCopies L T ≤ contractCount targetModel o b contract T) ∧
    (∀ (targetModel : Model) (strict : Bool), Real.logb 2 (a : ℝ) / (L : ℝ) ≤
      liminf (fun v : ℕ => actualLogRate targetModel K d strict (2 * v)) atTop)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  obtain ⟨R, _, floor, _⟩ :=
    (h (fun _ => false) budget 2 le_rfl budget_interval.1 budget_interval.2).2.2
  exact reset_floor_rejected R floor

def evidence : Registration sourceArena
    (type_of% @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.original_finite_even_bridge) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.original_finite_even_bridge, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal150.evidence.dependence

def original_finite_even_bridge_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.original_finite_even_bridge)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ state => state) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.ExactOriginal65.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.ExactOriginal65.evidence
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
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "body", "arg", "fn", "arg", "fn", "arg", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_finite_even_bridge_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.ExactOriginal65


namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.ObservedCountCorrespondence
noncomputable section

def actual_observation_count_correspondence_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.actual_observation_count_correspondence)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ p T => historyImageCount p.1 p.2.1 p.2.2.1 p.2.2.2
          (observationOffset p.1 + T)) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.ObservedCountCorrespondence.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.ObservedCountCorrespondence.evidence
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
    (fun _ p T => historyImageCount p.1 p.2.1 p.2.2.1 p.2.2.2
      (observationOffset p.1 + T)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms actual_observation_count_correspondence_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.ObservedCountCorrespondence
open Reg.Support.FibonacciOriginalSourceWitness.EvenLimits.Floor in
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.full_even_floor_ratio_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0} (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.full_even_floor_ratio)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ L v => (paddingCopies L (2 * v) : ℝ) / ((2 * v : ℕ) : ℝ)) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.full_even_floor_ratio_registration_unit, realizationName := `Reg.Support.FibonacciOriginalSourceWitness.EvenLimits.Floor.evidence,
  realizationSource := none, generated := false, arena := .source ⟨sourceArena⟩,
  objectArena := .source ⟨sourceArena⟩, catalog := Lean.Name.anonymous, localNames := false,
  realization := .source sourceArena ⟨evidence⟩, correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize.{0,0,0,0,0} observationSignature (fun _ L v => (paddingCopies L (2 * v) : ℝ) / ((2 * v : ℕ) : ℝ)) (fun e => nomatch e)), variation := .absent,
  sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "fn", "fn", "arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
open Reg.Support.FibonacciOriginalSourceWitness.EvenLimits.ContractRate in
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.contract_even_raw_asymptotics_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0} (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.contract_even_raw_asymptotics)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ p v => Real.logb 2 (contractCount p.2.2.2.1 p.1 p.2.1 p.2.2.2.2 (2 * v) : ℝ) / ((2 * v : ℕ) : ℝ)) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.contract_even_raw_asymptotics_registration_unit, realizationName := `Reg.Support.FibonacciOriginalSourceWitness.EvenLimits.ContractRate.evidence,
  realizationSource := none, generated := false, arena := .source ⟨sourceArena⟩,
  objectArena := .source ⟨sourceArena⟩, catalog := Lean.Name.anonymous, localNames := false,
  realization := .source sourceArena ⟨evidence⟩, correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize.{0,0,0,0,0} observationSignature (fun _ p v => Real.logb 2 (contractCount p.2.2.2.1 p.1 p.2.1 p.2.2.2.2 (2 * v) : ℝ) / ((2 * v : ℕ) : ℝ)) (fun e => nomatch e)), variation := .absent,
  sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics, definition := none, coordinates := #[0, 1, 2, 6, 7], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn", "arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
open Reg.Support.FibonacciOriginalSourceWitness.EvenLimits.Reindexing in
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.observation_even_reindexing_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0} (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.observation_even_reindexing)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ model v => observationOffset model + 2 * v) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.observation_even_reindexing_registration_unit, realizationName := `Reg.Support.FibonacciOriginalSourceWitness.EvenLimits.Reindexing.evidence,
  realizationSource := none, generated := false, arena := .source ⟨sourceArena⟩,
  objectArena := .source ⟨sourceArena⟩, catalog := Lean.Name.anonymous, localNames := false,
  realization := .source sourceArena ⟨evidence⟩, correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize.{0,0,0,0,0} observationSignature (fun _ model v => observationOffset model + 2 * v) (fun e => nomatch e)), variation := .absent,
  sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "arg", "fn", "arg", "fn", "fn", "arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
open Reg.Support.FibonacciFactorCompletion.ResetExecutionWord in noncomputable def Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.reset_execution_word_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0} (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.reset_execution_word) (type_of% (realize.{0,0,0,0,0} signature (fun _ _ words => words) (fun e => nomatch e))) Unit Unit :=
  { unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.reset_execution_word_registration_unit, realizationName := `Reg.Support.FibonacciFactorCompletion.ResetExecutionWord.evidence, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨evidence⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize.{0,0,0,0,0} signature (fun _ _ words => words) (fun e => nomatch e)), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "fn", "arg", "arg", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
