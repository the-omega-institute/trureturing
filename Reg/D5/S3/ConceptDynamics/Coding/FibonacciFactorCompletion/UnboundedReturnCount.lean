import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount
noncomputable section
open Classical
set_option pp.fullNames true

private theorem count_zero : returnCount 0 = 0 := by
  simpa using (actual_count_middle 0).2
private theorem count_three : returnCount 3 = 0 := by
  simpa using (actual_count_middle 3).2
private theorem count_seven : returnCount 7 = 0 := by
  simpa using (actual_count_middle 7).2
private theorem count_ten : returnCount 10 = 0 := by
  simpa using (actual_count_middle 10).2
private theorem count_thirteen : returnCount 13 = 1 := by
  have h := (actual_count_middle 13).2
  have seed : (middleWords 0).card = 1 := by rw [middleWords]; decide
  simpa [seed] using h

abbrev countSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def countActual : Realization countSignature := realize countSignature
  (fun _ _ n => returnCount n) (fun e => nomatch e)
def countRejected : Realization countSignature := realize countSignature
  (fun _ _ _ => 0) (fun e => nomatch e)

abbrev middleArena : Arena where
  signature := countSignature
  Law R := ∀ n : ℕ, Finite (ReturnFiber n) ∧
    R.readout () () n = if 13 ≤ n then (middleWords (n-13)).card else 0
private theorem middle_rejected : ¬ middleArena.Law countRejected := by
  intro h
  have hh := (h 13).2
  have seed : (middleWords 0).card = 1 := by rw [middleWords]; decide
  norm_num [countRejected, realize, seed] at hh

def middleRegistration : Registration middleArena (middleArena.Law countActual) where
  actual := countActual
  bridge := Iff.rfl
  variation := ⟨actual_count_middle, countRejected, middle_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨countRejected, ?_, rfl, middle_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 13, ?_⟩
    simp [countActual, realize, count_zero, count_thirteen]

abbrev supportArena : Arena where
  signature := countSignature
  Law R := ∀ n : ℕ, 0 < R.readout () () n ↔ ∃ a b : ℕ, n = 13 + 3*a + 10*b
private theorem support_rejected : ¬ supportArena.Law countRejected := by
  intro h
  have hh := (h 13).mpr ⟨0, 0, by omega⟩
  simpa [countRejected, realize] using hh

def supportRegistration : Registration supportArena (supportArena.Law countActual) where
  actual := countActual
  bridge := Iff.rfl
  variation := ⟨actual_count_support, countRejected, support_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨countRejected, ?_, rfl, support_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := middleRegistration.dependence

abbrev recurrenceSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Fin 3
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def recurrenceActual : Realization recurrenceSignature := realize recurrenceSignature
  (fun _ _ n => returnCount n) (fun e => nomatch e)
def recurrenceRejected (i : Fin 3) : Realization recurrenceSignature := realize recurrenceSignature
  (fun j _ n => if j = i then returnCount n + 1 else returnCount n) (fun e => nomatch e)
abbrev recurrenceArena : Arena where
  signature := recurrenceSignature
  Law R := ∀ n : ℕ, R.readout 0 () n =
    (if 3 ≤ n then R.readout 1 () (n-3) else 0) +
    (if 10 ≤ n then R.readout 2 () (n-10) else 0) + (if n = 13 then 1 else 0)
private theorem recurrence_rejected (i : Fin 3) : ¬ recurrenceArena.Law (recurrenceRejected i) := by
  intro h
  fin_cases i
  · have hh := h 0
    norm_num [recurrenceRejected, realize, count_zero] at hh
  · have hh := h 3
    norm_num [recurrenceRejected, realize, count_zero, count_three] at hh
  · have hh := h 10
    norm_num [recurrenceRejected, realize, count_zero, count_seven, count_ten] at hh
    simp [Fin.ext_iff] at hh

def recurrenceRegistration : Registration recurrenceArena (recurrenceArena.Law recurrenceActual) where
  actual := recurrenceActual
  bridge := Iff.rfl
  variation := ⟨actual_count_recurrence, recurrenceRejected 0, recurrence_rejected 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨recurrenceRejected i, ?_, rfl, recurrence_rejected i⟩
      intro j hj
      funext p n
      simp [recurrenceActual, recurrenceRejected, realize, hj]
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 13, ?_⟩
    simp [recurrenceActual, realize, count_zero, count_thirteen]

private theorem root_spec : 0 < criticalX ∧ criticalX < 1 ∧ criticalX^3 + criticalX^10 = 1 := by
  unfold criticalX
  exact Classical.choose_spec (p := fun x : ℝ => 0 < x ∧ x < 1 ∧ x^3 + x^10 = 1) _

abbrev windowSignature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def windowActual : Realization windowSignature := realize windowSignature
  (fun _ x s => decide (s ≤ x^13)) (fun e => nomatch e)
def windowRejected : Realization windowSignature := realize windowSignature
  (fun _ _ _ => false) (fun e => nomatch e)
abbrev windowArena : Arena where
  signature := windowSignature
  Law R := ∀ (x : ℝ), 0 < x → x < 1 → x^3 + x^10 = 1 →
    (∀ n : ℕ, R.readout () x ((returnCount n : ℝ) * x^n) = true) ∧
    (∀ n : ℕ, 31 ≤ n → x^40 ≤ (returnCount n : ℝ) * x^n)
private theorem window_actual : windowArena.Law windowActual := by
  intro x hx hu hr
  simpa [windowActual, realize] using actual_count_window x hx hu hr
private theorem window_rejected : ¬ windowArena.Law windowRejected := by
  intro h
  have hh := (h criticalX root_spec.1 root_spec.2.1 root_spec.2.2).1 0
  simp [windowRejected, realize] at hh

def windowRegistration : Registration windowArena
    (∀ (x : ℝ), 0 < x → x < 1 → x^3 + x^10 = 1 →
      (∀ n : ℕ, (returnCount n : ℝ) * x^n ≤ x^13) ∧
      (∀ n : ℕ, 31 ≤ n → x^40 ≤ (returnCount n : ℝ) * x^n)) where
  actual := windowActual
  bridge := by simp [windowActual, realize]
  variation := ⟨window_actual, windowRejected, window_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨windowRejected, ?_, rfl, window_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    have c6 : returnCount 6 = 0 := by simpa using (actual_count_middle 6).2
    have c16 : returnCount 16 = 1 := by
      have h := actual_count_recurrence 16
      norm_num [count_thirteen, c6] at h
      exact h
    refine ⟨2, (returnCount 0 : ℝ) * (2 : ℝ)^0,
      (returnCount 16 : ℝ) * (2 : ℝ)^16, ?_⟩
    norm_num [windowActual, realize, count_zero, c16]
    simp

abbrev positiveSignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def positiveActual : Realization positiveSignature := realize positiveSignature
  (fun _ _ x => decide (0 < x)) (fun e => nomatch e)
def positiveRejected : Realization positiveSignature := realize positiveSignature
  (fun _ _ _ => false) (fun e => nomatch e)
abbrev logArena : Arena where
  signature := positiveSignature
  Law R := R.readout () () alphaInfinity = true ∧ ∀ n : ℕ, 31 ≤ n →
    0 < (returnCount n : ℝ) ∧
    2*alphaInfinity*(n : ℝ)-80*alphaInfinity ≤ Real.logb 2 (returnCount n : ℝ) ∧
    Real.logb 2 (returnCount n : ℝ) ≤ 2*alphaInfinity*(n : ℝ)-26*alphaInfinity
private theorem log_actual : logArena.Law positiveActual := by
  simpa [positiveActual, realize] using actual_count_log_bounds
private theorem log_rejected : ¬ logArena.Law positiveRejected := by
  intro h
  simp [positiveRejected, realize] at h

def logRegistration : Registration logArena
    (0 < alphaInfinity ∧ ∀ n : ℕ, 31 ≤ n →
      0 < (returnCount n : ℝ) ∧
      2*alphaInfinity*(n : ℝ)-80*alphaInfinity ≤ Real.logb 2 (returnCount n : ℝ) ∧
      Real.logb 2 (returnCount n : ℝ) ≤ 2*alphaInfinity*(n : ℝ)-26*alphaInfinity) where
  actual := positiveActual
  bridge := by simp [positiveActual, realize]
  variation := ⟨log_actual, positiveRejected, log_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨positiveRejected, ?_, rfl, log_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, alphaInfinity, ?_⟩
    simp [positiveActual, realize, actual_count_log_bounds.1]

abbrev rateSignature : Signature := positiveSignature
def rateActual : Realization rateSignature := realize rateSignature
  (fun _ _ x => decide (Filter.Tendsto
    (fun n : ℕ => Real.logb 2 (returnCount n : ℝ) / (2*(n : ℝ)))
    Filter.atTop (nhds x))) (fun e => nomatch e)
def rateRejected : Realization rateSignature := realize rateSignature
  (fun _ _ _ => false) (fun e => nomatch e)
abbrev rateArena : Arena where
  signature := rateSignature
  Law R := Asymptotics.IsBigO Filter.atTop
    (fun n : ℕ => Real.logb 2 (returnCount n : ℝ)-2*alphaInfinity*(n : ℝ))
    (fun _ : ℕ => (1 : ℝ)) ∧ R.readout () () alphaInfinity = true
private theorem rate_actual : rateArena.Law rateActual := by
  simpa [rateActual, realize] using actual_even_rate
private theorem rate_rejected : ¬ rateArena.Law rateRejected := by
  intro h
  simp [rateRejected, realize] at h
private theorem rate_zero : ¬ Filter.Tendsto
    (fun n : ℕ => Real.logb 2 (returnCount n : ℝ) / (2*(n : ℝ)))
    Filter.atTop (nhds (0 : ℝ)) := by
  intro h
  have he := tendsto_nhds_unique actual_even_rate.2 h
  exact actual_count_log_bounds.1.ne' he

def rateRegistration : Registration rateArena
    (Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ => Real.logb 2 (returnCount n : ℝ)-2*alphaInfinity*(n : ℝ))
      (fun _ : ℕ => (1 : ℝ)) ∧
    Filter.Tendsto (fun n : ℕ => Real.logb 2 (returnCount n : ℝ) / (2*(n : ℝ)))
      Filter.atTop (nhds alphaInfinity)) where
  actual := rateActual
  bridge := by simp [rateActual, realize]
  variation := ⟨rate_actual, rateRejected, rate_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rateRejected, ?_, rfl, rate_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨(), alphaInfinity, 0, ?_⟩
    simp [rateActual, realize, actual_even_rate.2, rate_zero]

def actual_count_middle_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount.actual_count_middle)
      (type_of% (realize.{0,0,0,0,0} countSignature (fun _ _ n => returnCount n) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount.actual_count_middle_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount.middleRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨middleArena⟩
  objectArena := .source ⟨middleArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source middleArena ⟨middleRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} countSignature (fun _ _ n => returnCount n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "arg", "fn", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms actual_count_middle_registration
#print axioms middleRegistration

def actual_count_support_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount.actual_count_support)
      (type_of% (realize.{0,0,0,0,0} countSignature (fun _ _ n => returnCount n) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount.actual_count_support_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount.supportRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨supportArena⟩
  objectArena := .source ⟨supportArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source supportArena ⟨supportRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} countSignature (fun _ _ n => returnCount n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "fn", "arg", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms actual_count_support_registration
#print axioms supportRegistration

def actual_count_recurrence_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount.actual_count_recurrence)
      (type_of% (realize.{0,0,0,0,0} recurrenceSignature (fun _ _ n => returnCount n) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount.actual_count_recurrence_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount.recurrenceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨recurrenceArena⟩
  objectArena := .source ⟨recurrenceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source recurrenceArena ⟨recurrenceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} recurrenceSignature (fun _ _ n => returnCount n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "fn", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }, { path := #["body", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }, { path := #["body", "arg", "fn", "arg", "arg", "fn", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms actual_count_recurrence_registration
#print axioms recurrenceRegistration

def actual_count_window_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount.actual_count_window)
      (type_of% (realize.{0,0,0,0,0} windowSignature (fun _ x s => decide (s ≤ x^13)) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount.actual_count_window_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount.windowRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨windowArena⟩
  objectArena := .source ⟨windowArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source windowArena ⟨windowRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} windowSignature (fun _ x s => decide (s ≤ x^13)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg", "body"], stateBinder := 0, functionOperand := false, stateOperand := some #["fn", "arg"], booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms actual_count_window_registration
#print axioms windowRegistration

def actual_count_log_bounds_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount.actual_count_log_bounds)
      (type_of% (realize.{0,0,0,0,0} positiveSignature (fun _ _ x => decide (0 < x)) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount.actual_count_log_bounds_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount.logRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨logArena⟩
  objectArena := .source ⟨logArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source logArena ⟨logRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} positiveSignature (fun _ _ x => decide (0 < x)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms actual_count_log_bounds_registration
#print axioms logRegistration

def actual_even_rate_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount.actual_even_rate)
      (type_of% (realize.{0,0,0,0,0} rateSignature (fun _ _ x => decide (Filter.Tendsto (fun n : ℕ => Real.logb 2 (returnCount n : ℝ) / (2*(n : ℝ))) Filter.atTop (nhds x))) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount.actual_even_rate_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount.rateRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨rateArena⟩
  objectArena := .source ⟨rateArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rateArena ⟨rateRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} rateSignature (fun _ _ x => decide (Filter.Tendsto (fun n : ℕ => Real.logb 2 (returnCount n : ℝ) / (2*(n : ℝ))) Filter.atTop (nhds x))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg", "arg"], booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms actual_even_rate_registration
#print axioms rateRegistration

#print axioms count_zero
#print axioms count_three
#print axioms count_seven
#print axioms count_ten
#print axioms count_thirteen
#print axioms middle_rejected
#print axioms support_rejected
#print axioms recurrence_rejected
#print axioms root_spec
#print axioms window_actual
#print axioms window_rejected
#print axioms log_actual
#print axioms log_rejected
#print axioms rate_actual
#print axioms rate_rejected
#print axioms rate_zero

#print axioms _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount.actual_count_middle

#print axioms _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount.actual_count_support

#print axioms _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount.actual_count_recurrence

#print axioms _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount.actual_count_window

#print axioms _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount.actual_count_log_bounds

#print axioms _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount.actual_even_rate

#print axioms countActual

#print axioms countRejected

#print axioms recurrenceActual

#print axioms recurrenceRejected

#print axioms windowActual

#print axioms windowRejected

#print axioms positiveActual

#print axioms positiveRejected

#print axioms rateActual

#print axioms rateRejected

set_option pp.all true in
#check @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount.actual_count_middle

set_option pp.all true in
#check @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount.actual_count_support

set_option pp.all true in
#check @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount.actual_count_recurrence

set_option pp.all true in
#check @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount.actual_count_window

set_option pp.all true in
#check @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount.actual_count_log_bounds

set_option pp.all true in
#check @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount.actual_even_rate

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount
