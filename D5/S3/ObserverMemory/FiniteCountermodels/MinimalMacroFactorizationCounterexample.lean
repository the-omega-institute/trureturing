/- GID: D5/S3/ObserverMemory/FiniteCountermodels/MinimalMacroFactorizationCounterexample
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/FiniteCountermodels/MinimalMacroFactorizationCounterexample
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A deterministic three-state process does not descend through its two-class readout. -/

import Mathlib.Logic.Function.Basic

/- Library-search audit trail (2026-08-20):
   * The exact source string `qF=overlineFq` has no hit in D5 or the active
     frozen ledger.
   * D5 contains adjacent observer-fiber and prediction-completion
     factorization theorems, but no three-state counterexample with this map.
   * Pinned Mathlib provides `Function.FactorsThrough` and the exact bridge
     `Function.factorsThrough_iff`; the nonfactorization proof reuses both. -/

namespace D5.S3.ObserverMemory.FiniteCountermodels.MinimalMacroFactorizationCounterexample

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The two macroscopic observation classes in the finite source model. -/
inductive ObservationClass
  | A
  | B
  deriving DecidableEq, Nonempty

/-- States zero and one share class A; state two has class B. -/
def minimalObservation (x : Fin 3) : ObservationClass :=
  if x = 2 then .B else .A

/-- The deterministic process fixes zero and sends both other states to two. -/
def minimalProcess (x : Fin 3) : Fin 3 :=
  if x = 0 then 0 else 2

/-- The explicit deterministic model has equal present readouts at zero and
one but unequal next readouts, so no function on observation classes can
intertwine the microscopic process with the readout. -/
theorem deterministic_three_state_process_has_no_macro_factorization :
    minimalObservation 0 = .A ∧
      minimalObservation 1 = .A ∧
      minimalObservation 2 = .B ∧
      minimalProcess 0 = 0 ∧
      minimalProcess 1 = 2 ∧
      minimalProcess 2 = 2 ∧
      minimalObservation 0 = minimalObservation 1 ∧
      minimalObservation (minimalProcess 0) = .A ∧
      ObservationClass.A ≠ ObservationClass.B ∧
      minimalObservation (minimalProcess 1) = .B ∧
      minimalObservation (minimalProcess 0) ≠
        minimalObservation (minimalProcess 1) ∧
      ¬ ∃ macroProcess : ObservationClass -> ObservationClass,
        minimalObservation ∘ minimalProcess = macroProcess ∘ minimalObservation := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, ?_⟩
  have hnot :
      ¬ (minimalObservation ∘ minimalProcess).FactorsThrough minimalObservation := by
    intro hfactor
    have hsame :
        (minimalObservation ∘ minimalProcess) 0 =
          (minimalObservation ∘ minimalProcess) 1 :=
      hfactor (by decide)
    have hneq :
        (minimalObservation ∘ minimalProcess) 0 ≠
          (minimalObservation ∘ minimalProcess) 1 := by
      decide
    exact hneq hsame
  intro hexists
  exact hnot ((Function.factorsThrough_iff
    (f := minimalObservation) (minimalObservation ∘ minimalProcess)).2 hexists)

/-- A checked inhabitant of the microscopic domain. -/
example : Fin 3 := 0

/-- A checked inhabitant of the macroscopic codomain. -/
example : ObservationClass := .A

#print axioms deterministic_three_state_process_has_no_macro_factorization

end D5.S3.ObserverMemory.FiniteCountermodels.MinimalMacroFactorizationCounterexample
