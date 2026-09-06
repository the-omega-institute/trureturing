/- GID: D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier
   generality: I
   mirror-B: D5/B/S1/Digit/GoldenBase4TwentyStatePrefixBarrier
   mirror-E: none(waiver:explicit-finite-prefix-witness)
   anchors: []
   digest: An explicit twenty-state typed machine fits every power index below 367 and first fails at 367, so no dictionary confined to that prefix can establish a twenty-one-state lower bound. -/

import D5.S1.Digit.GoldenBase4DenseInput

/- This is a finite-prefix obstruction to an insufficient lower-bound dataset,
   not an all-powers upper construction. Machine semantics and the original
   M01 input/digit functions are reused. The table was found by identifying
   reference states 2 and 3 and keeping the zero successor of state 2, which
   changes transitions and is not a behavior-preserving reference quotient.
   Exact source-bound arithmetic checking was executed for 2,000 powers.
   These Lean proof bodies have not been elaborated or kernel checked here. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.GoldenBase4TwentyStatePrefixBarrier

open D5.S0.Automata.TypedPartialDFAOOverBase
open D5.S1.Digit.GoldenBase4AutomataOracle

/-- The thirteen previous-zero rows and seven previous-one rows. -/
def stateType (q : Fin 20) : BinaryZeckendorfState :=
  if q.val < 13 then .previousZero else .previousOne

/-- Zero successors of the explicit finite-prefix witness. -/
def zeroTarget : Fin 20 → Fin 20 :=
  ![0,8,7,6,5,4,4,3,3,2,2,2,1,12,11,11,10,9,8,8]

/-- One successors; unused entries remain hidden behind the type guard. -/
def oneTarget : Fin 20 → Fin 20 :=
  ![17,19,18,17,17,17,16,16,15,14,14,13,13,0,0,0,0,0,0,0]

/-- The output is always a base-four digit. -/
def output : Fin 20 → Fin 4 :=
  ![0,3,3,3,3,0,0,0,0,0,1,1,1,1,1,2,2,2,2,3]

/-- Every legal symbol has a successor; consecutive ones remain undefined. -/
def step (q : Fin 20) (a : Fin 2) : Option (Fin 20) :=
  if a = 0 then some (zeroTarget q)
  else if q.val < 13 then some (oneTarget q) else none

/-- A concrete machine in the same candidate class as the original problem. -/
def machine : TypedPartialDFAO binaryZeckendorfBase (Fin 4) (Fin 20) where
  start := 0
  stateType := stateType
  step := step
  output := output
  start_type := rfl
  step_type := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
private theorem agrees_before_367 : ∀ n : Fin 367,
    machine.evalOutput (base4PowerWord n.val) =
      GoldenBase4IntervalMachine.machine.evalOutput (base4PowerWord n.val) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
private theorem reference_at_367 :
    GoldenBase4IntervalMachine.machine.evalOutput (base4PowerWord 367) =
      some (0 : Fin 4) := by
  decide

/-- Every original power input with index below 367 is computed correctly. -/
theorem correct_before_367 (n : Nat) (hn : n < 367) :
    machine.evalOutput (base4PowerWord n) = some (base4GoldenDigit n) := by
  exact (agrees_before_367 ⟨n, hn⟩).trans
    (GoldenBase4DenseInput.base4PowerWord_correct n)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
/-- At index 367 the concrete twenty-state table emits one. -/
theorem output_at_367 :
    machine.evalOutput (base4PowerWord 367) = some (1 : Fin 4) := by
  decide

/-- The original exact arithmetic oracle has digit zero at index 367. -/
theorem true_digit_at_367 : base4GoldenDigit 367 = 0 := by
  have h := GoldenBase4DenseInput.base4PowerWord_correct 367
  rw [reference_at_367] at h
  exact (Option.some.inj h).symm

/-- This finite-prefix witness is not a solution of the infinite problem. -/
theorem fails_at_367 :
    machine.evalOutput (base4PowerWord 367) ≠ some (base4GoldenDigit 367) := by
  rw [output_at_367, true_digit_at_367]
  decide

/-- Every failure of this witness is at least the explicitly attained index. -/
theorem no_earlier_failure (n : Nat)
    (bad : machine.evalOutput (base4PowerWord n) ≠ some (base4GoldenDigit n)) :
    367 ≤ n := by
  by_contra h
  exact bad (correct_before_367 n (by omega))

/-- Both published initial anchors hold, including the leading-zero loop. -/
theorem initial_anchors :
    machine.step machine.start 0 = some machine.start ∧ machine.output machine.start = 0 :=
  ⟨rfl, rfl⟩

/-- Every collection of observations confined to indices below 367 has a
20-state witness. This includes the original 79 rows and the 144 gap4 rows.
The indices may repeat and the collection may be described by any index type. -/
theorem every_subprefix_has_twenty_state_witness {I : Type*}
    (index : I → Nat) (small : ∀ i, index i < 367) :
    ∃ M : TypedPartialDFAO binaryZeckendorfBase (Fin 4) (Fin 20),
      (∀ i, M.evalOutput (base4PowerWord (index i)) = some (base4GoldenDigit (index i))) ∧
      M.step M.start 0 = some M.start ∧ M.output M.start = 0 := by
  exact ⟨machine, fun i => correct_before_367 (index i) (small i), initial_anchors⟩

#print axioms correct_before_367
#print axioms fails_at_367
#print axioms every_subprefix_has_twenty_state_witness

end D5.S1.Digit.GoldenBase4TwentyStatePrefixBarrier
