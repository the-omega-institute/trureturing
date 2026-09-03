/- GID: D5/S3/ObserverMemory/Refinement/InvolutiveReadoutCompletion
   generality: G
   mirror-B: none(waiver:new-observer-library-node)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A readout flipped by an involution is broken at odd iterates and completed at even iterates. -/

import Mathlib.Algebra.Ring.Parity
import Mathlib.Logic.Function.Iterate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Refinement.InvolutiveReadoutCompletion

/-- A dynamical system whose visible readout is flipped by an involution at
every step. The state update itself need not be involutive. -/
structure InvolutiveReadoutSystem (State Readout : Type*) where
  step : State → State
  readout : State → Readout
  flip : Readout → Readout
  flip_involutive : Function.Involutive flip
  readout_step : ∀ state, readout (step state) = flip (readout state)

/-- Iterating the state update transports the readout through the same number
of visible flips. -/
theorem readout_iterate
    {State Readout : Type*}
    (system : InvolutiveReadoutSystem State Readout)
    (state : State) (steps : ℕ) :
    system.readout ((system.step^[steps]) state) =
      (system.flip^[steps]) (system.readout state) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [Function.iterate_succ_apply', system.readout_step, ih,
        Function.iterate_succ_apply']

/-- An even number of flips restores the visible readout. -/
theorem even_iterate_completes_readout
    {State Readout : Type*}
    (system : InvolutiveReadoutSystem State Readout)
    (state : State) {steps : ℕ} (heven : Even steps) :
    system.readout ((system.step^[steps]) state) = system.readout state := by
  rw [readout_iterate, system.flip_involutive.iterate_even heven]

/-- An odd number of flips leaves the readout on the opposite involutive sheet. -/
theorem odd_iterate_flips_readout
    {State Readout : Type*}
    (system : InvolutiveReadoutSystem State Readout)
    (state : State) {steps : ℕ} (hodd : Odd steps) :
    system.readout ((system.step^[steps]) state) =
      system.flip (system.readout state) := by
  rw [readout_iterate, system.flip_involutive.iterate_odd hodd]

/-- If the current readout is not fixed by the involution, every odd iterate is
visibly different from the starting readout. -/
theorem odd_iterate_breaks_readout
    {State Readout : Type*}
    (system : InvolutiveReadoutSystem State Readout)
    (state : State) {steps : ℕ} (hodd : Odd steps)
    (hnotFixed : system.flip (system.readout state) ≠ system.readout state) :
    system.readout ((system.step^[steps]) state) ≠ system.readout state := by
  rw [odd_iterate_flips_readout system state hodd]
  exact hnotFixed

/-- Even completion is a statement about the chosen readout. It does not by
itself imply that the full state update has returned to the initial state. -/
theorem even_readout_completion_of_state_distinct
    {State Readout : Type*}
    (system : InvolutiveReadoutSystem State Readout)
    (state : State) {steps : ℕ} (heven : Even steps)
    (hstate : (system.step^[steps]) state ≠ state) :
    system.readout ((system.step^[steps]) state) = system.readout state ∧
      (system.step^[steps]) state ≠ state :=
  ⟨even_iterate_completes_readout system state heven, hstate⟩

#print axioms readout_iterate
#print axioms even_iterate_completes_readout
#print axioms odd_iterate_flips_readout
#print axioms odd_iterate_breaks_readout
#print axioms even_readout_completion_of_state_distinct

end D5.S3.ObserverMemory.Refinement.InvolutiveReadoutCompletion
