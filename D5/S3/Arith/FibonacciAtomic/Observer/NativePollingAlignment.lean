/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativePollingAlignment
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/NativePollingAlignment
   mirror-E: none(waiver:unbounded-symbolic-execution)
   anchors: []
   utility: none
   digest: Exact native polling alignment with two genuine updates and a paid routing read. -/

import D5.S3.Arith.FibonacciAtomic.Observer.DelayedOriginalReadout
import D5.S3.ObserverMemory.Algorithms.NativeExecutionTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativePollingAlignment

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open DelayedOriginalReadout (rightClock rights right_clock_iterate right_clock_readout)
open D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution

/-- Complete controls for the pilot loop; the terminal control retains its bit. -/
inductive Control where
  | poll | firstUpdate | secondUpdate | route | done : Bool → Control
  deriving DecidableEq

/-- Absence retries; the two leaf replies terminate; branch is an unsupported hold. -/
def dispatch : Reply → Control
  | .absent => .firstUpdate
  | .alpha => .done false
  | .beta => .done true
  | .branch => .poll

/-- Every retry keeps both native updates and the source-preserving root read. -/
def program (K : Nat) : Control → Instruction Control Address Reply
  | .poll => .read (rights K) dispatch
  | .firstUpdate => .update .secondUpdate
  | .secondUpdate => .update .route
  | .route => .read [] (fun _ => .poll)
  | .done _ => .halt

/-- The observation field is obtained from one fixed original source. -/
def observations (u : Source) (j : Nat) (p : Address) : Reply :=
  readout p (substitution^[j] u)

private theorem reaches (K : Nat) (u : Source) (k : Nat) :
    ∀ (a e : Nat), e < 2 →
      rightClock u + a + 2 * k = 2 * K + e →
      Run (program K) (observations u) .poll a
        (.done (decide (e = 1))) (a + 2 * k) := by
  induction k with
  | zero =>
    intro a e he hc
    have clock := right_clock_iterate a u
    have replies := right_clock_readout K (substitution^[a] u)
    have zero_or_one : e = 0 ∨ e = 1 := by omega
    rcases zero_or_one with rfl | rfl
    · have reply : observations u a (rights K) = .alpha :=
        replies.2.1.mpr (by omega)
      apply Run.read (p := rights K) (k := dispatch) rfl
      simp only [reply, dispatch, Nat.mul_zero, Nat.add_zero]
      exact .refl _ _
    · have reply : observations u a (rights K) = .beta :=
        replies.2.2.1.mpr (by omega)
      apply Run.read (p := rights K) (k := dispatch) rfl
      simp only [reply, dispatch, decide_true, Nat.mul_zero, Nat.add_zero]
      exact .refl _ _
  | succ k ih =>
    intro a e he hc
    have clock := right_clock_iterate a u
    have reply : observations u a (rights K) = .absent :=
      (right_clock_readout K (substitution^[a] u)).1.mpr (by omega)
    apply Run.read (p := rights K) (k := dispatch) rfl
    rw [reply]
    apply Run.update (prog := program K) (z := Control.secondUpdate) rfl
    apply Run.update (prog := program K) (z := Control.route) rfl
    apply Run.read (p := []) (k := fun _ => .poll) rfl
    convert ih (a + 1 + 1) e he (by omega) using 1
    omega

/-- Under the finite clock promise, a native halt occurs exactly at the preserved
clock parity and after twice the remaining right-spine depth in real updates. -/
theorem native_polling_alignment (K : Nat) (u : Source)
    (bound : rightClock u ≤ 2 * K + 1) (b : Bool) (N : Nat) :
    Run (program K) (observations u) .poll 0 (.done b) N ↔
      b = decide (rightClock u % 2 = 1) ∧ N = 2 * (K - rightClock u / 2) := by
  have rem_lt := Nat.mod_lt (rightClock u) (by decide : 0 < 2)
  have quotient := Nat.mod_add_div (rightClock u) 2
  have halt := reaches K u (K - rightClock u / 2) 0 (rightClock u % 2) rem_lt (by omega)
  simp only [Nat.zero_add] at halt
  constructor
  · intro run
    obtain ⟨sameControl, sameEpoch⟩ := run_halt_unique run halt rfl rfl
    exact ⟨Control.done.inj sameControl, sameEpoch⟩
  · rintro ⟨rfl, rfl⟩
    exact halt

#print axioms native_polling_alignment

end D5.S3.Arith.FibonacciAtomic.Observer.NativePollingAlignment
