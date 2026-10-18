/- GID: D5/S3/Arith/FibonacciAtomic/NativeContinuation/Quantum/ReadoutInstrument
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/NativeContinuation/Quantum/ReadoutInstrument
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The native high-window continuation has an exact diagonal instrument branch for the hidden joint mode. -/

import D5.S3.Arith.FibonacciAtomic.NativeContinuation.JointLaw
import D5.S3.Quantum.Measurement.DiagonalKrausInstrumentFactorization

noncomputable section

open scoped BigOperators

namespace D5.S3.Arith.FibonacciAtomic.NativeContinuation.Quantum.ReadoutInstrument

open D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd
open D5.S3.Arith.FibonacciAtomic.GraftAffineClosure
open D5.S3.Arith.FibonacciAtomic.ImmediateWindowStateCapacity
open D5.S3.Arith.FibonacciAtomic.NativeContinuation.JointLaw
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Measurement.DiagonalKrausInstrumentFactorization
open PhyslibLeaf

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The five native source modes in the foundational order `(0,2,3,5,25)`. -/
def sourceWindow (i : Fin 5) : Window :=
  match i.1 with
  | 0 => .zero
  | 1 => .low
  | 2 => .middle
  | 3 => .high
  | _ => .ends

/-- The first quantity parity is the acquired record. -/
def acquiredParity (i : Fin 5) : Bool :=
  match i.1 with
  | 0 | 1 => false
  | _ => true

/-- The four actual readouts after appending the native high window. -/
def replyCode (i : Fin 5) : Fin 4 :=
  match i.1 with
  | 0 => 0
  | 1 => 3
  | 2 => 1
  | 3 => 2
  | _ => 3

/-- The live successor index; `3` denotes the absorbing rejection state. -/
def successorCode (i : Fin 5) : Fin 4 :=
  match i.1 with
  | 0 => 0
  | 1 => 3
  | 2 => 1
  | 3 => 2
  | _ => 3

/-- The acquired `(parity,reply)` outcome, encoded in `Fin 8`. -/
def outcomeCode (i : Fin 5) : Fin 8 :=
  ⟨(if acquiredParity i then 4 else 0) + (replyCode i).1, by
    have h : (replyCode i).1 < 4 := (replyCode i).isLt
    by_cases hp : acquiredParity i <;> simp [hp] <;> omega⟩

/-- One Kraus column for each source: the output is the deterministic successor
and the branch carries the acquired parity together with its actual reply. -/
def kraus (b : Fin 8) (i : Fin 5) (o : Fin 4) : ℂ :=
  if b = outcomeCode i ∧ o = successorCode i then 1 else 0

/-- The concrete matrix family used by the diagonal instrument theorem. -/
def K (_ : Unit) (b : Fin 8) (_ : Unit) : Matrix (Fin 4) (Fin 5) ℂ :=
  fun o i => if b = outcomeCode i ∧ o = successorCode i then 1 else 0

private theorem hcomplete :
    ∀ a : Unit, ∑ b : Fin 8, ∑ r : Unit, (K a b r).conjTranspose * K a b r = 1 := by
  intro a
  ext i j
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_succ, K, outcomeCode, acquiredParity, replyCode, successorCode]

/- The table is the actual initialized native reader followed by the fixed
high-window continuation. `none` is the absorbing rejection branch. -/
theorem native_reply_table :
    ∀ i : Fin 5,
      task 0 [sourceWindow i, .high] =
        (match i.1 with
        | 0 => some (5 : ZMod 0)
        | 1 => none
        | 2 => some (18 : ZMod 0)
        | 3 => some (26 : ZMod 0)
        | _ => none) := by
  intro i
  fin_cases i <;>
    simp [sourceWindow, task, D5.S0.Automata.DFAOStateLowerBound.DFAO.evalOutput,
      DFA.eval, DFA.evalFrom, rawMachine, rawTransition, rawOutput, first, last,
      clock, displacement, D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.step,
      D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.quantity] <;>
    norm_num

private theorem hgram :
    ∀ (a : Unit) (b : Fin 8) (i : Fin 5) (o o' : Fin 4), o ≠ o' →
      ∑ r : Unit, K a b r o i * (starRingEnd ℂ) (K a b r o' i) = 0 := by
  intro a b i o o' hoo
  by_cases hb : b = outcomeCode i
  · simp [K, hb]
    by_cases ho : o = successorCode i <;>
      by_cases ho' : o' = successorCode i <;>
      simp_all
  · simp [K, hb]

private theorem diagonal_factorization
    (b : Fin 8) (p : Fin 5 → ℂ) :
    MatrixMap.of_kraus (K () b) (K () b) (Matrix.diagonal p) =
      Matrix.diagonal (fun o =>
        ∑ i, (weight K () b o i : ℂ) * p i) := by
  have h := diagonal_instrument_factorization K hcomplete
  exact h.2.2.1.1 (fun a b i o o' hoo => hgram a b i o o' hoo) p () b

/-- On diagonal source laws, the branch carrying odd parity and rejection has
exactly the hidden joint mass `p_(25)`. -/
theorem hidden_joint_branch
    (p : Fin 5 → ℝ) :
    (∑ i : Fin 5, if outcomeCode i = (7 : Fin 8) then p i else 0) = p 4 := by
  classical
  simp [Fin.sum_univ_succ, outcomeCode, acquiredParity, replyCode]

/-- The diagonal Kraus factorization and the hidden-joint branch are one
consumer: the complete family is a channel, while branch `7` reads `κ`. -/
theorem diagonal_readout_consumer
    (p : Fin 5 → ℝ) :
    MatrixMap.of_kraus (K () (7 : Fin 8)) (K () (7 : Fin 8))
        (Matrix.diagonal (fun i => (p i : ℂ))) =
      Matrix.diagonal (fun o =>
        ∑ i, (weight K () (7 : Fin 8) o i : ℂ) * (p i : ℂ)) ∧
    (∑ i : Fin 5, if outcomeCode i = (7 : Fin 8) then p i else 0) = p 4 := by
  refine ⟨diagonal_factorization 7 (fun i => (p i : ℂ)), hidden_joint_branch p⟩

theorem branch_trace_is_hidden_joint (p : Fin 5 → ℝ) :
    Matrix.trace
        (MatrixMap.of_kraus (K () (7 : Fin 8)) (K () (7 : Fin 8))
          (Matrix.diagonal (fun i => (p i : ℂ)))) = (p 4 : ℂ) := by
  rw [diagonal_factorization]
  simp [Matrix.trace, weight, K, Fin.sum_univ_succ, outcomeCode, acquiredParity,
    replyCode, successorCode]

#print axioms diagonal_readout_consumer

end D5.S3.Arith.FibonacciAtomic.NativeContinuation.Quantum.ReadoutInstrument
