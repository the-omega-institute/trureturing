/- GID: D5/S3/Arith/FibonacciAtomic/Observer/FutureResponses/NativeJointFutureClasses
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/FutureResponses/NativeJointFutureClasses
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact eleven-class common-source classification of two native future replies. -/

import D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition
import Mathlib.Data.Fintype.Sum

set_option autoImplicit false
noncomputable section

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeJointFutureClasses

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition

/-- The three possible initially present root shapes. -/
inductive RootClass
  | alpha | beta | branch
  deriving DecidableEq

instance : Fintype RootClass := ⟨{.alpha, .beta, .branch}, by intro c; cases c <;> simp⟩

/-- Root shape forgets the descendants of an existing branch. -/
def rootClass : Source → RootClass
  | .of true => .alpha
  | .of false => .beta
  | .mul _ _ => .branch

/-- One substitution changes only the root class in this three-state way. -/
def advance : RootClass → RootClass
  | .alpha => .beta
  | .beta => .branch
  | .branch => .branch

private theorem root_step (u : Source) :
    rootClass (substitution u) = advance (rootClass u) := by
  cases u with
  | of b => cases b <;> rfl
  | mul l r => rfl

private theorem root_iterate (u : Source) (k : ℕ) :
    rootClass (substitution^[k] u) = advance^[k] (rootClass u) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', root_step, ih]

private theorem root_read (u : Source) :
    readout [] u = match rootClass u with
      | .alpha => .alpha | .beta => .beta | .branch => .branch := by
  cases u with
  | of b => cases b <;> rfl
  | mul l r => rfl

private theorem iterate_mul (l r : Source) (k : ℕ) :
    substitution^[k] (.mul l r) = .mul (substitution^[k] l) (substitution^[k] r) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [Function.iterate_succ_apply', ih]
    exact substitution.map_mul _ _

/-- Two leaf classes and the nine jointly realizable ordered pairs of root classes. -/
abbrev JointClass := Bool ⊕ (RootClass × RootClass)

/-- This statistic is computed on one actual right subtree. -/
def jointClass : Source → JointClass
  | .of b => .inl b
  | .mul l r => .inr (rootClass l, rootClass r)

/-- Both queried addresses belong to the same initial source, with the same supplied count. -/
def futureReplies (v : Source) (k : ℕ) : Reply × Reply :=
  let t : Source := .mul (.of true) v
  (readout [true, false] (substitution^[k] t),
   readout [true, true] (substitution^[k] t))

private theorem same_root_iff (u v : Source) :
    readout [] u = readout [] v ↔ rootClass u = rootClass v := by
  rw [root_read, root_read]
  cases rootClass u <;> cases rootClass v <;> simp

private theorem same_code_future (u v : Source) (h : jointClass u = jointClass v)
    (k : ℕ) : futureReplies u k = futureReplies v k := by
  cases u with
  | of a =>
    cases v with
    | of b => have hab : a = b := Sum.inl.inj h; subst b; rfl
    | mul l r => simp [jointClass] at h
  | mul l r =>
    cases v with
    | of b => simp [jointClass] at h
    | mul l' r' =>
      have hc := Sum.inr.inj h
      have hl := congrArg Prod.fst hc
      have hr := congrArg Prod.snd hc
      simp only [jointClass] at hl hr
      simp only [futureReplies, iterate_mul, readout]
      rw [root_read, root_read, root_read, root_read,
        root_iterate, root_iterate, root_iterate, root_iterate, hl, hr]

/-- Equality at every future count is exactly equality of the eleven-valued spatial code.
No height bound or bounded enumeration is used. -/
private theorem classification (u v : Source) :
    (∀ k : ℕ, futureReplies u k = futureReplies v k) ↔ jointClass u = jointClass v := by
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    cases u with
    | of a =>
      cases v with
      | of b =>
        have hn : futureReplies (.of false) 1 ≠ futureReplies (.of true) 1 := by decide
        cases a <;> cases b
        · rfl
        · exact (hn h1).elim
        · exact (hn h1.symm).elim
        · rfl
      | mul l r =>
        have bad : readout [] l = Reply.absent := by
          simpa [futureReplies, readout] using (congrArg Prod.fst h0).symm
        rw [root_read] at bad
        cases hc : rootClass l <;> simp [hc] at bad
    | mul l r =>
      cases v with
      | of b =>
        have bad : readout [] l = Reply.absent := by
          simpa [futureReplies, readout] using congrArg Prod.fst h0
        rw [root_read] at bad
        cases hc : rootClass l <;> simp [hc] at bad
      | mul l' r' =>
        have hl : rootClass l = rootClass l' := same_root_iff l l' |>.mp (by
          simpa [futureReplies, readout] using congrArg Prod.fst h0)
        have hr : rootClass r = rootClass r' := same_root_iff r r' |>.mp (by
          simpa [futureReplies, readout] using congrArg Prod.snd h0)
        simp [jointClass, hl, hr]
  · intro h k
    exact same_code_future u v h k

/-- Canonical finite native root representatives. -/
def rootRepresentative : RootClass → Source
  | .alpha => .of true
  | .beta => .of false
  | .branch => .mul (.of true) (.of true)

/-- Every pair is realized in a single tree, rather than by independent marginal sources. -/
def representative : JointClass → Source
  | .inl b => .of b
  | .inr (l, r) => .mul (rootRepresentative l) (rootRepresentative r)

/-- The common-source code has exactly eleven attained labels. -/
private theorem eleven_joint_classes :
    Function.Surjective jointClass ∧ Fintype.card JointClass = 11 := by
  constructor
  · intro c
    refine ⟨representative c, ?_⟩
    cases c with
    | inl b => rfl
    | inr p => rcases p with ⟨l, r⟩; cases l <;> cases r <;> rfl
  · decide

/-- The all-future common-source response quotient has precisely eleven attained classes. -/
theorem native_joint_future_classification :
    (∀ u v : Source, (∀ k : ℕ, futureReplies u k = futureReplies v k) ↔
      jointClass u = jointClass v) ∧
    Function.Surjective jointClass ∧ Fintype.card JointClass = 11 :=
  ⟨classification, eleven_joint_classes⟩

end D5.S3.Arith.FibonacciAtomic.Observer.NativeJointFutureClasses
