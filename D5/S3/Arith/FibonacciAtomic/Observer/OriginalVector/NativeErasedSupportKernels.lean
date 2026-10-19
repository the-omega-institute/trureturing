/- GID: D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/NativeErasedSupportKernels
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/OriginalVector/NativeErasedSupportKernels
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact labeled, leaf-erased and presence prefix kernels at native even epochs. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialDepth
import D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.Kernel
import D5.S3.Arith.FibonacciAtomic.Observer.DelayedOriginalReadout

/-! # Native erased and support prefix kernels

Two substitutions shift labeled and erased prefix agreement by one layer and
presence agreement by two layers. Iteration gives the corresponding even-epoch kernels.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.OriginalVector.NativeErasedSupportKernels

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open ActualLeafHistoryRigidity (subtree)
open NativeSerialDepth (OriginalAgree)

local notation "C" => (substitution^[2])

/-- Leaf erasure retains the distinction between a branch and an absent address. -/
inductive ErasedReply
  | leaf | branch | absent
  deriving DecidableEq

/-- Only the two leaf labels are identified. -/
def erase : Reply → ErasedReply
  | .alpha | .beta => .leaf
  | .branch => .branch
  | .absent => .absent

/-- Equality of every leaf-erased reply through an inclusive radius. -/
def ErasedAgree (r : Nat) (u v : Source) : Prop :=
  ∀ a : Address, a.length ≤ r → erase (readout a u) = erase (readout a v)

/-- Equality of presence bits at the same ordered addresses. -/
def SupportAgree (r : Nat) (u v : Source) : Prop :=
  ∀ a : Address, a.length ≤ r → (readout a u ≠ .absent ↔ readout a v ≠ .absent)

private theorem root_reflection (u v : Source) (same : ErasedAgree 1 (C u) (C v)) :
    readout [] u = readout [] v := by
  have left := same [false] (by simp)
  have right := same [true] (by simp)
  have roots (t : Source) : readout [] (C t) = .branch :=
    FiniteMenu.Kernel.branch_after [] t 2 (by
      simp [NativeRankedNavigationCompiler.pathCost])
  cases u with
  | of b =>
    cases v with
    | of c => cases b <;> cases c <;> first | rfl | contradiction
    | mul l r =>
      change erase (readout [true] (C (.of b))) = erase (readout [] (C r)) at right
      rw [roots r] at right
      cases b <;> cases right
  | mul l r =>
    cases v with
    | of c =>
      change erase (readout [] (C r)) = erase (readout [true] (C (.of c))) at right
      rw [roots r] at right
      cases c <;> cases right
    | mul l' r' => rfl

private theorem sharp_forward (h : Nat) (u v : Source) (same : OriginalAgree h u v) :
    OriginalAgree (h+1) (C u) (C v) := by
  induction h generalizing u v with
  | zero =>
    have root := same [] (by simp)
    cases u with
    | of b =>
      cases v with
      | of c =>
        have bc : b = c := by cases b <;> cases c <;> simp_all [readout]
        subst c
        exact fun _ _ => rfl
      | mul l r => cases b <;> cases root
    | mul l r =>
      cases v with
      | of c => cases c <;> cases root
      | mul l' r' =>
        intro a ha
        cases a with
        | nil => rfl
        | cons b a =>
          have az : a = [] := List.length_eq_zero_iff.mp (by
            simp only [List.length_cons] at ha
            omega)
          subst a
          have roots (t : Source) : readout [] (C t) = .branch :=
            FiniteMenu.Kernel.branch_after [] t 2 (by
              simp [NativeRankedNavigationCompiler.pathCost])
          cases b
          · exact (roots l).trans (roots l').symm
          · exact (roots r).trans (roots r').symm
  | succ h ih =>
    have root := same [] (by simp)
    cases u with
    | of b =>
      cases v with
      | of c =>
        have bc : b = c := by cases b <;> cases c <;> simp_all [readout]
        subst c
        exact fun _ _ => rfl
      | mul l r => cases b <;> cases root
    | mul l r =>
      cases v with
      | of c => cases c <;> cases root
      | mul l' r' =>
        have left : OriginalAgree h l l' := fun a ha =>
          same (false :: a) (by simp only [List.length_cons]; omega)
        have right : OriginalAgree h r r' := fun a ha =>
          same (true :: a) (by simp only [List.length_cons]; omega)
        intro a ha
        cases a with
        | nil => rfl
        | cons b a =>
          have small : a.length ≤ h+1 := by simp only [List.length_cons] at ha; omega
          cases b
          · exact ih l l' left a small
          · exact ih r r' right a small

private theorem erased_reflection (h : Nat) (u v : Source)
    (same : ErasedAgree (h + 1) (C u) (C v)) : OriginalAgree h u v := by
  induction h generalizing u v with
  | zero =>
    intro a ha
    have az : a = [] := List.length_eq_zero_iff.mp (by omega)
    subst a
    exact root_reflection u v same
  | succ h ih =>
    have root := root_reflection u v (fun a ha => same a (by omega))
    cases u with
    | of b =>
      cases v with
      | of c =>
        have bc : b = c := by cases b <;> cases c <;> simp_all [readout]
        subst c
        exact fun _ _ => rfl
      | mul l r => cases b <;> cases root
    | mul l r =>
      cases v with
      | of c => cases c <;> cases root
      | mul l' r' =>
        have left : ErasedAgree (h+1) (C l) (C l') := fun a ha =>
          same (false :: a) (by simp only [List.length_cons]; omega)
        have right : ErasedAgree (h+1) (C r) (C r') := fun a ha =>
          same (true :: a) (by simp only [List.length_cons]; omega)
        intro a ha
        cases a with
        | nil => rfl
        | cons b a =>
          have small : a.length ≤ h := by simp only [List.length_cons] at ha; omega
          cases b
          · exact ih l l' left a small
          · exact ih r r' right a small

private theorem erased_reply_presence (p : Address) (b : Bool) (u v : Source) :
    erase (readout p u) = erase (readout p v) ↔
      (readout p u ≠ .absent ↔ readout p v ≠ .absent) ∧
      (readout (p ++ [b]) u ≠ .absent ↔ readout (p ++ [b]) v ≠ .absent) := by
  have readAt := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have pu := readAt p [] u
  have pv := readAt p [] v
  simp only [List.append_nil] at pu pv
  rw [pu, pv, readAt p [b] u, readAt p [b] v]
  have present (t : Source) : readout [] t ≠ .absent := by
    intro ht
    have ht' := (DelayedOriginalReadout.right_clock_readout 0 t).1.mp ht
    omega
  cases su : subtree p u with
  | none =>
    cases sv : subtree p v with
    | none => simp [erase]
    | some y => cases y with
      | of c => cases c <;> simp [readout, erase]
      | mul l r => simp [readout, erase]
  | some x =>
    cases sv : subtree p v with
    | none => cases x with
      | of c => cases c <;> simp [readout, erase]
      | mul l r => simp [readout, erase]
    | some y =>
      cases x with
      | of c => cases y with
        | of d => cases c <;> cases d <;> simp [readout, erase]
        | mul l r => cases c <;> cases b <;> simp [readout, erase, present]
      | mul l r => cases y with
        | of c => cases c <;> cases b <;> simp [readout, erase, present]
        | mul l' r' => cases b <;> simp [readout, erase, present]

private theorem erased_support (r : Nat) (u v : Source) :
    ErasedAgree r u v ↔ SupportAgree (r+1) u v := by
  constructor
  · intro same a ha
    by_cases hz : a = []
    · subst a
      have present (t : Source) : readout [] t ≠ .absent := by
        intro ht
        have ht' := (DelayedOriginalReadout.right_clock_readout 0 t).1.mp ht
        omega
      exact ⟨fun _ => present v, fun _ => present u⟩
    · have he : a = a.dropLast ++ [a.getLast hz] := (List.dropLast_concat_getLast hz).symm
      have small : a.dropLast.length ≤ r := by
        simp only [List.length_dropLast]
        omega
      rw [he]
      exact ((erased_reply_presence a.dropLast (a.getLast hz) u v).mp
        (same a.dropLast small)).2
  · intro same a ha
    apply (erased_reply_presence a false u v).mpr
    exact ⟨same a (by omega), same (a ++ [false]) (by
      simp only [List.length_append, List.length_singleton]
      omega)⟩

/-- Two native steps shift the labeled and erased kernels by one layer,
and the presence kernel by two layers. -/
theorem two_step_prefix_kernel (h : Nat) (u v : Source) :
    (OriginalAgree h u v ↔ OriginalAgree (h+1) (C u) (C v)) ∧
    (OriginalAgree h u v ↔ ErasedAgree (h+1) (C u) (C v)) ∧
    (OriginalAgree h u v ↔ SupportAgree (h+2) (C u) (C v)) := by
  have erased : OriginalAgree h u v ↔ ErasedAgree (h+1) (C u) (C v) :=
    ⟨fun same a ha => congrArg erase (sharp_forward h u v same a ha),
      erased_reflection h u v⟩
  refine ⟨⟨sharp_forward h u v, ?_⟩, erased, erased.trans (erased_support (h+1) (C u) (C v))⟩
  intro same
  exact erased.mpr (fun a ha => congrArg erase (same a ha))

private theorem labeled_iterates (h k : Nat) (u v : Source) :
    OriginalAgree h u v ↔
      OriginalAgree (h+k) (substitution^[2*k] u) (substitution^[2*k] v) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have step := (two_step_prefix_kernel (h+k)
      (substitution^[2*k] u) (substitution^[2*k] v)).1
    simpa only [show h+(k+1) = h+k+1 by omega,
      show 2*(k+1) = 2+2*k by omega, Function.iterate_add_apply] using ih.trans step

/-- At every positive even epoch, erased and presence prefixes recover
exactly the original labeled prefix at the stated radii. -/
theorem even_epoch_support_kernel (h k : Nat) (positive : 1 ≤ k) (u v : Source) :
    (ErasedAgree (h+k) (substitution^[2*k] u) (substitution^[2*k] v) ↔
      OriginalAgree h u v) ∧
    (SupportAgree (h+k+1) (substitution^[2*k] u) (substitution^[2*k] v) ↔
      OriginalAgree h u v) := by
  obtain ⟨j, rfl⟩ : ∃ j : Nat, k = j+1 := ⟨k-1, by omega⟩
  have step := two_step_prefix_kernel (h+j)
    (substitution^[2*j] u) (substitution^[2*j] v)
  have previous := (labeled_iterates h j u v).symm
  simpa only [show h+(j+1) = h+j+1 by omega,
    show h+(j+1)+1 = h+j+2 by omega,
    show 2*(j+1) = 2+2*j by omega, Function.iterate_add_apply] using
    And.intro (step.2.1.symm.trans previous) (step.2.2.symm.trans previous)

#print axioms two_step_prefix_kernel
#print axioms even_epoch_support_kernel

end D5.S3.Arith.FibonacciAtomic.Observer.OriginalVector.NativeErasedSupportKernels
