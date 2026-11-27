/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import OmegaMathlib.Data.Nat.Choose.Basic
public import OmegaMathlib.Data.Nat.Fib.Basic

/-! The strict natural numbers and two arithmetic definitions interpreted in Mathlib. -/

noncomputable section

namespace OmegaChecks.NatCorrespondence

/-- Interpret strict zero and successor as standard zero and successor. -/
@[expose] public def toStd : Omega.Nat → Nat :=
  Omega.Nat.rec 0 (fun _ n => n.succ)

/-- Interpret standard zero and successor as strict zero and successor. -/
@[expose] public def fromStd : Nat → Omega.Nat :=
  Nat.rec .zero (fun _ n => n.succ)

public theorem toStd_fromStd (n : Nat) : toStd (fromStd n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ ih

public theorem fromStd_toStd (n : Omega.Nat) : fromStd (toStd n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Omega.Nat.succ ih

public theorem fromOmegaEq {α : Sort u} {a b : α} (h : Omega.Eq a b) : a = b :=
  Omega.Eq.rec rfl h

public theorem toStd_add (a b : Omega.Nat) :
    toStd (a.add b) = toStd a + toStd b := by
  induction b with
  | zero => exact (congrArg toStd (fromOmegaEq (Omega.Nat.add_zero a))).trans rfl
  | succ b ih =>
    exact (congrArg toStd (fromOmegaEq (Omega.Nat.add_succ a b))).trans (congrArg Nat.succ ih)

public theorem toStd_le_iff (a b : Omega.Nat) :
    toStd a ≤ toStd b ↔ Omega.Nat.le a b := by
  induction a generalizing b with
  | zero => exact ⟨fun _ => Omega.Nat.zero_le b, fun _ => Nat.zero_le (toStd b)⟩
  | succ a ih =>
    induction b using Omega.Nat.rec with
    | zero =>
      exact ⟨fun h => (Nat.not_succ_le_zero _ h).elim,
        fun h => Omega.False.elim (Omega.Nat.not_succ_le_zero a h)⟩
    | succ b _ =>
      exact Nat.succ_le_succ_iff.trans ((ih b).trans
        ⟨Omega.Nat.succ_le_succ, Omega.Nat.le_of_succ_le_succ⟩)

/-- Every strict Fibonacci value agrees with the pinned Mathlib definition. -/
public theorem toStd_fib (n : Omega.Nat) : toStd (Omega.Nat.fib n) = (toStd n).fib := by
  suffices h : toStd (Omega.Nat.fib n) = (toStd n).fib ∧
      toStd (Omega.Nat.fib n.succ) = (toStd n).succ.fib by
    exact h.1
  induction n with
  | zero =>
    rw [fromOmegaEq Omega.Nat.fib_zero, fromOmegaEq Omega.Nat.fib_one]
    exact ⟨rfl, rfl⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have recurrence : Omega.Nat.fib n.succ.succ = (Omega.Nat.fib n).add (Omega.Nat.fib n.succ) :=
      fromOmegaEq (Omega.Nat.fib_add_two (n := n))
    rw [recurrence, toStd_add, ih.1, ih.2]
    exact (Nat.fib_add_two (n := toStd n)).symm

/-- Every strict binomial coefficient agrees with the pinned Mathlib definition. -/
public theorem toStd_choose (n k : Omega.Nat) :
    toStd (Omega.Nat.choose n k) = (toStd n).choose (toStd k) := by
  induction n generalizing k with
  | zero =>
    induction k using Omega.Nat.rec with
    | zero => rw [fromOmegaEq (Omega.Nat.choose_zero_right _)]; rfl
    | succ k _ =>
      rw [fromOmegaEq (Omega.Nat.choose_zero_succ k)]
      exact (Nat.choose_zero_succ (toStd k)).symm
  | succ n ih =>
    induction k using Omega.Nat.rec with
    | zero =>
      rw [fromOmegaEq (Omega.Nat.choose_zero_right _)]
      exact (Nat.choose_zero_right (toStd n).succ).symm
    | succ k _ =>
      have recurrence : Omega.Nat.choose n.succ k.succ =
          (Omega.Nat.choose n k).add (Omega.Nat.choose n k.succ) :=
        fromOmegaEq (Omega.Nat.choose_succ_succ n k)
      rw [recurrence, toStd_add, ih k, ih k.succ]
      exact (Nat.choose_succ_succ (toStd n) (toStd k)).symm

end OmegaChecks.NatCorrespondence
