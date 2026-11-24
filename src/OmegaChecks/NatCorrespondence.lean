/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import OmegaMath.Data.Nat.Choose.Basic
public import OmegaMath.Data.Nat.Fib.Basic

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

public theorem toStd_add (a b : Omega.Nat) :
    toStd (a.add b) = toStd a + toStd b := by
  induction b with
  | zero => rfl
  | succ b ih => exact congrArg Nat.succ ih

public theorem toStd_le_iff (a b : Omega.Nat) :
    toStd a ≤ toStd b ↔ Omega.Nat.le a b := by
  induction a generalizing b with
  | zero => exact ⟨fun _ => Omega.Nat.zero_le b, fun _ => Nat.zero_le (toStd b)⟩
  | succ a ih =>
    induction b using Omega.Nat.rec with
    | zero =>
      exact ⟨fun h => (Nat.not_succ_le_zero _ h).elim, fun h => Omega.False.elim h⟩
    | succ b _ => exact Nat.succ_le_succ_iff.trans (ih b)

/-- Every strict Fibonacci value agrees with the pinned Mathlib definition. -/
public theorem toStd_fib (n : Omega.Nat) : toStd n.fib = (toStd n).fib := by
  suffices h : toStd n.fib = (toStd n).fib ∧
      toStd n.succ.fib = (toStd n).succ.fib by
    exact h.1
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have recurrence : n.succ.succ.fib = n.fib.add n.succ.fib :=
      Omega.Eq.rec rfl Omega.Nat.fib_add_two
    rw [recurrence, toStd_add, ih.1, ih.2]
    exact (Nat.fib_add_two (n := toStd n)).symm

/-- Every strict binomial coefficient agrees with the pinned Mathlib definition. -/
public theorem toStd_choose (n k : Omega.Nat) :
    toStd (n.choose k) = (toStd n).choose (toStd k) := by
  induction n generalizing k with
  | zero =>
    induction k using Omega.Nat.rec with
    | zero => rfl
    | succ k _ => exact (Nat.choose_zero_succ (toStd k)).symm
  | succ n ih =>
    induction k using Omega.Nat.rec with
    | zero => exact (Nat.choose_zero_right (toStd n).succ).symm
    | succ k _ =>
      have recurrence : n.succ.choose k.succ = (n.choose k).add (n.choose k.succ) :=
        Omega.Eq.rec rfl (Omega.Nat.choose_succ_succ n k)
      rw [recurrence, toStd_add, ih k, ih k.succ]
      exact (Nat.choose_succ_succ (toStd n) (toStd k)).symm

end OmegaChecks.NatCorrespondence
