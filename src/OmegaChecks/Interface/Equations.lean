module

public import OmegaChecks.Interface.Equations.Logic
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Prime.Defs

/-! Pointwise equations for strict arithmetic algorithms interpreted over official types. -/

namespace OmegaChecks.Interface.Equations

@[expose] public def pair (n : Nat) : Bool → Nat :=
  Nat.rec (motive := fun _ => Bool → Nat) (Bool.rec 0 1)
    (fun _ p => Bool.rec (p true) (p true + p false)) n

public theorem Nat.fib (n : Nat) : pair n false = n.fib := by
  suffices h : pair n false = n.fib ∧ pair n true = n.succ.fib from h.1
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    change pair n true + pair n false = n.succ.succ.fib
    rw [ih.1, ih.2, _root_.Nat.fib_add_two, _root_.Nat.add_comm]

@[expose] public def pascal (n k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (Nat.rec 1 (fun _ _ => 0))
    (fun _ previous => Nat.rec 1 (fun j _ => previous j + previous j.succ)) n k

public theorem Nat.choose (n k : Nat) : pascal n k = n.choose k := by
  induction n generalizing k with
  | zero => cases k <;> rfl
  | succ n ih =>
    cases k with
    | zero => rfl
    | succ k =>
      change pascal n k + pascal n k.succ = n.succ.choose k.succ
      rw [ih, ih, _root_.Nat.choose_succ_succ]

public theorem Nat.add (a b : Nat) :
    Nat.rec a (fun _ r => Nat.succ r) b = a + b := by
  induction b with
  | zero => rfl
  | succ b ih => exact congrArg Nat.succ ih

public theorem Nat.le (a b : Nat) :
    Nat.rec (motive := fun _ => Nat → Prop) (fun _ => True)
      (fun _ smaller n => Nat.rec (motive := fun _ => Prop) False (fun k _ => smaller k) n) a b
      = (a ≤ b) := by
  apply propext
  induction a generalizing b with
  | zero => exact ⟨fun _ => Nat.zero_le b, fun _ => True.intro⟩
  | succ a ih =>
    cases b with
    | zero => exact ⟨False.elim, Nat.not_succ_le_zero _⟩
    | succ b => exact (ih b).trans Nat.succ_le_succ_iff.symm

/-- Recursively cancel common successors before constructing the signed difference. -/
@[expose] public def difference (m n : Nat) : Int :=
  Nat.rec (motive := fun _ => Nat → Int) Int.negOfNat
    (fun a diff b => Nat.rec (Int.ofNat a.succ) (fun k _ => diff k) b) m n

public theorem Int.subNatNat (m n : Nat) : difference m n = _root_.Int.subNatNat m n := by
  induction m generalizing n with
  | zero => cases n <;> simp [difference, _root_.Int.negOfNat, _root_.Int.subNatNat]
  | succ m ih =>
    cases n with
    | zero => simp [difference, _root_.Int.subNatNat]
    | succ n => simpa [difference, _root_.Int.subNatNat] using ih n

/-- The divisor characterization computes the pinned prime predicate at every input. -/
public theorem Nat.Prime (p : Nat) :
    (2 ≤ p ∧ ∀ m, (∃ k, p = m * k) → m = 1 ∨ m = p) = _root_.Nat.Prime p :=
  propext _root_.Nat.prime_def.symm

end OmegaChecks.Interface.Equations
