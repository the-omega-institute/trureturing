/- GID: D5/S3/ObserverMemory/Algorithms/DedicatedPairReplacement
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/DedicatedPairReplacement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two physical reads replace disjoint adjacent-pair suffixes by one shared table. -/

import D5.S3.Observer.Budget.FinitePositiveIntervalControl
import Mathlib.Data.Fintype.Sum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.DedicatedPairReplacement

open ActualControlSlots (Action Controller digit)
open D5.S3.Observer.Budget.FinitePositiveIntervalControl (Follows)

variable {p P d : Nat} {E : Type}

local notation "Old" => E ⊕ (Fin p × Fin (d + 1))
local notation "Internal" => Fin d ⊕ (Fin p × Fin 2)
local notation "New" => E ⊕ Internal

/-- The common countdown ends in its zero reading state. -/
def entry (hd : 0 < d) : Internal := .inl ⟨d - 1, by omega⟩

/-- All removed states are redirected to the same entry. Only old entries
are encountered on the affected exterior paths. -/
def redirect (hd : 0 < d) : Old → New
  | .inl e => .inl e
  | .inr _ => .inr (entry hd)

/-- A successor digit is cyclic, including the last source block. -/
private def nextDigit (hp : 2 ≤ p) (b : Fin p) : Fin p :=
  ⟨(b.val + 1) % p, Nat.mod_lt _ (by omega)⟩

/-- The old internal carrier is p disjoint countdowns. Zero is the final
read, and every positive index is one charged unit wait. -/
structure Dedicated (hp : 2 ≤ p) (C : Controller p P Old)
    (labels : Fin p × Fin 2 → E) : Prop where
  waiting : ∀ b i, 0 < i.val → C.action (.inr (b, i)) = .wait
  advance : ∀ b i (hi : 0 < i.val),
    C.waitNext (.inr (b, i)) = .inr (b, ⟨i.val - 1, by omega⟩)
  reading : ∀ b, C.action (.inr (b, 0)) = .read
  lower : ∀ b, C.readNext (.inr (b, 0)) b = .inl (labels (b, 0))
  upper : ∀ b, C.readNext (.inr (b, 0)) (nextDigit hp b) = .inl (labels (b, 1))
  terminal : ∀ b e, C.action (.inl (labels (b, e))) = .halt

/-- Exterior rows and their outputs are retained. The shared chain stores
no branch; its physical read chooses a charged branch wait and branch read.
Unused digit rows go to a pre-existing terminal label. -/
def table (hp : 2 ≤ p) (hd : 0 < d) (C : Controller p P Old)
    (labels : Fin p × Fin 2 → E) : Controller p P New where
  initial := redirect hd C.initial
  action
    | .inl e => C.action (.inl e)
    | .inr (.inl i) => if i.val = 0 then .read else .wait
    | .inr (.inr (_, e)) => if e = 0 then .wait else .read
  waitNext
    | .inl e => redirect hd (C.waitNext (.inl e))
    | .inr (.inl i) => .inr (.inl ⟨i.val - 1, by omega⟩)
    | .inr (.inr (b, _)) => .inr (.inr (b, 1))
  readNext
    | .inl e, b => redirect hd (C.readNext (.inl e) b)
    | .inr (.inl _), b => .inr (.inr (b, 0))
    | .inr (.inr (b, _)), a =>
        .inl (labels (b, if a = b then 0 else if a = nextDigit hp b then 1 else 0))
  output
    | .inl e => C.output (.inl e)
    | .inr _ => C.output (.inl (labels (⟨0, by omega⟩, 0)))

private theorem pair_digits (hp : 2 ≤ p) (hP : 3 ≤ P) (L : Nat)
    (hL : L ≤ P - 3) (b : Fin p) (e : Fin 2) :
    digit hp (by omega) (((b.val * P + L + e.val + (P - L - 1 - 1) : Nat) :
      ZMod (p * P))) = b ∧
    digit hp (by omega) (((b.val * P + L + e.val + (P - L - 1) : Nat) :
      ZMod (p * P))) = if e = 0 then b else nextDigit hp b := by
  have hpos : 0 < P := by omega
  have early : P - L - 1 - 1 < P := by omega
  have last : P - L - 1 < P := by omega
  have law := (D5.S3.Observer.Budget.PositiveIntervalAcquisition.result p P hp hpos).choose_spec.2.1
  have first := (law b.val (P - L - 1 - 1) (L + e.val) (by omega)).1
  have final := (law b.val (P - L - 1) (L + e.val) (by omega)).1
  have first_cut :
      D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.threshold
        P (P - L - 1 - 1) (L + e.val) = 0 := by
    simp only [D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.threshold,
      Nat.mod_eq_of_lt early]
    rw [if_pos (by omega)]
  have final_cut :
      D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.threshold
        P (P - L - 1) (L + e.val) = e := by
    fin_cases e <;>
      simp [D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.threshold,
        Nat.mod_eq_of_lt last, show P - (P - L - 1) = L + 1 by omega]
  simp only [first_cut, Nat.div_eq_of_lt early, Fin.val_zero, Nat.add_zero,
    Nat.mod_eq_of_lt b.isLt] at first
  rw [final_cut, Nat.div_eq_of_lt last, Nat.add_zero] at final
  constructor
  · apply Fin.ext
    change (((b.val * P + L + e.val + (P - L - 1 - 1) : Nat) :
      ZMod (p * P))).val / P = b.val
    rw [ZMod.val_natCast]
    simpa only [Nat.add_assoc] using first
  · apply Fin.ext
    change (((b.val * P + L + e.val + (P - L - 1) : Nat) :
      ZMod (p * P))).val / P = _
    rw [ZMod.val_natCast]
    rw [show b.val * P + L + e.val = b.val * P + (L + e.val) by omega, final]
    fin_cases e <;> simp [nextDigit, Nat.mod_eq_of_lt b.isLt]

private theorem common_chain (hp : 2 ≤ p) (hP : 0 < P) (hd : 0 < d)
    (C : Controller p P Old) (labels : Fin p × Fin 2 → E)
    (n : Nat) (hn : n < d) (s : ZMod (p * P)) (tail : List Action)
    (z : ZMod (p * P) × New)
    (ht : Follows (table hp hd C labels) hp hP
      (s + (n : ZMod (p * P)), .inr (.inl ⟨0, hd⟩)) tail z) :
    Follows (table hp hd C labels) hp hP (s, .inr (.inl ⟨n, hn⟩))
      (List.replicate n Action.wait ++ tail) z := by
  induction n generalizing s with
  | zero => simpa using ht
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, Follows]
    refine ⟨by simp [table], ?_⟩
    simp only [Controller.step, table, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    apply ih (by omega) (s + 1)
    simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using ht

private theorem nextDigit_ne (hp : 2 ≤ p) (b : Fin p) : nextDigit hp b ≠ b := by
  intro he
  have hv := congrArg Fin.val he
  change (b.val + 1) % p = b.val at hv
  by_cases h : b.val + 1 < p
  · rw [Nat.mod_eq_of_lt h] at hv
    omega
  · rw [show b.val + 1 = p by omega, Nat.mod_self] at hv
    omega

private theorem shared_suffix (hp : 2 ≤ p) (hP : 3 ≤ P) (L : Nat)
    (hL : L ≤ P - 3) (C : Controller p P (E ⊕ (Fin p × Fin (P - L - 1 + 1))))
    (labels : Fin p × Fin 2 → E) (b : Fin p) (e : Fin 2) :
    let d := P - L - 1
    let hd : 0 < d := by omega
    let T := table hp hd C labels
    let s : ZMod (p * P) := (b.val * P + L + e.val : Nat)
    Follows T hp (by omega) (s, .inr (entry hd))
      (List.replicate (d - 1) Action.wait ++ [Action.read, Action.wait, Action.read])
      (s + (d : ZMod (p * P)), .inl (labels (b, e))) := by
  dsimp only
  let d := P - L - 1
  have hd : 0 < d := by dsimp [d]; omega
  let T := table hp hd C labels
  let s : ZMod (p * P) := (b.val * P + L + e.val : Nat)
  have digits := pair_digits hp hP L hL b e
  have first : digit hp (by omega) (s + ((d - 1 : Nat) : ZMod (p * P))) = b := by
    simpa [s, d, Nat.cast_add] using digits.1
  have final : digit hp (by omega) (s + (d : ZMod (p * P))) =
      if e = 0 then b else nextDigit hp b := by
    simpa [s, d, Nat.cast_add] using digits.2
  have phase : s + ((d - 1 : Nat) : ZMod (p * P)) + 1 = s + (d : ZMod (p * P)) := by
    calc
      _ = s + (((d - 1 + 1 : Nat) : ZMod (p * P))) := by
        simp only [Nat.cast_add, Nat.cast_one, add_assoc]
      _ = s + (d : ZMod (p * P)) := by rw [Nat.sub_add_cancel hd]
  have tail : Follows T hp (by omega)
      (s + ((d - 1 : Nat) : ZMod (p * P)), .inr (.inl ⟨0, hd⟩))
      [Action.read, Action.wait, Action.read]
      (s + (d : ZMod (p * P)), .inl (labels (b, e))) := by
    fin_cases e <;> simp [Follows, Controller.step, T, table, first, phase, final,
      nextDigit_ne hp b]
  exact common_chain hp (by omega) hd C labels (d - 1) (by omega) s _ _ tail

private theorem dedicated_chain (hp : 2 ≤ p) (hP : 0 < P)
    (C : Controller p P Old) (labels : Fin p × Fin 2 → E)
    (H : Dedicated hp C labels) (b : Fin p) (n : Nat) (hn : n ≤ d)
    (s : ZMod (p * P)) (tail : List Action) (z : ZMod (p * P) × Old)
    (ht : Follows C hp hP (s + (n : ZMod (p * P)), .inr (b, 0)) tail z) :
    Follows C hp hP (s, .inr (b, ⟨n, by omega⟩))
      (List.replicate n Action.wait ++ tail) z := by
  induction n generalizing s with
  | zero => simpa using ht
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, Follows]
    have ha := H.waiting b (⟨n + 1, by omega⟩ : Fin (d + 1)) (by simp)
    have hs := H.advance b (⟨n + 1, by omega⟩ : Fin (d + 1)) (by simp)
    refine ⟨ha, ?_⟩
    simp only [Controller.step, ha, hs,
      Nat.add_sub_cancel]
    apply ih (by omega) (s + 1)
    simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using ht

private theorem old_suffix (hp : 2 ≤ p) (hP : 3 ≤ P) (L : Nat)
    (hL : L ≤ P - 3) (C : Controller p P (E ⊕ (Fin p × Fin (P - L - 1 + 1))))
    (labels : Fin p × Fin 2 → E) (H : Dedicated hp C labels) (b : Fin p) (e : Fin 2) :
    let d := P - L - 1
    let s : ZMod (p * P) := (b.val * P + L + e.val : Nat)
    Follows C hp (by omega) (s, .inr (b, ⟨d, by omega⟩))
      (List.replicate d Action.wait ++ [Action.read])
      (s + (d : ZMod (p * P)), .inl (labels (b, e))) := by
  dsimp only
  let d := P - L - 1
  let s : ZMod (p * P) := (b.val * P + L + e.val : Nat)
  have final : digit hp (by omega) (s + (d : ZMod (p * P))) =
      if e = 0 then b else nextDigit hp b := by
    simpa [s, d, Nat.cast_add] using (pair_digits hp hP L hL b e).2
  apply dedicated_chain hp (by omega) C labels H b d le_rfl s
  rw [Follows, H.reading]
  refine ⟨rfl, ?_⟩
  simp only [Controller.step, H.reading, final, Follows]
  fin_cases e <;> simp [H.lower, H.upper, s, d, Nat.cast_add]

private theorem follows_endpoint {Q : Type} (C : Controller p P Q)
    (hp : 2 ≤ p) (hP : 0 < P) (word : List Action)
    (c z : ZMod (p * P) × Q) (H : Follows C hp hP c word z) :
    (C.step hp hP)^[word.length] c = z := by
  induction word generalizing c with
  | nil => exact H
  | cons a word ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    exact ih _ H.2

private theorem exterior_step (hp : 2 ≤ p) (hP : 0 < P) (hd : 0 < d)
    (C : Controller p P Old) (labels : Fin p × Fin 2 → E)
    (s : ZMod (p * P)) (e : E) :
    (table hp hd C labels).step hp hP (s, .inl e) =
      Prod.map id (redirect hd) (C.step hp hP (s, .inl e)) := by
  cases ha : C.action (.inl e) <;> simp [Controller.step, table, ha, redirect]

private theorem exterior_prefix (hp : 2 ≤ p) (hP : 0 < P) (hd : 0 < d)
    (C : Controller p P Old) (labels : Fin p × Fin 2 → E)
    (c : ZMod (p * P) × Old) (n : Nat)
    (H : ∀ i, i < n → ∃ e : E, ((C.step hp hP)^[i] c).2 = .inl e) :
    ((table hp hd C labels).step hp hP)^[n] (Prod.map id (redirect hd) c) =
      Prod.map id (redirect hd) ((C.step hp hP)^[n] c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      ih (fun i hi => H i (by omega))]
    obtain ⟨e, he⟩ := H n (by omega)
    have hc : (C.step hp hP)^[n] c = (((C.step hp hP)^[n] c).1, .inl e) :=
      Prod.ext rfl he
    rw [hc]
    exact exterior_step hp hP hd C labels _ e

end D5.S3.ObserverMemory.Algorithms.DedicatedPairReplacement
