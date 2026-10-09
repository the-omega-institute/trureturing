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

set_option quotPrecheck false in
local notation "nextDigit(" hp "," b ")" =>
  Fin.mk ((Fin.val b + 1) % p) (Nat.mod_lt _ (Nat.lt_of_lt_of_le (by decide : 0 < 2) hp))

/-- The old internal carrier is p disjoint countdowns. Zero is the final
read, and every positive index is one charged unit wait. -/
structure Dedicated (hp : 2 ≤ p) (C : Controller p P Old)
    (labels : Fin p × Fin 2 → E) : Prop where
  waiting : ∀ b i, 0 < i.val → C.action (.inr (b, i)) = .wait
  advance : ∀ b i (hi : 0 < i.val),
    C.waitNext (.inr (b, i)) = .inr (b, ⟨i.val - 1, by omega⟩)
  reading : ∀ b, C.action (.inr (b, 0)) = .read
  lower : ∀ b, C.readNext (.inr (b, 0)) b = .inl (labels (b, 0))
  upper : ∀ b, C.readNext (.inr (b, 0)) (nextDigit(hp, b)) = .inl (labels (b, 1))
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
        .inl (labels (b, if a = b then 0 else if a = nextDigit(hp, b) then 1 else 0))
  output
    | .inl e => C.output (.inl e)
    | .inr _ => C.output (.inl (labels (⟨0, by omega⟩, 0)))

private theorem pair_digits (hp : 2 ≤ p) (hP : 3 ≤ P) (L : Nat)
    (hL : L ≤ P - 3) (b : Fin p) (e : Fin 2) :
    digit hp (by omega) (((b.val * P + L + e.val + (P - L - 1 - 1) : Nat) :
      ZMod (p * P))) = b ∧
    digit hp (by omega) (((b.val * P + L + e.val + (P - L - 1) : Nat) :
      ZMod (p * P))) = if e = 0 then b else nextDigit(hp, b) := by
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
    fin_cases e <;> simp [Nat.mod_eq_of_lt b.isLt]

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

private theorem nextDigit_ne (hp : 2 ≤ p) (b : Fin p) : nextDigit(hp, b) ≠ b := by
  let : NeZero p := ⟨by omega⟩
  have one : (1 : Fin p) ≠ 0 := by
    simp [Fin.ext_iff, Nat.mod_eq_of_lt (by omega : 1 < p)]
  simpa [Fin.add_def, Fin.val_one, Nat.mod_eq_of_lt (by omega : 1 < p)] using
    (add_ne_left.mpr one : b + 1 ≠ b)

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
      if e = 0 then b else nextDigit(hp, b) := by
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
      if e = 0 then b else nextDigit(hp, b) := by
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

private theorem follows_live {Q : Type} (C : Controller p P Q)
    (hp : 2 ≤ p) (hP : 0 < P) (word : List Action)
    (c z : ZMod (p * P) × Q) (H : Follows C hp hP c word z)
    (live : ∀ a ∈ word, a ≠ Action.halt) (i : Nat) (hi : i < word.length) :
    C.action (((C.step hp hP)^[i] c).2) ≠ .halt := by
  induction word generalizing c i with
  | nil => simp at hi
  | cons a word ih =>
    cases i with
    | zero => simpa only [Function.iterate_zero, id_eq, H.1] using live a (by simp)
    | succ i =>
      rw [Function.iterate_succ_apply]
      exact ih _ H.2 (fun a ha => live a (by simp [ha])) i (by simpa using hi)

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

/-- The two-read shared table, its charged carrier, and its exterior path
bridge all use the same controller and arbitrary preassigned terminal labels. -/
theorem result (p P L : Nat) (hp : 2 ≤ p) (hP : 3 ≤ P) (hL : L ≤ P - 3)
    (E : Type) [Finite E] (labels : Fin p × Fin 2 → E)
    (C : Controller p P (E ⊕ (Fin p × Fin (P - L - 1 + 1))))
    (H : Dedicated hp C labels) :
    let d := P - L - 1
    let hd : 0 < d := by omega
    let q : E ⊕ (Fin d ⊕ (Fin p × Fin 2)) := .inr (.inl ⟨0, hd⟩)
    let word := List.replicate (d - 1) Action.wait ++ [Action.read, Action.wait, Action.read]
    ∃ T : Controller p P (E ⊕ (Fin d ⊕ (Fin p × Fin 2))),
      T.initial = redirect hd C.initial ∧
      (∀ e, T.action (.inl e) = C.action (.inl e) ∧
        T.output (.inl e) = C.output (.inl e) ∧
        T.waitNext (.inl e) = redirect hd (C.waitNext (.inl e)) ∧
        ∀ a, T.readNext (.inl e) a = redirect hd (C.readNext (.inl e) a)) ∧
      Nat.card (Fin p × Fin (d + 1)) = p * (d + 1) ∧
      Nat.card (Fin d ⊕ (Fin p × Fin 2)) = d + 2 * p ∧
      Nat.card (E ⊕ (Fin p × Fin (d + 1))) = Nat.card E + p * (d + 1) ∧
      Nat.card (E ⊕ (Fin d ⊕ (Fin p × Fin 2))) = Nat.card E + (d + 2 * p) ∧
      ((p * (d + 1) : Nat) : Int) - ((d + 2 * p : Nat) : Int) =
        ((p - 1 : Nat) : Int) * (d : Int) - (p : Int) ∧
      (d + 2 * p < p * (d + 1) ↔ 0 < ((p - 1 : Nat) : Int) * (d : Int) - (p : Int)) ∧
      word.countP (fun a => match a with | .wait => true | _ => false) = d ∧
      word.countP (fun a => match a with | .read => true | _ => false) = 2 ∧
      (∀ b e,
        let s : ZMod (p * P) := (b.val * P + L + e.val : Nat)
        Follows T hp (by omega) (s, .inr (entry hd))
          (List.replicate (d - 1) Action.wait) (s + ((d - 1 : Nat) : ZMod (p * P)), q) ∧
        digit hp (by omega) (s + ((d - 1 : Nat) : ZMod (p * P))) = b ∧
        T.action q = .read ∧
        T.readNext q b = .inr (.inr (b, 0)) ∧
        T.action (.inr (.inr (b, 0))) = .wait ∧
        T.waitNext (.inr (.inr (b, 0))) = .inr (.inr (b, 1)) ∧
        T.action (.inr (.inr (b, 1))) = .read ∧
        Follows T hp (by omega) (s, .inr (entry hd)) word
          (s + (d : ZMod (p * P)), .inl (labels (b, e))) ∧
        (T.step hp (by omega))^[d + 2] (s, .inr (entry hd)) =
          (s + (d : ZMod (p * P)), .inl (labels (b, e))) ∧
        (∀ i, i < d + 2 → T.action (((T.step hp (by omega))^[i]
          (s, .inr (entry hd))).2) ≠ .halt) ∧
        T.action (.inl (labels (b, e))) = .halt ∧
        T.output (.inl (labels (b, e))) = C.output (.inl (labels (b, e)))) ∧
      (∀ (c : ZMod (p * P) × (E ⊕ (Fin p × Fin (d + 1)))) n,
        (∀ i, i < n → ∃ e : E, ((C.step hp (by omega))^[i] c).2 = .inl e) →
        (T.step hp (by omega))^[n] (Prod.map id (redirect hd) c) =
          Prod.map id (redirect hd) ((C.step hp (by omega))^[n] c) ∧
        ∀ i, i < n → T.action (((T.step hp (by omega))^[i]
          (Prod.map id (redirect hd) c)).2) = C.action (((C.step hp (by omega))^[i] c).2)) ∧
      (∀ (c : ZMod (p * P) × (E ⊕ (Fin p × Fin (d + 1)))) n (b : Fin p) (e : Fin 2),
        (∀ i, i < n → ∃ f : E, ((C.step hp (by omega))^[i] c).2 = .inl f) →
        (C.step hp (by omega))^[n] c =
          (((b.val * P + L + e.val : Nat) : ZMod (p * P)), .inr (b, ⟨d, by omega⟩)) →
        (C.step hp (by omega))^[n + (d + 1)] c =
          (((b.val * P + L + e.val : Nat) : ZMod (p * P)) + (d : ZMod (p * P)),
            .inl (labels (b, e))) ∧
        (T.step hp (by omega))^[n + (d + 2)] (Prod.map id (redirect hd) c) =
          (((b.val * P + L + e.val : Nat) : ZMod (p * P)) + (d : ZMod (p * P)),
            .inl (labels (b, e))) ∧
        C.output (((C.step hp (by omega))^[n + (d + 1)] c).2) =
          T.output (((T.step hp (by omega))^[n + (d + 2)]
            (Prod.map id (redirect hd) c)).2)) := by
  classical
  let : Fintype E := Fintype.ofFinite E
  dsimp only
  let d := P - L - 1
  have hd : 0 < d := by dsimp [d]; omega
  have hpos : 0 < P := by omega
  let T := table hp hd C labels
  let q : E ⊕ (Fin d ⊕ (Fin p × Fin 2)) := .inr (.inl ⟨0, hd⟩)
  let word := List.replicate (d - 1) Action.wait ++ [Action.read, Action.wait, Action.read]
  have length : word.length = d + 2 := by simp [word]; omega
  have fee : ((p * (d + 1) : Nat) : Int) - ((d + 2 * p : Nat) : Int) =
      ((p - 1 : Nat) : Int) * (d : Int) - (p : Int) := by
    rw [Nat.cast_sub (by omega : 1 ≤ p)]
    push_cast
    ring
  refine ⟨T, rfl, ?_, ?_, ?_, ?_, ?_, fee, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e
    exact ⟨rfl, rfl, rfl, fun _ => rfl⟩
  · simp [Nat.card_eq_fintype_card]
  · simp [Nat.card_eq_fintype_card, mul_comm]
  · simp [Nat.card_eq_fintype_card]
  · simp [Nat.card_eq_fintype_card, mul_comm]
  · rw [← fee]
    rw [sub_pos]
    norm_cast
  · simp [List.countP_replicate]; omega
  · simp [List.countP_replicate]
  · intro b e
    let s : ZMod (p * P) := (b.val * P + L + e.val : Nat)
    have run := shared_suffix hp hP L hL C labels b e
    change Follows T hp hpos (s, .inr (entry hd)) word
      (s + (d : ZMod (p * P)), .inl (labels (b, e))) at run
    have first : digit hp hpos (s + ((d - 1 : Nat) : ZMod (p * P))) = b := by
      simpa [s, d, Nat.cast_add] using (pair_digits hp hP L hL b e).1
    have front := common_chain hp hpos hd C labels (d - 1) (by omega) s []
      (s + ((d - 1 : Nat) : ZMod (p * P)), q) rfl
    simp only [List.append_nil] at front
    refine ⟨front, first, rfl, rfl, rfl, rfl, by simp [T, table], run, ?_, ?_,
      H.terminal b e, rfl⟩
    · simpa only [length] using follows_endpoint T hp hpos word _ _ run
    · intro i hi
      apply follows_live T hp hpos word _ _ run
      · intro a ha
        cases a <;> simp_all [word]
      · omega
  · intro c n hc
    refine ⟨exterior_prefix hp hpos hd C labels c n hc, ?_⟩
    intro i hi
    rw [exterior_prefix hp hpos hd C labels c i (fun j hj => hc j (by omega))]
    obtain ⟨e, he⟩ := hc i hi
    simp only [Prod.map, id_eq, he, redirect]
    rfl
  · intro c n b e hc he
    have old := old_suffix hp hP L hL C labels H b e
    have new := shared_suffix hp hP L hL C labels b e
    have oldend := follows_endpoint C hp hpos _ _ _ old
    have newend := follows_endpoint T hp hpos _ _ _ new
    have oldlen : (List.replicate d Action.wait ++ [Action.read]).length = d + 1 := by simp
    rw [oldlen] at oldend
    rw [length] at newend
    have lifted := exterior_prefix hp hpos hd C labels c n hc
    rw [he] at lifted
    have oldwhole : (C.step hp hpos)^[n + (d + 1)] c =
        (((b.val * P + L + e.val : Nat) : ZMod (p * P)) + (d : ZMod (p * P)),
          .inl (labels (b, e))) := by
      rw [Nat.add_comm n (d + 1), Function.iterate_add_apply, he]
      exact oldend
    have newwhole : (T.step hp hpos)^[n + (d + 2)] (Prod.map id (redirect hd) c) =
        (((b.val * P + L + e.val : Nat) : ZMod (p * P)) + (d : ZMod (p * P)),
          .inl (labels (b, e))) := by
      rw [Nat.add_comm n (d + 2), Function.iterate_add_apply, lifted]
      exact newend
    exact ⟨oldwhole, newwhole, by rw [oldwhole, newwhole]; rfl⟩

end D5.S3.ObserverMemory.Algorithms.DedicatedPairReplacement
