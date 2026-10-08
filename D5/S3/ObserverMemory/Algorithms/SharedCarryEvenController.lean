/- GID: D5/S3/ObserverMemory/Algorithms/SharedCarryEvenController
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/SharedCarryEvenController
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Even-base first-carry acquisition shares two read and wait controls per positive time. -/

import D5.S3.ObserverMemory.Algorithms.ActualControlSlots
import Mathlib.Data.Fintype.Sum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.SharedCarryEvenController

open ActualControlSlots

/-- One initial read, one wait/read pair per color, and all original labels. -/
@[reducible] def State (p P : Nat) (Colors : Type) :=
  Unit ⊕ ((Colors × Bool) ⊕ ZMod (p * P))

local notation "Root" => Sum.inl ()
local notation "W(" c ")" => Sum.inr (Sum.inl (c, false))
local notation "R(" c ")" => Sum.inr (Sum.inl (c, true))
local notation "H(" x ")" => Sum.inr (Sum.inr x)

/-- The time index is t-1; the second component is the initial digit's parity. -/
def color {p P : Nat} (b : Fin p) (t : Fin (P - 1)) : Fin (P - 1) × Fin 2 :=
  (t, ⟨b.val % 2, Nat.mod_lt _ (by decide)⟩)

/-- A total table: each row uses only its own color, index, and supplied digit. -/
def table (p P : Nat) : Controller p P (State p P (Fin (P - 1) × Fin 2)) where
  initial := Root
  action := fun q => match q with
    | .inl _ => .read
    | .inr (.inl (_, false)) => .wait
    | .inr (.inl (_, true)) => .read
    | .inr (.inr _) => .halt
  waitNext := fun q => match q with
    | .inr (.inl (c, false)) => R(c)
    | _ => q
  readNext := fun q d => match q with
    | .inl _ =>
        if h : 1 < P then W(color d ⟨0, by omega⟩)
        else H((d.val : Nat))
    | .inr (.inl (c, true)) =>
        if d.val % 2 = c.2.val then
          if h : c.1.val + 2 < P then W(color d ⟨c.1.val + 1, by omega⟩)
          else H((d.val * P : Nat))
        else H(((if d.val = 0 then p - 1 else d.val - 1) * P +
          (P - (c.1.val + 1)) : Nat))
    | _ => q
  output := fun q => match q with
    | .inr (.inr x) => x
    | _ => 0

/-- The number of waits before the first carry, capped at the last scan. -/
def waits {p P : Nat} (x : ZMod (p * P)) : Nat :=
  if x.val % P = 0 then P - 1 else P - x.val % P

section Execution

variable {p P : Nat} (hp : 2 ≤ p) (hP : 0 < P) (he : Even p)

include hP in
private theorem waits_bounds (x : ZMod (p * P)) :
    waits x < P ∧ (1 < P → 0 < waits x) := by
  have remainder := Nat.mod_lt x.val hP
  unfold waits
  split_ifs <;> omega

private theorem digit_shift (x : ZMod (p * P)) (t : Nat) (ht : t < P) :
    (digit hp hP (x + (t : ZMod (p * P)))).val =
      (x.val / P + if P ≤ x.val % P + t then 1 else 0) % p := by
  let : NeZero (p * P) := ⟨by positivity⟩
  change (x + (t : ZMod (p * P))).val / P = _
  rw [ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod]
  have moddiv := Nat.mod_mul_right_div_self (x.val + t) P p
  rw [show (x.val + t) % (p * P) / P = (x.val + t) / P % p by
    simpa only [Nat.mul_comm] using moddiv]
  rw [Nat.add_div hP,
    Nat.mod_eq_of_lt ht, Nat.div_eq_of_lt ht, Nat.add_zero]

include he in
private theorem carry_parity (b : Fin p) :
    ((b.val + 1) % p) % 2 ≠ b.val % 2 := by
  have divisible : 2 ∣ p := even_iff_two_dvd.mp he
  rw [Nat.mod_mod_of_dvd _ divisible]
  have opposite := Nat.mod_two_add_succ_mod_two b.val
  omega

private theorem carry_predecessor (b : Fin p) :
    (if (b.val + 1) % p = 0 then p - 1 else (b.val + 1) % p - 1) = b.val := by
  by_cases wrap : b.val + 1 = p
  · simp only [wrap, Nat.mod_self, ite_true]
    omega
  · have small : b.val + 1 < p := by omega
    rw [Nat.mod_eq_of_lt small, if_neg (by omega)]
    omega

private theorem before_digit (x : ZMod (p * P)) (t : Nat) (ht : t < waits x) :
    digit hp hP (x + (t : ZMod (p * P))) = digit hp hP x := by
  have small : t < P := lt_trans ht (waits_bounds hP x).1
  have no_carry : x.val % P + t < P := by
    have remainder := Nat.mod_lt x.val hP
    unfold waits at ht
    split_ifs at ht <;> omega
  apply Fin.ext
  rw [digit_shift hp hP x t small, if_neg (by omega), Nat.add_zero]
  exact Nat.mod_eq_of_lt (digit hp hP x).isLt

private theorem final_digit (x : ZMod (p * P)) (hn : x.val % P ≠ 0) :
    (digit hp hP (x + (waits x : ZMod (p * P)))).val =
      ((digit hp hP x).val + 1) % p := by
  have at_carry : P ≤ x.val % P + waits x := by
    have remainder := Nat.mod_lt x.val hP
    simp only [waits, if_neg hn]
    omega
  rw [digit_shift hp hP x (waits x) (waits_bounds hP x).1, if_pos at_carry]
  rfl

private theorem zero_digit (x : ZMod (p * P)) (hz : x.val % P = 0) :
    digit hp hP (x + (waits x : ZMod (p * P))) = digit hp hP x := by
  apply Fin.ext
  have small := (waits_bounds hP x).1
  rw [digit_shift hp hP x (waits x) small,
    if_neg (by omega), Nat.add_zero]
  exact Nat.mod_eq_of_lt (digit hp hP x).isLt

include he

/-- The row at time t+1 has one fixed answer for each supplied digit, even
when distinct histories reach the same color. -/
private theorem row_step (x : ZMod (p * P)) (t : Nat) (ht : t < waits x) :
    let i : Fin (P - 1) := ⟨t, by have := (waits_bounds hP x).1; omega⟩
    (table p P).readNext R(color (digit hp hP x) i)
      (digit hp hP (x + ((t + 1 : Nat) : ZMod (p * P)))) =
      if hn : t + 1 < waits x then
        W(color (digit hp hP x) ⟨t + 1, by have := (waits_bounds hP x).1; omega⟩)
      else H(x) := by
  dsimp only
  let b := digit hp hP x
  have remainder := Nat.mod_lt x.val hP
  have decomposition := Nat.mod_add_div x.val P
  have original : ((b.val * P + x.val % P : Nat) : ZMod (p * P)) = x := by
    let : NeZero (p * P) := ⟨by positivity⟩
    rw [show b.val * P + x.val % P = x.val by
        change x.val / P * P + x.val % P = x.val
        simpa only [Nat.add_comm, Nat.mul_comm] using decomposition,
      ZMod.natCast_zmod_val]
  by_cases early : t + 1 < waits x
  · rw [before_digit hp hP x (t + 1) early]
    simp only [table, color, ite_true, dif_pos early]
    rw [dif_pos (by have := (waits_bounds hP x).1; omega)]
  · have last : t + 1 = waits x := by omega
    rw [dif_neg early, last]
    by_cases zero : x.val % P = 0
    · rw [zero_digit hp hP x zero]
      simp only [table, color, ite_true]
      rw [dif_neg (by simp only [waits, if_pos zero] at last; omega)]
      congr 2
      simpa only [zero, Nat.add_zero] using original
    · have dig := final_digit hp hP x zero
      have parity := carry_parity he b
      have previous := carry_predecessor b
      simp only [table, color]
      have different : (digit hp hP (x + (waits x : ZMod (p * P)))).val % 2 ≠
          (digit hp hP x).val % 2 := by
        rw [dig]
        exact parity
      simp only [if_neg different]
      rw [dig, previous]
      have remaining : P - waits x = x.val % P := by
        simp only [waits, if_neg zero]
        omega
      simp only [last, remaining]
      exact congrArg (fun z : ZMod (p * P) => H(z)) original

omit he in
private theorem first_step (x : ZMod (p * P)) :
    (table p P).run hp hP x 1 =
      (x, if hn : 0 < waits x then
        W(color (digit hp hP x) ⟨0, by have := (waits_bounds hP x).1; omega⟩)
      else H(x)) := by
  simp only [Controller.run, Function.iterate_one, table, Controller.step]
  by_cases wide : 1 < P
  · rw [dif_pos wide, dif_pos ((waits_bounds hP x).2 wide)]
  · have one : P = 1 := by omega
    have zero : waits x = 0 := by have := (waits_bounds hP x).1; omega
    rw [dif_neg wide, dif_neg (by omega)]
    congr 2
    let : NeZero (p * P) := ⟨by positivity⟩
    have val : (digit hp hP x).val = x.val := by simp [digit, one]
    rw [val, ZMod.natCast_zmod_val]

/-- All actual odd prefixes retain the original source's label across shared rows. -/
private theorem odd_prefix (x : ZMod (p * P)) (t : Nat) (ht : t ≤ waits x) :
    (table p P).run hp hP x (2 * t + 1) =
      (x + (t : ZMod (p * P)), if hn : t < waits x then
        W(color (digit hp hP x) ⟨t, by have := (waits_bounds hP x).1; omega⟩)
      else H(x)) := by
  induction t with
  | zero => simpa using first_step hp hP x
  | succ t ih =>
    have before : t < waits x := by omega
    have prev := ih (by omega)
    rw [dif_pos before] at prev
    have time : 2 * (t + 1) + 1 = (2 * t + 1) + 1 + 1 := by omega
    rw [time]
    rw [Controller.run, Function.iterate_succ_apply', Function.iterate_succ_apply']
    change (table p P).step hp hP
      ((table p P).step hp hP ((table p P).run hp hP x (2 * t + 1))) = _
    rw [prev]
    simp only [Controller.step, table]
    have physical : x + (t : ZMod (p * P)) + 1 =
        x + ((t + 1 : Nat) : ZMod (p * P)) := by push_cast; ring
    rw [physical]
    exact Prod.ext rfl (row_step hp hP he x t before)

private theorem even_prefix (x : ZMod (p * P)) (t : Nat)
    (ht : 0 < t) (hl : t ≤ waits x) :
    (table p P).run hp hP x (2 * t) =
      (x + (t : ZMod (p * P)),
        R(color (digit hp hP x) ⟨t - 1, by have := (waits_bounds hP x).1; omega⟩)) := by
  have prev := odd_prefix hp hP he x (t - 1) (by omega)
  rw [dif_pos (by omega)] at prev
  have time : 2 * t = (2 * (t - 1) + 1) + 1 := by omega
  rw [time]
  rw [Controller.run, Function.iterate_succ_apply']
  change (table p P).step hp hP ((table p P).run hp hP x (2 * (t - 1) + 1)) = _
  rw [prev]
  simp only [Controller.step, table]
  apply Prod.ext
  · push_cast
    rw [show t = t - 1 + 1 by omega]
    push_cast
    ring
  · rfl

private theorem action_prefix (x : ZMod (p * P)) (t : Nat)
    (ht : t ≤ 2 * waits x) :
    (table p P).action ((table p P).run hp hP x t).2 =
      if t % 2 = 0 then .read else .wait := by
  have decomposition := Nat.mod_add_div t 2
  by_cases even : t % 2 = 0
  · rw [if_pos even]
    by_cases zero : t = 0
    · simp [zero, Controller.run, table]
    · have time : t = 2 * (t / 2) := by omega
      rw [time, even_prefix hp hP he x (t / 2) (by omega) (by omega)]
      rfl
  · rw [if_neg even]
    have time : t = 2 * (t / 2) + 1 := by omega
    have before : t / 2 < waits x := by omega
    rw [time, odd_prefix hp hP he x (t / 2) (by omega), dif_pos before]
    rfl

private def correct : (table p P).Correct hp hP := by
  refine {
    length := fun x => 2 * waits x + 1
    first_read := rfl
    halt := ?_
    output := ?_
    live := ?_
    after_read := ?_
    last_read := ?_ }
  · intro x
    rw [odd_prefix hp hP he x (waits x) le_rfl, dif_neg (lt_irrefl _)]
    rfl
  · intro x
    rw [odd_prefix hp hP he x (waits x) le_rfl, dif_neg (lt_irrefl _)]
    rfl
  · intro x t ht
    rw [action_prefix hp hP he x t (by omega)]
    split <;> intro h <;> cases h
  · intro x t ht hr
    rw [action_prefix hp hP he x t (by omega)] at hr
    have even : t % 2 = 0 := by
      by_contra bad
      rw [if_neg bad] at hr
      cases hr
    rw [action_prefix hp hP he x (t + 1) (by omega), if_neg (by omega)]
  · intro x
    rw [show 2 * waits x + 1 - 1 = 2 * waits x by omega,
      action_prefix hp hP he x (2 * waits x) le_rfl, if_pos (by omega)]

/-- Count issued actions before the certified halt, including the initial read. -/
noncomputable def eventCount {Q : Type} (C : Controller p P Q)
    (I : C.Correct hp hP) (x : ZMod (p * P)) (a : Action) : Nat := by
  classical
  exact ((Finset.range (I.length x)).filter
    (fun t => C.action (C.run hp hP x t).2 = a)).card

private theorem event_counts (x : ZMod (p * P)) :
    eventCount hp hP (table p P) (correct hp hP he) x .read = waits x + 1 ∧
    eventCount hp hP (table p P) (correct hp hP he) x .wait = waits x := by
  classical
  have reads : ((Finset.range (2 * waits x + 1)).filter
      (fun t => (table p P).action ((table p P).run hp hP x t).2 = .read)) =
      (Finset.range (waits x + 1)).image (fun t => 2 * t) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨ht, ha⟩
      rw [action_prefix hp hP he x t (by omega)] at ha
      have parity : t % 2 = 0 := by
        by_contra bad
        rw [if_neg bad] at ha
        cases ha
      have decomposition := Nat.mod_add_div t 2
      exact ⟨t / 2, by omega, by omega⟩
    · rintro ⟨n, hn, rfl⟩
      refine ⟨by omega, ?_⟩
      rw [action_prefix hp hP he x (2 * n) (by omega), if_pos (by omega)]
  have waiting : ((Finset.range (2 * waits x + 1)).filter
      (fun t => (table p P).action ((table p P).run hp hP x t).2 = .wait)) =
      (Finset.range (waits x)).image (fun t => 2 * t + 1) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨ht, ha⟩
      rw [action_prefix hp hP he x t (by omega)] at ha
      have parity : t % 2 ≠ 0 := by
        intro even
        rw [if_pos even] at ha
        cases ha
      have decomposition := Nat.mod_add_div t 2
      exact ⟨t / 2, by omega, by omega⟩
    · rintro ⟨n, hn, rfl⟩
      refine ⟨by omega, ?_⟩
      rw [action_prefix hp hP he x (2 * n + 1) (by omega), if_neg (by omega)]
  constructor
  · change ((Finset.range (2 * waits x + 1)).filter _).card = _
    rw [reads, Finset.card_image_of_injective]
    · exact Finset.card_range _
    · intro a b h
      dsimp at h
      omega
  · change ((Finset.range (2 * waits x + 1)).filter _).card = _
    rw [waiting, Finset.card_image_of_injective]
    · exact Finset.card_range _
    · intro a b h
      dsimp at h
      omega

omit he in
private theorem state_card (hp : 2 ≤ p) (hP : 0 < P) :
    Nat.card (State p P (Fin (P - 1) × Fin 2)) = p * P + 4 * P - 3 := by
  let : NeZero (p * P) := ⟨by positivity⟩
  let : Fintype (State p P (Fin (P - 1) × Fin 2)) := by
    unfold State
    infer_instance
  have nominal : Nat.card (State p P (Fin (P - 1) × Fin 2)) =
      1 + ((P - 1) * 2) * 2 + p * P := by
    simp [State, Nat.card_eq_fintype_card, Fintype.card_prod, ZMod.card, Nat.add_assoc]
  rw [nominal]
  omega

/-- For every even base and every positive width (in particular P=p^k),
one shared total table decodes every original source, has the exact nominal
capacity, and simultaneously attains the worst read and wait counts. -/
theorem result :
    ∃ I : (table p P).Correct hp hP,
      Nat.card (State p P (Fin (P - 1) × Fin 2)) = p * P + 4 * P - 3 ∧
      (∀ x, eventCount hp hP (table p P) I x .read ≤ P ∧
        eventCount hp hP (table p P) I x .wait ≤ P - 1) ∧
      (∃ x, eventCount hp hP (table p P) I x .read = P ∧
        eventCount hp hP (table p P) I x .wait = P - 1) ∧
      (P = 1 → Nat.card (State p P (Fin (P - 1) × Fin 2)) = p + 1) := by
  let I := correct hp hP he
  refine ⟨I, state_card hp hP, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨reads, waiting⟩ := event_counts hp hP he x
    rw [reads, waiting]
    have bound := (waits_bounds hP x).1
    omega
  · refine ⟨0, ?_⟩
    obtain ⟨reads, waiting⟩ := event_counts hp hP he (0 : ZMod (p * P))
    have last_wait : waits (0 : ZMod (p * P)) = P - 1 := by simp [waits]
    constructor
    · exact reads.trans (by rw [last_wait]; omega)
    · exact waiting.trans last_wait
  · intro one
    rw [state_card hp hP, one]
    omega

end Execution

end D5.S3.ObserverMemory.Algorithms.SharedCarryEvenController
