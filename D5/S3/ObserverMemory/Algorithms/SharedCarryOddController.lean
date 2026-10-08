/- GID: D5/S3/ObserverMemory/Algorithms/SharedCarryOddController
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/SharedCarryOddController
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Odd-base first-carry acquisition shares time blocks through near-perfect matchings. -/

import D5.S3.ObserverMemory.Algorithms.SharedCarryEvenController
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.SuccPred

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.SharedCarryOddController

open ActualControlSlots
open SharedCarryEvenController

variable (a P : Nat) (ha : 0 < a) (hd : a ∣ P - 1)

local notation "p" => (2 * a + 1)
local notation "Colors" => (Fin ((P - 1) / a) × ZMod p)
local notation "Q" => State p P Colors
local notation "Root" => Sum.inl ()
local notation "W(" c ")" => Sum.inr (Sum.inl (c, false))
local notation "R(" c ")" => Sum.inr (Sum.inl (c, true))
local notation "H(" x ")" => Sum.inr (Sum.inr x)

/-- Time t is represented by i=t-1. Each color omits just its second digit. -/
def color (b : Fin p) (i : Fin (P - 1)) : Colors :=
  (⟨i.val / a, (Nat.div_lt_iff_lt_mul ha).mpr
      (by simpa only [Nat.div_mul_cancel hd] using i.isLt)⟩,
   (b.val : ZMod p) - ((2 * (i.val % a) + 1 : Nat) : ZMod p))

local notation "col" => color a P ha hd

/-- The stationary row reverses its matching color and the observed digit.
Zero relative digit is unused and selects the existing zero halt label. -/
def table : Controller p P Q where
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
        if h : 1 < P then W(col d ⟨0, by omega⟩)
        else H((d.val : Nat))
    | .inr (.inl (c, true)) =>
        let j := ((d.val : ZMod p) - c.2).val
        let i := c.1.val * a + (j - 1) / 2
        if j = 0 then H(0)
        else if j % 2 = 1 then
          if h : i + 2 < P then W(col d ⟨i + 1, by omega⟩)
          else H((d.val * P : Nat))
        else H(((if d.val = 0 then p - 1 else d.val - 1) * P +
          (P - (i + 1)) : Nat))
    | .inr (.inl (_, false)) => H(0)
    | .inr (.inr _) => q
  output := fun q => match q with
    | .inr (.inr x) => x
    | _ => 0

private theorem matching_offsets (b : Fin p) (i : Fin (P - 1)) :
    ((b.val : ZMod p) - (col b i).2).val = 2 * (i.val % a) + 1 ∧
    ((((b.val + 1) % p : Nat) : ZMod p) - (col b i).2).val =
      2 * (i.val % a) + 2 := by
  have small := Nat.mod_lt i.val ha
  have first : (b.val : ZMod p) - (col b i).2 =
      ((2 * (i.val % a) + 1 : Nat) : ZMod p) := by simp [color]
  have second : (((b.val + 1) % p : Nat) : ZMod p) - (col b i).2 =
      ((2 * (i.val % a) + 2 : Nat) : ZMod p) := by
    simp only [ZMod.natCast_mod, color, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [first, second]
  exact ⟨ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)⟩

private theorem row_no_carry (b : Fin p) (i : Fin (P - 1)) :
    (table a P ha hd).readNext R(col b i) b =
      if h : i.val + 2 < P then W(col b ⟨i.val + 1, by omega⟩)
      else H(((b.val * P : Nat) : ZMod (p * P))) := by
  have off := (matching_offsets a P ha hd b i).1
  have nonzero : 2 * (i.val % a) + 1 ≠ 0 := by omega
  have odd : (2 * (i.val % a) + 1) % 2 = 1 := by omega
  have idx : (col b i).1.val * a + (2 * (i.val % a) + 1 - 1) / 2 = i.val := by
    dsimp only [color]
    have half : (2 * (i.val % a) + 1 - 1) / 2 = i.val % a := by omega
    rw [half]
    simpa only [Nat.add_comm, Nat.mul_comm] using Nat.mod_add_div i.val a
  simp only [table, off, if_neg nonzero, if_pos odd, idx]

private theorem row_carry (b : Fin p) (i : Fin (P - 1)) :
    (table a P ha hd).readNext R(col b i)
      ⟨(b.val + 1) % p, Nat.mod_lt _ (by omega)⟩ =
      H(((b.val * P + (P - (i.val + 1)) : Nat) : ZMod (p * P))) := by
  have off := (matching_offsets a P ha hd b i).2
  have nonzero : 2 * (i.val % a) + 2 ≠ 0 := by omega
  have even : (2 * (i.val % a) + 2) % 2 ≠ 1 := by omega
  have idx : (col b i).1.val * a + (2 * (i.val % a) + 2 - 1) / 2 = i.val := by
    dsimp only [color]
    have half : (2 * (i.val % a) + 2 - 1) / 2 = i.val % a := by omega
    rw [half]
    simpa only [Nat.add_comm, Nat.mul_comm] using Nat.mod_add_div i.val a
  simp only [table, off, if_neg nonzero, if_neg even, idx]
  rw [carry_predecessor b]

section Execution

variable (hP : 0 < P)

local notation "hp" => (show 2 ≤ p by omega)
local notation "C" => table a P ha hd

/-- The same fixed row realizes every original input at its first carry or
its final no-carry scan, including across distinct occurrences of its color. -/
private theorem row_step (x : ZMod (p * P)) (i : Fin (P - 1))
    (hi : i.val < waits x) :
    (C).readNext R(col (digit hp hP x) i)
      (digit hp hP (x + ((i.val + 1 : Nat) : ZMod (p * P)))) =
      if h : i.val + 1 < waits x then
        W(col (digit hp hP x) ⟨i.val + 1, by have := (waits_bounds hP x).1; omega⟩)
      else H(x) := by
  let : NeZero (p * P) := ⟨by positivity⟩
  let b := digit hp hP x
  have decomposition := Nat.mod_add_div x.val P
  have label : ((b.val * P + x.val % P : Nat) : ZMod (p * P)) = x := by
    rw [show b.val * P + x.val % P = x.val by
      change x.val / P * P + x.val % P = x.val
      simpa only [Nat.add_comm, Nat.mul_comm] using decomposition, ZMod.natCast_zmod_val]
  by_cases more : i.val + 1 < waits x
  · rw [before_digit hp hP x (i.val + 1) more, row_no_carry a P ha hd]
    rw [dif_pos more, dif_pos (by have := (waits_bounds hP x).1; omega)]
  · rw [dif_neg more]
    have last : i.val + 1 = waits x := by omega
    by_cases zero : x.val % P = 0
    · have d := zero_digit hp hP x zero
      rw [last, d, row_no_carry a P ha hd]
      rw [dif_neg (by simp only [waits, if_pos zero] at last; omega)]
      exact congrArg (fun z : ZMod (p * P) => H(z))
        (by simpa only [zero, Nat.add_zero] using label)
    · have d := final_digit hp hP x zero
      have deq : digit hp hP (x + (waits x : ZMod (p * P))) =
          ⟨(b.val + 1) % p, Nat.mod_lt _ (by omega)⟩ := Fin.ext d
      rw [last, deq, row_carry a P ha hd]
      have rest : P - (i.val + 1) = x.val % P := by
        have bound := Nat.mod_lt x.val hP
        simp only [waits, if_neg zero] at last
        omega
      rw [rest]
      exact congrArg (fun z : ZMod (p * P) => H(z)) label

/-- A mathematical trajectory, not an input accessible to the stationary table. -/
private def trace (x : ZMod (p * P)) (n : Nat) : ZMod (p * P) × Q :=
  if live : n ≤ 2 * waits x then
    if zero : n = 0 then (x, Root)
    else if even : n % 2 = 0 then
      (x + (n / 2 : Nat), R(col (digit hp hP x)
        ⟨n / 2 - 1, by have := (waits_bounds hP x).1; omega⟩))
    else
      (x + (n / 2 : Nat), W(col (digit hp hP x)
        ⟨n / 2, by have := (waits_bounds hP x).1; omega⟩))
  else (x + (waits x : Nat), H(x))

private theorem trace_read (x : ZMod (p * P)) (t : Nat)
    (ht : 0 < t) (hl : t ≤ waits x) :
    trace a P ha hd hP x (2 * t) =
      (x + (t : Nat), R(col (digit hp hP x)
        ⟨t - 1, by have := (waits_bounds hP x).1; omega⟩)) := by
  simp [trace, show 2 * t ≤ 2 * waits x by omega, show 2 * t ≠ 0 by omega]

private theorem trace_wait (x : ZMod (p * P)) (t : Nat) (ht : t < waits x) :
    trace a P ha hd hP x (2 * t + 1) =
      (x + (t : Nat), W(col (digit hp hP x)
        ⟨t, by have := (waits_bounds hP x).1; omega⟩)) := by
  simp [trace, show 2 * t + 1 ≤ 2 * waits x by omega,
    show (2 * t + 1) / 2 = t by omega]

private theorem trace_halt (x : ZMod (p * P)) (n : Nat) (hn : 2 * waits x < n) :
    trace a P ha hd hP x n = (x + (waits x : Nat), H(x)) := by
  simp only [trace, dif_neg (Nat.not_le.mpr hn)]

private theorem trace_step (x : ZMod (p * P)) :
    Function.Semiconj (trace a P ha hd hP x) Nat.succ ((C).step hp hP) := by
  intro n
  change trace a P ha hd hP x (n + 1) = (C).step hp hP (trace a P ha hd hP x n)
  by_cases stopped : 2 * waits x < n
  · rw [trace_halt a P ha hd hP x (n + 1) (by omega),
      trace_halt a P ha hd hP x n stopped]
    rfl
  · have live : n ≤ 2 * waits x := by omega
    by_cases zero : n = 0
    · subst n
      have start : trace a P ha hd hP x 0 = (x, Root) := by simp [trace]
      rw [start]
      by_cases positive : 0 < waits x
      · rw [trace_wait a P ha hd hP x 0 positive]
        have wide : 1 < P := by have := (waits_bounds hP x).1; omega
        simp [Controller.step, table, wide]
      · have wzero : waits x = 0 := by omega
        rw [trace_halt a P ha hd hP x 1 (by omega), wzero]
        have one : P = 1 := by
          by_contra bad
          exact positive ((waits_bounds hP x).2 (by omega))
        let : NeZero (p * P) := ⟨by positivity⟩
        have label : (((digit hp hP x).val : Nat) : ZMod (p * P)) = x := by
          rw [show (digit hp hP x).val = x.val by simp [digit, one],
            ZMod.natCast_zmod_val]
        simp [Controller.step, table, one, label]
    · by_cases even : n % 2 = 0
      · have tn : n = 2 * (n / 2) := by omega
        have nt : 0 < n / 2 := by omega
        have tr := trace_read a P ha hd hP x (n / 2) nt (by omega)
        rw [← tn] at tr
        rw [tr]
        have time : n + 1 = 2 * (n / 2) + 1 := by omega
        rw [time]
        have row := row_step a P ha hd hP x
          ⟨n / 2 - 1, by have := (waits_bounds hP x).1; omega⟩
          (by change n / 2 - 1 < waits x; omega)
        have pred : n / 2 - 1 + 1 = n / 2 := by omega
        simp only [pred] at row
        by_cases more : n / 2 < waits x
        · rw [trace_wait a P ha hd hP x (n / 2) more, dif_pos more] at *
          simpa only [Controller.step, table] using congrArg (fun q =>
            (x + (n / 2 : Nat), q)) row.symm
        · have last : n / 2 = waits x := by omega
          rw [trace_halt a P ha hd hP x (2 * (n / 2) + 1) (by omega),
            dif_neg more] at *
          simpa only [Controller.step, table, last] using congrArg (fun q =>
            (x + (n / 2 : Nat), q)) row.symm
      · have tn : n = 2 * (n / 2) + 1 := by omega
        have before : n / 2 < waits x := by omega
        have target : n + 1 = 2 * (n / 2 + 1) := by omega
        have tw := (congrArg (trace a P ha hd hP x) tn).trans
          (trace_wait a P ha hd hP x (n / 2) before)
        rw [target, trace_read a P ha hd hP x (n / 2 + 1) (by omega) (by omega), tw]
        simp [Controller.step, table, Nat.cast_add, add_assoc]

private theorem run_trace (x : ZMod (p * P)) (n : Nat) :
    (C).run hp hP x n = trace a P ha hd hP x n := by
  have recurrence := (trace_step a P ha hd hP x).iterate_right n
  have initial : trace a P ha hd hP x 0 = (x, Root) := by simp [trace]
  have count : Nat.succ^[n] 0 = n := by simpa using Nat.succ_iterate 0 n
  simpa only [Controller.run, count, initial, table] using (recurrence 0).symm

private theorem action_at (x : ZMod (p * P)) (n : Nat) (hn : n ≤ 2 * waits x) :
    (C).action ((C).run hp hP x n).2 = if n % 2 = 0 then .read else .wait := by
  rw [run_trace a P ha hd hP x n]
  simp only [trace, dif_pos hn]
  by_cases zero : n = 0
  · subst n
    rfl
  · simp only [dif_neg zero]
    by_cases even : n % 2 = 0
    · simp only [dif_pos even, if_pos even]
      rfl
    · simp only [dif_neg even, if_neg even]
      rfl

private def correct : (C).Correct hp hP where
  length := fun x => 2 * waits x + 1
  first_read := rfl
  halt := by
    intro x
    rw [run_trace a P ha hd hP x _, trace_halt a P ha hd hP x _ (by omega)]
    rfl
  output := by
    intro x
    rw [run_trace a P ha hd hP x _, trace_halt a P ha hd hP x _ (by omega)]
    rfl
  live := by
    intro x n hn
    rw [action_at a P ha hd hP x n (by omega)]
    split <;> intro h <;> cases h
  after_read := by
    intro x n hn hr
    rw [action_at a P ha hd hP x n (by omega)] at hr
    have even : n % 2 = 0 := by
      split at hr
      · assumption
      · cases hr
    rw [action_at a P ha hd hP x (n + 1) (by omega),
      if_neg (show (n + 1) % 2 ≠ 0 by omega)]
  last_read := by
    intro x
    rw [show 2 * waits x + 1 - 1 = 2 * waits x by omega,
      action_at a P ha hd hP x _ le_rfl,
      if_pos (show (2 * waits x) % 2 = 0 by omega)]

private theorem event_counts (x : ZMod (p * P)) :
    eventCount hp hP C (correct a P ha hd hP) x .read = waits x + 1 ∧
    eventCount hp hP C (correct a P ha hd hP) x .wait = waits x := by
  classical
  have read_iff (n : Nat) (hn : n < 2 * waits x + 1) :
      (C).action ((C).run hp hP x n).2 = .read ↔ n % 2 = 0 := by
    rw [action_at a P ha hd hP x n (by omega)]
    split <;> simp_all
  have wait_iff (n : Nat) (hn : n < 2 * waits x + 1) :
      (C).action ((C).run hp hP x n).2 = .wait ↔ n % 2 = 1 := by
    rw [action_at a P ha hd hP x n (by omega)]
    split <;> simp_all
  constructor
  · change ((Finset.range (2 * waits x + 1)).filter _).card = waits x + 1
    conv_rhs => rw [← Finset.card_range (waits x + 1)]
    apply Finset.card_bij (fun n _ => n / 2)
    · intro n hn
      obtain ⟨range, act⟩ := Finset.mem_filter.mp hn
      have bound := Finset.mem_range.mp range
      simp only [Finset.mem_range]
      omega
    · intro n hn m hm he
      obtain ⟨rn, an⟩ := Finset.mem_filter.mp hn
      obtain ⟨rm, am⟩ := Finset.mem_filter.mp hm
      have pn := (read_iff n (Finset.mem_range.mp rn)).mp an
      have pm := (read_iff m (Finset.mem_range.mp rm)).mp am
      omega
    · intro n hn
      have bound := Finset.mem_range.mp hn
      refine ⟨2 * n, ?_, by omega⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
      exact (read_iff (2 * n) (by omega)).mpr (by omega)
  · change ((Finset.range (2 * waits x + 1)).filter _).card = waits x
    conv_rhs => rw [← Finset.card_range (waits x)]
    apply Finset.card_bij (fun n _ => n / 2)
    · intro n hn
      obtain ⟨range, act⟩ := Finset.mem_filter.mp hn
      have bound := Finset.mem_range.mp range
      have parity := (wait_iff n bound).mp act
      simp only [Finset.mem_range]
      omega
    · intro n hn m hm he
      obtain ⟨rn, an⟩ := Finset.mem_filter.mp hn
      obtain ⟨rm, am⟩ := Finset.mem_filter.mp hm
      have pn := (wait_iff n (Finset.mem_range.mp rn)).mp an
      have pm := (wait_iff m (Finset.mem_range.mp rm)).mp am
      omega
    · intro n hn
      have bound := Finset.mem_range.mp hn
      refine ⟨2 * n + 1, ?_, by omega⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
      exact (wait_iff (2 * n + 1) (by omega)).mpr (by omega)

include ha hd hP in
private theorem state_card :
    Nat.card Q = p * P + 1 + 4 * p * (P - 1) / (p - 1) := by
  let : NeZero (p * P) := ⟨by positivity⟩
  let : NeZero p := ⟨by omega⟩
  let : Fintype Q := by unfold State; infer_instance
  have nominal : Nat.card Q = 1 + (((P - 1) / a) * p) * 2 + p * P := by
    simp [State, Nat.card_eq_fintype_card, Fintype.card_prod, ZMod.card, Nat.add_assoc]
  have numerator : 4 * p * (P - 1) = (2 * p * ((P - 1) / a)) * (2 * a) := by
    calc
      4 * p * (P - 1) = 4 * p * (((P - 1) / a) * a) :=
        congrArg (fun n => 4 * p * n) (Nat.div_mul_cancel hd).symm
      _ = _ := by ring
  rw [nominal, show p - 1 = 2 * a by omega, numerator,
    Nat.mul_div_cancel _ (show 0 < 2 * a by omega)]
  ring

/-- For every odd base p=2a+1 and every positive width with a dividing P-1,
one fixed total table decodes all original sources and attains the exact
nominal capacity and simultaneous worst read and wait counts. -/
theorem result :
    ∃ I : (C).Correct hp hP,
      Nat.card Q = p * P + 1 + 4 * p * (P - 1) / (p - 1) ∧
      (∀ x, eventCount hp hP C I x .read ≤ P ∧
        eventCount hp hP C I x .wait ≤ P - 1) ∧
      (∃ x, eventCount hp hP C I x .read = P ∧
        eventCount hp hP C I x .wait = P - 1) ∧
      (P = 1 → Nat.card Q = p + 1) := by
  refine ⟨correct a P ha hd hP, state_card a P ha hd hP, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨reads, waiting⟩ := event_counts a P ha hd hP x
    rw [reads, waiting]
    have bound := (waits_bounds hP x).1
    omega
  · obtain ⟨reads, waiting⟩ := event_counts a P ha hd hP (0 : ZMod (p * P))
    have zero : waits (0 : ZMod (p * P)) = P - 1 := by simp [waits]
    exact ⟨0, reads.trans (by rw [zero]; omega), waiting.trans zero⟩
  · intro one
    rw [state_card a P ha hd hP, one]
    simp

end Execution

end D5.S3.ObserverMemory.Algorithms.SharedCarryOddController
