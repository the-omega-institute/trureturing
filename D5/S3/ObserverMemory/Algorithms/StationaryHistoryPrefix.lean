/- GID: D5/S3/ObserverMemory/Algorithms/StationaryHistoryPrefix
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/StationaryHistoryPrefix
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual original controller histories and their prefix laws. -/

import D5.S3.ObserverMemory.Algorithms.StationaryUnitControl
import D5.S3.ObserverMemory.Algorithms.FixedForestTargetInventory
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.TakeDrop

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.StationaryReadHistory

open StationaryUnitControl
open scoped BigOperators
attribute [local instance] Classical.propDecidable

universe u
variable {P ell h : Nat} {Q : Type u} (C : Controller P Q) (hP : 1 < P)
    (I : Initialized C hP ell h)

/-- The full physical action alphabet, including the actual absolute read answer. -/
inductive Action (P : Nat) where
  | wait : Action P
  | read : Fin 3 → Action P
  | halt : ZMod (3 * P) → Action P
  deriving DecidableEq

def action (x : ZMod (3 * P)) (t : Nat) : Action P :=
  match C.instruction (C.run hP (x, C.initial) t).2 with
  | .wait _ => .wait
  | .read _ => .read (digit hP (C.run hP (x, C.initial) t).1)
  | .halt z => .halt z

/-- All actions and all answers before time t, with literal unit waits retained. -/
def trace (x : ZMod (3 * P)) : Nat → List (Action P)
  | 0 => []
  | t + 1 => trace x t ++ [action C hP x t]

def Action.isRead : Action P → Bool
  | .read _ => true
  | _ => false

def Action.isWait : Action P → Bool
  | .wait => true
  | _ => false

def replay (q : Q) (w : List (Action P)) : Q :=
  w.foldl (fun q a => match C.instruction q, a with
      | .wait next, .wait => next
      | .read row, .read c => row c
      | _, _ => q) q

def shift (w : List (Action P)) : Nat := (w.filter Action.isWait).length

def readNumber (w : List (Action P)) : Nat := (w.filter Action.isRead).length

private theorem replay_append (q : Q) (a b : List (Action P)) :
    replay C q (a ++ b) = replay C (replay C q a) b := by
  simpa only [replay] using
    (List.foldl_append (f := fun q a => match C.instruction q, a with
      | .wait next, .wait => next
      | .read row, .read c => row c
      | _, _ => q) (b := q) (l := a) (l' := b))

private theorem trace_length (x : ZMod (3 * P)) (t : Nat) :
    (trace C hP x t).length = t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [trace, ih]

private theorem shift_append (a b : List (Action P)) : shift (a ++ b) = shift a + shift b := by
  simp [shift, List.filter_append]

/-- Replaying the recorded prefix reconstructs the actual control and phase.
Only wait actions contribute to the physical translation. -/
theorem trace_reconstruction (x : ZMod (3 * P)) (t : Nat) :
    C.run hP (x, C.initial) t =
      (x + (shift (trace C hP x t) : ZMod (3 * P)),
        replay C C.initial (trace C hP x t)) := by
  induction t with
  | zero => simp [Controller.run, trace, shift, replay]
  | succ t ih =>
    have advance : C.run hP (x, C.initial) (t + 1) =
        C.next hP (C.run hP (x, C.initial) t) :=
      Function.iterate_succ_apply' _ _ _
    have qeq : (C.run hP (x, C.initial) t).2 =
        replay C C.initial (trace C hP x t) := congrArg Prod.snd ih
    simp only [replay] at qeq
    have seq : (C.run hP (x, C.initial) t).1 =
        x + (shift (trace C hP x t) : ZMod (3 * P)) := congrArg Prod.fst ih
    rw [advance, trace, shift_append, replay_append]
    cases ins : C.instruction (C.run hP (x, C.initial) t).2 with
    | wait next =>
      simp only [action, shift, List.filter, Action.isWait,
        List.length_cons, List.length_nil, Nat.cast_add, Nat.cast_one, zero_add,
        replay, List.foldl_cons, List.foldl_nil, ← qeq,
        Controller.next, Controller.step, ins, Option.getD_some,
        seq, add_assoc]
    | read row =>
      simp only [action, shift, List.filter, Action.isWait,
        List.length_nil, add_zero,
        replay, List.foldl_cons, List.foldl_nil, ← qeq,
        Controller.next, Controller.step, ins, Option.getD_some, seq]
    | halt z =>
      simp only [action, shift, List.filter, Action.isWait,
        List.length_nil, add_zero,
        replay, List.foldl_cons, List.foldl_nil, ← qeq,
        Controller.next, Controller.step, ins, Option.getD_none]
      exact ih.trans (by simp only [replay, ← qeq, shift])

noncomputable def readTimes (x : ZMod (3 * P)) : Finset Nat :=
  (Finset.range (I.length x)).filter (fun t => IsRead C (C.run hP (x, C.initial) t).2)

noncomputable abbrev reads (x : ZMod (3 * P)) : Nat := (readTimes C hP I x).card

private theorem read_time_mem (x : ZMod (3 * P)) (i : Fin (reads C hP I x)) :
    (readTimes C hP I x).orderEmbOfFin rfl i ∈ readTimes C hP I x :=
  Finset.orderEmbOfFin_mem _ rfl i

noncomputable def readTime (x : ZMod (3 * P)) (i : Fin (reads C hP I x)) : Nat :=
  (readTimes C hP I x).orderEmbOfFin rfl i

/-- Events retain the original input and its read index. -/
abbrev Event := Σ x : ZMod (3 * P), Fin (reads C hP I x)

noncomputable def eventWord (e : Event C hP I) : List (Action P) :=
  trace C hP e.1 (readTime C hP I e.1 e.2 + 1)

noncomputable def historyWords [NeZero (3 * P)] : Finset (List (Action P)) :=
  Finset.univ.image (eventWord C hP I)

/-- A history is an actual full prefix, never a row or a weight. -/
abbrev History [NeZero (3 * P)] := {w : List (Action P) // w ∈ historyWords C hP I}

noncomputable abbrev event [NeZero (3 * P)] (e : Event C hP I) : History C hP I :=
  ⟨eventWord C hP I e, Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩⟩

private theorem event_time_bound (e : Event C hP I) :
    readTime C hP I e.1 e.2 < I.length e.1 :=
  Finset.mem_range.mp (Finset.mem_filter.mp (read_time_mem C hP I e.1 e.2)).1

private theorem event_is_read (e : Event C hP I) :
    IsRead C (C.run hP (e.1, C.initial) (readTime C hP I e.1 e.2)).2 :=
  (Finset.mem_filter.mp (read_time_mem C hP I e.1 e.2)).2

/-- The event image is exhaustive; drawing a prefix again adds no node. -/
theorem event_surjective [NeZero (3 * P)] : Function.Surjective (event C hP I) := by
  intro n
  obtain ⟨e, _, he⟩ := Finset.mem_image.mp n.property
  exact ⟨e, Subtype.ext he⟩

/-- A fixed input has distinct histories at distinct read indices. -/
theorem event_input_injective [NeZero (3 * P)] (x : ZMod (3 * P)) :
    Function.Injective (fun i : Fin (reads C hP I x) => event C hP I ⟨x, i⟩) := by
  intro i j he
  have hw := congrArg (fun n : History C hP I => n.val.length) he
  simp only [eventWord, trace_length] at hw
  have ht : readTime C hP I x i = readTime C hP I x j := by omega
  exact (readTimes C hP I x).orderEmbOfFin rfl |>.injective ht


private theorem trace_eq_map (x : ZMod (3 * P)) (t : Nat) :
    trace C hP x t = (List.range t).map (action C hP x) := by
  induction t with
  | zero => rfl
  | succ t ih => simp [trace, List.range_succ, ih]

private theorem trace_take (x : ZMod (3 * P)) {t v : Nat} (ht : t ≤ v) :
    (trace C hP x v).take t = trace C hP x t := by
  simp [trace_eq_map, ← List.map_take, List.take_range, Nat.min_eq_left ht]

private theorem trace_get (x : ZMod (3 * P)) {t v : Nat} (ht : t < v) :
    (trace C hP x v)[t]'(by rw [trace_length]; exact ht) = action C hP x t := by
  simp [trace_eq_map]

private theorem action_read_iff (x : ZMod (3 * P)) (t : Nat) :
    (action C hP x t).isRead = true ↔ IsRead C (C.run hP (x, C.initial) t).2 := by
  cases ins : C.instruction (C.run hP (x, C.initial) t).2 <;>
    simp [action, Action.isRead, IsRead, ins]

private theorem count_reads_trace (x : ZMod (3 * P)) (t : Nat) :
    readNumber (trace C hP x t) =
      ((Finset.range t).filter (fun v => IsRead C (C.run hP (x, C.initial) v).2)).card := by
  induction t with
  | zero => simp [trace, readNumber]
  | succ t ih =>
    simp only [readNumber] at ih
    by_cases hr : IsRead C (C.run hP (x, C.initial) t).2
    · have ha := (action_read_iff C hP x t).2 hr
      simp [trace, readNumber, List.filter_append, List.filter, ha,
        Finset.range_add_one, Finset.filter_insert, hr, ih, readNumber]
    · have ha : (action C hP x t).isRead = false := by
        cases he : (action C hP x t).isRead
        · rfl
        · exact False.elim (hr ((action_read_iff C hP x t).1 he))
      simp [trace, readNumber, List.filter_append, List.filter, ha,
        Finset.range_add_one, Finset.filter_insert, hr, ih, readNumber]

private theorem reads_pos (x : ZMod (3 * P)) : 0 < reads C hP I x := by
  apply Finset.card_pos.mpr
  exact ⟨ell, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (I.shape x).first_before_stop,
    (I.shape x).first_read⟩⟩

private theorem reads_bound (x : ZMod (3 * P)) : reads C hP I x ≤ h :=
  (I.shape x).read_bound

private theorem first_read_time (x : ZMod (3 * P)) :
    readTime C hP I x ⟨0, reads_pos C hP I x⟩ = ell := by
  rw [readTime, Finset.orderEmbOfFin_zero rfl (reads_pos C hP I x)]
  apply le_antisymm
  · apply Finset.min'_le
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (I.shape x).first_before_stop,
      (I.shape x).first_read⟩
  · apply Finset.le_min'
    intro t ht
    have hr := (Finset.mem_filter.mp ht).2
    by_contra hh
    obtain ⟨q, hw⟩ := (I.shape x).prefix_wait t (by omega)
    obtain ⟨row, hi⟩ := hr
    rw [hw] at hi
    cases hi

private theorem last_read_time (x : ZMod (3 * P)) :
    readTime C hP I x ⟨reads C hP I x - 1, by have := reads_pos C hP I x; omega⟩ =
      I.length x - 1 := by
  rw [readTime, Finset.orderEmbOfFin_last rfl (reads_pos C hP I x)]
  apply le_antisymm
  · apply Finset.max'_le
    intro t ht
    have := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
    omega
  · apply Finset.le_max'
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
      have := (I.shape x).first_before_stop; omega), (I.shape x).last_read⟩

/-- Each prefix can reconstruct its pre-read configuration and current answer. -/
theorem event_reconstruction (e : Event C hP I) :
    C.run hP (e.1, C.initial) (readTime C hP I e.1 e.2) =
      (e.1 + (shift ((eventWord C hP I e).dropLast) : ZMod (3 * P)),
        replay C C.initial ((eventWord C hP I e).dropLast)) ∧
    eventWord C hP I e = (eventWord C hP I e).dropLast ++ 
      [.read (digit hP (C.run hP (e.1, C.initial) (readTime C hP I e.1 e.2)).1)] := by
  have hr := event_is_read C hP I e
  obtain ⟨row, hi⟩ := hr
  have drop : (eventWord C hP I e).dropLast = trace C hP e.1 (readTime C hP I e.1 e.2) := by
    simp [eventWord, trace]
  refine ⟨?_, ?_⟩
  · rw [drop]; exact trace_reconstruction C hP _ _
  · rw [drop]
    simp [eventWord, trace, action, hi]


private theorem read_rank (x : ZMod (3 * P)) (i : Fin (reads C hP I x)) :
    readNumber (eventWord C hP I ⟨x, i⟩) = i.val + 1 := by
  change readNumber (trace C hP x (readTime C hP I x i + 1)) = i.val + 1
  rw [count_reads_trace]
  let s := (Finset.univ : Finset (Fin (reads C hP I x))).filter (fun j => j.val < i.val + 1)
  have hc : s.card = i.val + 1 := by
    simpa [s, Nat.min_eq_right (by omega : i.val + 1 ≤ reads C hP I x)] using
      (Fin.card_filter_val_lt (n := reads C hP I x) (m := i.val + 1))
  rw [← hc]
  symm
  apply Finset.card_bij (fun j _ => readTime C hP I x j)
  · intro j hj
    have hj' : j ≤ i := by
      have := (Finset.mem_filter.mp hj).2
      exact Fin.le_iff_val_le_val.mpr (by omega)
    have hm := read_time_mem C hP I x j
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, (Finset.mem_filter.mp hm).2⟩
    have := (readTimes C hP I x).orderEmbOfFin rfl |>.monotone hj'
    change readTime C hP I x j ≤ readTime C hP I x i at this
    omega
  · intro a ha b hb he
    exact (readTimes C hP I x).orderEmbOfFin rfl |>.injective he
  · intro t ht
    have htime := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
    have hm : t ∈ readTimes C hP I x := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, (Finset.mem_filter.mp ht).2⟩
      have hb : readTime C hP I x i < I.length x := event_time_bound C hP I ⟨x,i⟩; omega
    let j := ((readTimes C hP I x).orderIsoOfFin rfl).symm ⟨t,hm⟩
    have he : readTime C hP I x j = t := by
      exact congrArg Subtype.val ((readTimes C hP I x).orderIsoOfFin rfl |>.apply_symm_apply ⟨t,hm⟩)
    refine ⟨j, ?_, he⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hj : j ≤ i := by
      apply (readTimes C hP I x).orderEmbOfFin rfl |>.le_iff_le.mp
      change readTime C hP I x j ≤ readTime C hP I x i
      rw [he]; omega
    have := Fin.le_iff_val_le_val.mp hj; omega

def level [NeZero (3 * P)] (n : History C hP I) : Nat := readNumber n.val - 1

def time [NeZero (3 * P)] (n : History C hP I) : Nat := n.val.length - 1

def historyShift [NeZero (3 * P)] (n : History C hP I) : Nat := shift n.val

def readControl [NeZero (3 * P)] (n : History C hP I) : Q :=
  replay C C.initial n.val.dropLast

noncomputable def support [NeZero (3 * P)] (n : History C hP I) : Finset (ZMod (3 * P)) :=
  Finset.univ.filter (fun x => ∃ i : Fin (reads C hP I x), event C hP I ⟨x,i⟩ = n)

private theorem event_level [NeZero (3 * P)] (e : Event C hP I) :
    level C hP I (event C hP I e) = e.2.val := by
  simpa [level, event] using congrArg (fun n : Nat => n - 1) (read_rank C hP I e.1 e.2)

private theorem event_time [NeZero (3 * P)] (e : Event C hP I) :
    time C hP I (event C hP I e) = readTime C hP I e.1 e.2 := by
  simp [time, eventWord, trace_length]

private theorem event_shift [NeZero (3 * P)] (e : Event C hP I) :
    historyShift C hP I (event C hP I e) = shift ((eventWord C hP I e).dropLast) := by
  obtain ⟨_, hw⟩ := event_reconstruction C hP I e
  simp only [historyShift]
  rw [hw, shift_append]
  simp [shift, List.filter, Action.isWait]

private theorem support_nonempty [NeZero (3 * P)] (n : History C hP I) :
    (support C hP I n).Nonempty := by
  obtain ⟨e, he⟩ := event_surjective C hP I n
  refine ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.2, he⟩⟩

/-- The configuration of each supporting original input is reconstructed exactly. -/
theorem history_configuration [NeZero (3 * P)] (n : History C hP I)
    (x : ZMod (3 * P)) (hx : x ∈ support C hP I n) :
    C.run hP (x,C.initial) (time C hP I n) =
      (x + (historyShift C hP I n : ZMod (3 * P)), readControl C hP I n) := by
  obtain ⟨_, i, hi⟩ := Finset.mem_filter.mp hx
  subst n
  rw [event_time, event_shift]
  exact (event_reconstruction C hP I ⟨x,i⟩).1

/-- Incidences are pairs of a full history and one supporting original label.
The equivalence retains an event's read index in its inverse. -/
noncomputable def eventIncidenceEquiv [NeZero (3 * P)] :
    Event C hP I ≃ Σ n : History C hP I, {x : ZMod (3 * P) // x ∈ support C hP I n} :=
  Equiv.ofBijective (fun e => ⟨event C hP I e, ⟨e.1, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, e.2, rfl⟩⟩⟩) (by
    constructor
    · intro a b he
      have hn : event C hP I a = event C hP I b := congrArg Sigma.fst he
      have hx : a.1 = b.1 := congrArg (fun z => z.2.val) he
      rcases a with ⟨x,i⟩; rcases b with ⟨y,j⟩
      dsimp at hx; subst y
      have hi := event_input_injective C hP I x hn
      subst j; rfl
    · rintro ⟨n,x,hx⟩
      obtain ⟨_,i,hi⟩ := Finset.mem_filter.mp hx
      refine ⟨⟨x,i⟩, ?_⟩
      subst n; rfl)


/-- Read positions strictly before the last action of a complete read prefix. -/
def previousTimes (w : List (Action P)) : Finset Nat :=
  (Finset.range (w.length - 1)).filter (fun t => (w[t]?.getD .wait).isRead = true)

private theorem previous_times_event (e : Event C hP I) :
    previousTimes (eventWord C hP I e) =
      (Finset.range (readTime C hP I e.1 e.2)).filter
        (fun t => IsRead C (C.run hP (e.1,C.initial) t).2) := by
  ext t
  simp only [previousTimes, eventWord, trace_length, Nat.add_sub_cancel,
    Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨ht,ha⟩
    refine ⟨ht, ?_⟩
    have hget : (trace C hP e.1 (readTime C hP I e.1 e.2 + 1))[t]?.getD .wait =
        action C hP e.1 t := by
      rw [List.getElem?_eq_getElem (by rw [trace_length]; omega), Option.getD_some,
        trace_get C hP e.1 (by omega)]
    rw [hget] at ha
    exact (action_read_iff C hP _ _).1 ha
  · rintro ⟨ht,ha⟩
    refine ⟨ht, ?_⟩
    rw [List.getElem?_eq_getElem (by rw [trace_length]; omega), Option.getD_some,
      trace_get C hP e.1 (by omega)]
    exact (action_read_iff C hP _ _).2 ha

private theorem previous_prefix_actual [NeZero (3 * P)] (n : History C hP I)
    (hs : (previousTimes n.val).Nonempty) :
    n.val.take ((previousTimes n.val).max' hs + 1) ∈ historyWords C hP I := by
  obtain ⟨e, he⟩ := event_surjective C hP I n
  subst n
  let t := (previousTimes (eventWord C hP I e)).max' hs
  have hm : t ∈ previousTimes (eventWord C hP I e) := Finset.max'_mem _ _
  rw [previous_times_event] at hm
  have ht : t < readTime C hP I e.1 e.2 := Finset.mem_range.mp (Finset.mem_filter.mp hm).1
  have hr := (Finset.mem_filter.mp hm).2
  have hm' : t ∈ readTimes C hP I e.1 := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hr⟩
    have := event_time_bound C hP I e
    omega
  let i := ((readTimes C hP I e.1).orderIsoOfFin rfl).symm ⟨t,hm'⟩
  have hi : readTime C hP I e.1 i = t :=
    congrArg Subtype.val ((readTimes C hP I e.1).orderIsoOfFin rfl |>.apply_symm_apply ⟨t,hm'⟩)
  apply Finset.mem_image.mpr
  refine ⟨⟨e.1,i⟩, Finset.mem_univ _, ?_⟩
  change trace C hP e.1 (readTime C hP I e.1 i + 1) =
    (trace C hP e.1 (readTime C hP I e.1 e.2 + 1)).take (t + 1)
  rw [hi, trace_take C hP _ (by omega)]

/-- The unique parent is obtained by truncating to the preceding read.
This operation depends only on the full prefix, without selecting a row. -/
noncomputable def parent [NeZero (3 * P)] (n : History C hP I) : Option (History C hP I) :=
  if hs : (previousTimes n.val).Nonempty then
    some ⟨n.val.take ((previousTimes n.val).max' hs + 1), previous_prefix_actual C hP I n hs⟩
  else none

private theorem previous_time_last (x : ZMod (3 * P))
    (i : Nat) (hi : i + 1 < reads C hP I x) :
    ∃ hs : (previousTimes (eventWord C hP I ⟨x,⟨i + 1,hi⟩⟩)).Nonempty,
      (previousTimes (eventWord C hP I ⟨x,⟨i + 1,hi⟩⟩)).max' hs =
        readTime C hP I x ⟨i,by omega⟩ := by
  have hlt : readTime C hP I x ⟨i,by omega⟩ < readTime C hP I x ⟨i + 1,hi⟩ :=
    (readTimes C hP I x).orderEmbOfFin rfl |>.strictMono (by change i < i + 1; omega)
  have hm : readTime C hP I x ⟨i,by omega⟩ ∈
      previousTimes (eventWord C hP I ⟨x,⟨i + 1,hi⟩⟩) := by
    rw [previous_times_event]
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, event_is_read C hP I ⟨x,⟨i,by omega⟩⟩⟩
  refine ⟨⟨_,hm⟩, le_antisymm ?_ (Finset.le_max' _ _ hm)⟩
  apply Finset.max'_le
  intro t ht
  rw [previous_times_event] at ht
  have ht' : t < readTime C hP I x ⟨i + 1,hi⟩ := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
  have hm' : t ∈ readTimes C hP I x := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, (Finset.mem_filter.mp ht).2⟩
    have hb : readTime C hP I x ⟨i + 1,hi⟩ < I.length x := event_time_bound C hP I ⟨x,⟨i + 1,hi⟩⟩
    omega
  let j := ((readTimes C hP I x).orderIsoOfFin rfl).symm ⟨t,hm'⟩
  have hj : readTime C hP I x j = t :=
    congrArg Subtype.val ((readTimes C hP I x).orderIsoOfFin rfl |>.apply_symm_apply ⟨t,hm'⟩)
  have hjlt : j < (⟨i + 1,hi⟩ : Fin (reads C hP I x)) := by
    apply (readTimes C hP I x).orderEmbOfFin rfl |>.lt_iff_lt.mp
    change readTime C hP I x j < readTime C hP I x ⟨i + 1,hi⟩
    rw [hj]; exact ht'
  have hjle : j ≤ (⟨i,by omega⟩ : Fin (reads C hP I x)) := by
    have hjv : j.val < i + 1 := hjlt
    change j.val ≤ i
    omega
  have hmle := (readTimes C hP I x).orderEmbOfFin rfl |>.monotone hjle
  change readTime C hP I x j ≤ readTime C hP I x ⟨i,by omega⟩ at hmle
  rwa [hj] at hmle

/-- Consecutive actual read events have exactly the canonical prefix parent. -/
theorem parent_successor [NeZero (3 * P)] (x : ZMod (3 * P))
    (i : Nat) (hi : i + 1 < reads C hP I x) :
    parent C hP I (event C hP I ⟨x,⟨i + 1,hi⟩⟩) =
      some (event C hP I ⟨x,⟨i,by omega⟩⟩) := by
  obtain ⟨hs,ht⟩ := previous_time_last C hP I x i hi
  unfold parent
  split
  · apply congrArg Option.some
    apply Subtype.ext
    change (trace C hP x (readTime C hP I x ⟨i + 1,hi⟩ + 1)).take
      ((previousTimes (eventWord C hP I ⟨x,⟨i + 1,hi⟩⟩)).max' hs + 1) =
        trace C hP x (readTime C hP I x ⟨i,by omega⟩ + 1)
    rw [ht, trace_take C hP _ (by
      have hb := (readTimes C hP I x).orderEmbOfFin rfl |>.monotone
        (show (⟨i,by omega⟩ : Fin (reads C hP I x)) ≤ ⟨i + 1,hi⟩ from by change i ≤ i + 1; omega)
      change readTime C hP I x ⟨i,by omega⟩ ≤ readTime C hP I x ⟨i + 1,hi⟩ at hb
      omega)]
  · rename_i hn
    exact False.elim (hn hs)

include I in
private theorem trace_common (x : ZMod (3 * P)) {t : Nat} (ht : t ≤ ell) :
    trace C hP x t = List.replicate t .wait := by
  induction t with
  | zero => rfl
  | succ t ih =>
    obtain ⟨q,hi⟩ := (I.shape x).prefix_wait t (by omega)
    rw [trace, ih (by omega)]
    simp only [action,hi]
    change List.replicate t (.wait : Action P) ++ List.replicate 1 .wait =
      List.replicate (t + 1) .wait
    rw [List.replicate_add]

private theorem digit_block [NeZero (3 * P)] (c : Fin 3) :
    digit hP ((c.val * P : Nat) : ZMod (3 * P)) = c := by
  apply Fin.ext
  have hb : c.val * P < 3 * P := Nat.mul_lt_mul_of_pos_right c.isLt (by omega)
  change (((c.val * P : Nat) : ZMod (3 * P)).val / P) = c.val
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hb, Nat.mul_div_left _ (by omega : 0 < P)]

def rootInput (c : Fin 3) : ZMod (3 * P) :=
  ((c.val * P : Nat) : ZMod (3 * P)) - (ell : ZMod (3 * P))

def rootWord (c : Fin 3) : List (Action P) := List.replicate ell .wait ++ [.read c]

private theorem first_event_word (x : ZMod (3 * P)) :
    eventWord C hP I ⟨x,⟨0,reads_pos C hP I x⟩⟩ =
      rootWord (ell := ell) (digit hP (x + (ell : ZMod (3 * P)))) := by
  change trace C hP x (readTime C hP I x ⟨0,reads_pos C hP I x⟩ + 1) = _
  rw [first_read_time, trace, trace_common C hP I x (le_refl ell)]
  obtain ⟨row,hi⟩ := (I.shape x).first_read
  have hs := congrArg Prod.fst (initialized_prefix C hP I x (le_refl ell))
  simp [rootWord, action, hi, hs]

private theorem root_word_actual [NeZero (3 * P)] (c : Fin 3) :
    rootWord (ell := ell) c ∈ historyWords C hP I := by
  apply Finset.mem_image.mpr
  refine ⟨⟨rootInput (P := P) (ell := ell) c, ⟨0,reads_pos C hP I _⟩⟩,
    Finset.mem_univ _, ?_⟩
  rw [first_event_word]
  simp only [rootInput, sub_add_cancel]
  rw [digit_block]

noncomputable def root [NeZero (3 * P)] (c : Fin 3) : History C hP I :=
  ⟨rootWord (ell := ell) c,root_word_actual C hP I c⟩

private theorem first_event [NeZero (3 * P)] (x : ZMod (3 * P)) :
    event C hP I ⟨x,⟨0,reads_pos C hP I x⟩⟩ =
      root C hP I (digit hP (x + (ell : ZMod (3 * P)))) :=
  Subtype.ext (first_event_word C hP I x)

private theorem first_parent [NeZero (3 * P)] (x : ZMod (3 * P)) :
    parent C hP I (event C hP I ⟨x,⟨0,reads_pos C hP I x⟩⟩) = none := by
  have he : previousTimes (eventWord C hP I ⟨x,⟨0,reads_pos C hP I x⟩⟩) = ∅ := by
    rw [previous_times_event]
    dsimp only
    rw [first_read_time]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    have hlt := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
    obtain ⟨q,hw⟩ := (I.shape x).prefix_wait t hlt
    obtain ⟨row,hr⟩ := (Finset.mem_filter.mp ht).2
    rw [hw] at hr; cases hr
  unfold parent
  split
  · rename_i hs
    change (previousTimes (eventWord C hP I ⟨x,⟨0,reads_pos C hP I x⟩⟩)).Nonempty at hs
    rw [he] at hs
    exact False.elim (Finset.not_nonempty_empty hs)
  · rfl

/-- Precisely the three first-answer prefixes have no parent. -/
theorem roots_exact [NeZero (3 * P)] (n : History C hP I) :
    parent C hP I n = none ↔ ∃ c, n = root C hP I c := by
  constructor
  · intro hp
    obtain ⟨⟨x,i⟩,he⟩ := event_surjective C hP I n
    subst n
    by_cases hz : i.val = 0
    · have hi : i = ⟨0,reads_pos C hP I x⟩ := Fin.ext hz
      subst i
      exact ⟨_,first_event C hP I x⟩
    · have hi : i.val - 1 + 1 < reads C hP I x := by have := i.isLt; omega
      have he : i = ⟨i.val - 1 + 1,hi⟩ := Fin.ext (by change i.val = i.val - 1 + 1; omega)
      rw [he, parent_successor] at hp
      cases hp
  · rintro ⟨c,rfl⟩
    have hf := first_parent C hP I (rootInput (P := P) (ell := ell) c)
    rw [first_event] at hf
    simp only [rootInput, sub_add_cancel] at hf
    rwa [digit_block] at hf


def color [NeZero (3 * P)] (n : History C hP I) : Fin 3 :=
  match n.val.getLast? with
  | some (.read c) => c
  | _ => 0

private theorem event_color [NeZero (3 * P)] (e : Event C hP I) :
    color C hP I (event C hP I e) =
      digit hP (C.run hP (e.1,C.initial) (readTime C hP I e.1 e.2)).1 := by
  obtain ⟨_,hw⟩ := event_reconstruction C hP I e
  simp only [color]
  rw [hw]
  simp

private theorem trace_counts (x : ZMod (3 * P)) (t : Nat) (ht : t ≤ I.length x) :
    t = shift (trace C hP x t) + readNumber (trace C hP x t) := by
  induction t with
  | zero => simp [trace,shift,readNumber]
  | succ t ih =>
    have ih' := ih (by omega)
    cases ins : C.instruction (C.run hP (x,C.initial) t).2 with
    | wait q =>
      simp only [trace,shift,readNumber,List.filter_append,List.length_append,
        List.filter,action,ins,
        Action.isWait,Action.isRead,List.length_cons,List.length_nil,Nat.add_zero]
      simp only [shift,readNumber] at ih'
      omega
    | read row =>
      simp only [trace,shift,readNumber,List.filter_append,List.length_append,
        List.filter,action,ins,
        Action.isWait,Action.isRead,List.length_cons,List.length_nil,Nat.add_zero]
      simp only [shift,readNumber] at ih'
      omega
    | halt z => exact False.elim ((I.finite x).live t (by omega) z ins)

/-- Time, read level and physical shift retain the literal action accounting. -/
theorem history_time_decomposition [NeZero (3 * P)] (n : History C hP I) :
    time C hP I n = historyShift C hP I n + level C hP I n := by
  obtain ⟨e,he⟩ := event_surjective C hP I n
  subst n
  have ht : readTime C hP I e.1 e.2 + 1 ≤ I.length e.1 := by
    have := event_time_bound C hP I e; omega
  have hc := trace_counts C hP I e.1 _ ht
  have hr := read_rank C hP I e.1 e.2
  change readTime C hP I e.1 e.2 + 1 =
    historyShift C hP I (event C hP I e) + readNumber (eventWord C hP I e) at hc
  rw [hr] at hc
  rw [event_time,event_level]
  omega

private theorem post_event_control (e : Event C hP I) :
    (C.run hP (e.1,C.initial) (readTime C hP I e.1 e.2 + 1)).2 =
      replay C C.initial (eventWord C hP I e) :=
  congrArg Prod.snd (trace_reconstruction C hP e.1 _)

noncomputable abbrev finalEvent (x : ZMod (3 * P)) : Event C hP I :=
  ⟨x,⟨reads C hP I x - 1,by have := reads_pos C hP I x; omega⟩⟩

private theorem final_halt (x : ZMod (3 * P)) :
    C.instruction (replay C C.initial (eventWord C hP I (finalEvent C hP I x))) = .halt x := by
  have hc := post_event_control C hP I (finalEvent C hP I x)
  dsimp only [finalEvent] at hc
  rw [last_read_time] at hc
  have hn : I.length x - 1 + 1 = I.length x := by
    have := (I.shape x).first_before_stop; omega
  rw [hn] at hc
  rw [← hc]
  exact (I.finite x).halt

/-- A full prefix is terminal precisely at its original input's last read. -/
private theorem terminal_event_iff (e : Event C hP I) :
    (∃ x, C.instruction (replay C C.initial (eventWord C hP I e)) = .halt x) ↔
      e.2.val + 1 = reads C hP I e.1 := by
  constructor
  · rintro ⟨x,hx⟩
    by_contra hn
    have hi : e.2.val + 1 < reads C hP I e.1 := by have := e.2.isLt; omega
    have hlt : readTime C hP I e.1 e.2 + 1 < I.length e.1 := by
      have hs := (readTimes C hP I e.1).orderEmbOfFin rfl |>.strictMono
        (show e.2 < ⟨e.2.val + 1,hi⟩ from by change e.2.val < e.2.val + 1; omega)
      change readTime C hP I e.1 e.2 < readTime C hP I e.1 ⟨e.2.val + 1,hi⟩ at hs
      have hb : readTime C hP I e.1 ⟨e.2.val + 1,hi⟩ < I.length e.1 :=
        event_time_bound C hP I ⟨e.1,⟨e.2.val + 1,hi⟩⟩
      omega
    have hc := post_event_control C hP I e
    rw [← hc] at hx
    exact (I.finite e.1).live _ hlt x hx
  · intro hi
    have he : e = finalEvent C hP I e.1 := by
      rcases e with ⟨x,i⟩
      dsimp only [finalEvent]
      congr 1
      apply Fin.ext
      dsimp only at hi
      change i.val = reads C hP I x - 1
      omega
    rw [he]
    exact ⟨e.1,final_halt C hP I e.1⟩

/-- Leaves are graph leaves of the actual full-prefix parent relation. -/
def IsLeaf [NeZero (3 * P)] (n : History C hP I) : Prop :=
  ∀ m, parent C hP I m ≠ some n

private theorem event_parent_or_first [NeZero (3 * P)] (e : Event C hP I) :
    parent C hP I (event C hP I e) = none ∨
      ∃ (i : Nat) (hi : i + 1 < reads C hP I e.1),
        e.2.val = i + 1 ∧ parent C hP I (event C hP I e) =
          some (event C hP I ⟨e.1,⟨i,by omega⟩⟩) := by
  rcases e with ⟨x,j⟩
  by_cases hz : j.val = 0
  · left
    have he : j = ⟨0,reads_pos C hP I x⟩ := Fin.ext hz
    subst j; exact first_parent C hP I x
  · right
    have hi : j.val - 1 + 1 < reads C hP I x := by have := j.isLt; omega
    refine ⟨j.val - 1,hi,by dsimp only; omega,?_⟩
    have he : (⟨j.val - 1 + 1,hi⟩ : Fin (reads C hP I x)) = j :=
      Fin.ext (by change j.val - 1 + 1 = j.val; omega)
    simpa only [he] using parent_successor C hP I x (j.val - 1) hi

/-- A history is a leaf exactly when its actual post-read control halts. -/
theorem leaf_iff_terminal [NeZero (3 * P)] (n : History C hP I) :
    IsLeaf C hP I n ↔ ∃ x, C.instruction (replay C C.initial n.val) = .halt x := by
  obtain ⟨e,he⟩ := event_surjective C hP I n
  subst n
  change IsLeaf C hP I (event C hP I e) ↔
    ∃ x, C.instruction (replay C C.initial (eventWord C hP I e)) = .halt x
  rw [terminal_event_iff]
  constructor
  · intro hn
    by_contra hi
    have hb : e.2.val + 1 < reads C hP I e.1 := by have := e.2.isLt; omega
    have hp := parent_successor C hP I e.1 e.2.val hb
    have hh : (⟨e.2.val,by omega⟩ : Fin (reads C hP I e.1)) = e.2 := Fin.ext rfl
    rw [hh] at hp
    exact hn _ hp
  · intro hi m hm
    obtain ⟨d,hd⟩ := event_surjective C hP I m
    subst m
    rcases event_parent_or_first C hP I d with hp | ⟨j,hj,_,hp⟩
    · rw [hp] at hm; cases hm
    · have he := Option.some.inj (hp.symm.trans hm)
      have ht := (terminal_event_iff C hP I ⟨d.1,⟨j,by omega⟩⟩).1
        (by rw [show eventWord C hP I ⟨d.1,⟨j,by omega⟩⟩ = eventWord C hP I e from
          congrArg Subtype.val he]; exact (terminal_event_iff C hP I e).2 hi)
      dsimp only at ht
      omega

/-- Every leaf keeps its original label, without output relabeling. -/
theorem leaf_original [NeZero (3 * P)] (n : History C hP I)
    (hn : IsLeaf C hP I n) (x : ZMod (3 * P)) (hx : x ∈ support C hP I n) :
    C.instruction (replay C C.initial n.val) = .halt x := by
  obtain ⟨_,i,hi⟩ := Finset.mem_filter.mp hx
  subst n
  have ht := (terminal_event_iff C hP I ⟨x,i⟩).1 ((leaf_iff_terminal C hP I _).1 hn)
  have he : i = (finalEvent C hP I x).2 := Fin.ext (by dsimp only [finalEvent] at * ; omega)
  subst i
  exact final_halt C hP I x

/-- The exact leaf inventory is equivalent to all 3P fixed original labels. -/
noncomputable def leafEquiv [NeZero (3 * P)] :
    ZMod (3 * P) ≃ {n : History C hP I // IsLeaf C hP I n} :=
  Equiv.ofBijective (fun x => ⟨event C hP I (finalEvent C hP I x),
    (leaf_iff_terminal C hP I _).2 ⟨x,final_halt C hP I x⟩⟩) (by
    constructor
    · intro x y he
      have hw := congrArg (fun n => n.val.val) he
      change eventWord C hP I (finalEvent C hP I x) =
        eventWord C hP I (finalEvent C hP I y) at hw
      have hx := final_halt C hP I x
      rw [hw] at hx
      exact UnitInstruction.halt.inj (hx.symm.trans (final_halt C hP I y))
    · rintro ⟨n,hn⟩
      obtain ⟨⟨x,i⟩,he⟩ := event_surjective C hP I n
      subst n
      have ht := (terminal_event_iff C hP I ⟨x,i⟩).1 ((leaf_iff_terminal C hP I _).1 hn)
      have hi : i = (finalEvent C hP I x).2 := Fin.ext (by dsimp only [finalEvent] at * ; omega)
      subst i
      exact ⟨x,rfl⟩)


private theorem parent_level [NeZero (3 * P)] {n p : History C hP I}
    (hp : parent C hP I n = some p) : level C hP I n = level C hP I p + 1 := by
  obtain ⟨e,he⟩ := event_surjective C hP I n
  subst n
  rcases event_parent_or_first C hP I e with hn | ⟨i,hi,he,hpar⟩
  · rw [hn] at hp; cases hp
  · have hpp := Option.some.inj (hp.symm.trans hpar)
    rw [hpp,event_level,event_level]
    exact he

private theorem support_parent [NeZero (3 * P)] {n p : History C hP I}
    (hp : parent C hP I n = some p) : support C hP I n ⊆ support C hP I p := by
  intro x hx
  obtain ⟨_,j,hj⟩ := Finset.mem_filter.mp hx
  subst n
  rcases event_parent_or_first C hP I ⟨x,j⟩ with hn | ⟨i,hi,_,hpar⟩
  · rw [hn] at hp; cases hp
  · have hpp := Option.some.inj (hp.symm.trans hpar)
    dsimp only at hi
    rw [hpp]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨i,by omega⟩,rfl⟩


end D5.S3.ObserverMemory.Algorithms.StationaryReadHistory
