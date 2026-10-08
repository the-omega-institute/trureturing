/- GID: D5/S3/ObserverMemory/Algorithms/StationaryHistoryRows
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/StationaryHistoryRows
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual original controller histories and their rows laws. -/

import D5.S3.ObserverMemory.Algorithms.StationaryHistoryData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.StationaryReadHistory

open StationaryUnitControl
open private trajectory_waits from D5.S3.ObserverMemory.Algorithms.StationaryUnitControl
open scoped BigOperators
open private replay_append trace_length shift_append read_time_mem event_time_bound event_is_read
  trace_eq_map trace_take trace_get action_read_iff count_reads_trace reads_pos reads_bound
  first_read_time last_read_time read_rank event_level event_time event_shift support_nonempty
  previous_times_event previous_prefix_actual previous_time_last trace_common digit_block
  first_event_word root_word_actual first_event first_parent event_color trace_counts
  post_event_control final_halt terminal_event_iff event_parent_or_first parent_level
  support_parent from D5.S3.ObserverMemory.Algorithms.StationaryHistoryPrefix
open private indexed_disjoint literal_gap_positive root_data from
  D5.S3.ObserverMemory.Algorithms.StationaryHistoryContinuation
attribute [local instance] Classical.propDecidable

universe u
variable {P ell h : Nat} {Q : Type u} (C : Controller P Q) (hP : 1 < P)
    (I : Initialized C hP ell h)

private theorem consecutive_waits (x : ZMod (3 * P)) (i : Nat)
    (hi : i + 1 < reads C hP I x) {t : Nat}
    (ha : readTime C hP I x ⟨i, by omega⟩ < t)
    (hb : t < readTime C hP I x ⟨i + 1, hi⟩) :
    IsWait C (C.run hP (x, C.initial) t).2 := by
  have ht : t < I.length x := lt_trans hb (event_time_bound C hP I ⟨x,⟨i + 1, hi⟩⟩)
  cases ins : C.instruction (C.run hP (x, C.initial) t).2 with
  | wait next => exact ⟨next,ins⟩
  | halt z => exact False.elim ((I.finite x).live t ht z ins)
  | read row =>
    have hm : t ∈ readTimes C hP I x :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ht,⟨row,ins⟩⟩
    let j := ((readTimes C hP I x).orderIsoOfFin rfl).symm ⟨t,hm⟩
    have hj : readTime C hP I x j = t :=
      congrArg Subtype.val ((readTimes C hP I x).orderIsoOfFin rfl |>.apply_symm_apply ⟨t,hm⟩)
    have hja : (⟨i, by omega⟩ : Fin (reads C hP I x)) < j := by
      apply (readTimes C hP I x).orderEmbOfFin rfl |>.lt_iff_lt.mp
      change readTime C hP I x ⟨i, by omega⟩ < readTime C hP I x j
      rwa [hj]
    have hjb : j < (⟨i + 1, hi⟩ : Fin (reads C hP I x)) := by
      apply (readTimes C hP I x).orderEmbOfFin rfl |>.lt_iff_lt.mp
      change readTime C hP I x j < readTime C hP I x ⟨i + 1, hi⟩
      rwa [hj]
    have : i < j.val := hja
    have : j.val < i + 1 := hjb
    omega

/-- The actual consecutive-read trajectory supplies the literal wait chain.
The chain starts after the source read and ends at its first future read. -/
theorem event_arrival (x : ZMod (3 * P)) (i : Nat)
    (hi : i + 1 < reads C hP I x) :
    Waits C (readTime C hP I x ⟨i + 1, hi⟩ - (readTime C hP I x ⟨i, by omega⟩ + 1))
      (replay C C.initial (eventWord C hP I ⟨x,⟨i, by omega⟩⟩))
      (C.run hP (x, C.initial) (readTime C hP I x ⟨i + 1, hi⟩)).2 := by
  have hp := literal_gap_positive C hP I x i hi
  have hw := trajectory_waits C hP (x, C.initial)
    (t := readTime C hP I x ⟨i, by omega⟩ + 1)
    (d := readTime C hP I x ⟨i + 1, hi⟩ - (readTime C hP I x ⟨i, by omega⟩ + 1))
    (fun k hk => consecutive_waits C hP I x i hi (by omega) (by omega))
  have he : readTime C hP I x ⟨i, by omega⟩ + 1 +
      (readTime C hP I x ⟨i + 1, hi⟩ - (readTime C hP I x ⟨i, by omega⟩ + 1)) =
      readTime C hP I x ⟨i + 1, hi⟩ := by omega
  rw [he,post_event_control C hP I ⟨x,⟨i, by omega⟩⟩] at hw
  exact hw

def postControl [NeZero (3 * P)] (n : History C hP I) : Q :=
  replay C C.initial n.val

/-- Each full history uses its actual source read row and recorded answer. -/
theorem history_row_execution [NeZero (3 * P)] (n : History C hP I) :
    ∃ row, C.instruction (readControl C hP I n) = .read row ∧
      postControl C hP I n = row (color C hP I n) := by
  obtain ⟨e,he⟩ := event_surjective C hP I n
  subst n
  obtain ⟨row,hr⟩ := event_is_read C hP I e
  have hc : (C.run hP (e.1,C.initial) (readTime C hP I e.1 e.2)).2 =
      readControl C hP I (event C hP I e) :=
    congrArg Prod.snd (event_reconstruction C hP I e).1
  refine ⟨row,?_,?_⟩
  · rwa [← hc]
  · rw [postControl,← post_event_control]
    have hs : C.run hP (e.1,C.initial) (readTime C hP I e.1 e.2 + 1) =
        C.next hP (C.run hP (e.1,C.initial) (readTime C hP I e.1 e.2)) :=
      Function.iterate_succ_apply' _ _ _
    rw [hs]
    simp only [Controller.next,Controller.step,hr,Option.getD_some,event_color]

private theorem same_row_post [NeZero (3 * P)] {n m : History C hP I}
    (hq : readControl C hP I n = readControl C hP I m)
    (hc : color C hP I n = color C hP I m) :
    postControl C hP I n = postControl C hP I m := by
  obtain ⟨r,hr,hpost⟩ := history_row_execution C hP I n
  obtain ⟨s,hs,hother⟩ := history_row_execution C hP I m
  rw [← hq,hr] at hs
  have hrs : r = s := UnitInstruction.read.inj hs
  rw [hpost,hother,hrs,hc]

/-- A child records the first future read after a positive literal wait. -/
theorem child_arrival [NeZero (3 * P)] {n p : History C hP I}
    (hp : parent C hP I n = some p) :
    0 < time C hP I n - (time C hP I p + 1) ∧
    Waits C (time C hP I n - (time C hP I p + 1))
      (postControl C hP I p) (readControl C hP I n) ∧
    IsRead C (readControl C hP I n) := by
  obtain ⟨e,he⟩ := event_surjective C hP I n
  subst n
  rcases event_parent_or_first C hP I e with hn | ⟨i, hi,he,hpar⟩
  · rw [hn] at hp; cases hp
  · have hpp := Option.some.inj (hp.symm.trans hpar)
    rw [hpp]
    have hei : e.2 = ⟨i + 1, hi⟩ := Fin.ext he
    rcases e with ⟨x,j⟩
    dsimp only at hei
    rw [hei]
    dsimp only
    rw [event_time,event_time]
    have hc := congrArg Prod.snd (event_reconstruction C hP I ⟨x,⟨i + 1, hi⟩⟩).1
    change (C.run hP (x, C.initial) (readTime C hP I x ⟨i + 1, hi⟩)).2 =
      readControl C hP I (event C hP I ⟨x,⟨i + 1, hi⟩⟩) at hc
    rw [← hc]
    dsimp only
    exact ⟨by have := literal_gap_positive C hP I x i hi; omega,
      event_arrival C hP I x i hi,event_is_read C hP I ⟨x,⟨i + 1, hi⟩⟩⟩

/-- All continuing full histories on one actual row have the same literal
waiting length and next read target, including histories at different levels. -/
theorem same_row_arrival [NeZero (3 * P)] {n m a b : History C hP I}
    (ha : parent C hP I a = some n) (hb : parent C hP I b = some m)
    (hq : readControl C hP I n = readControl C hP I m)
    (hc : color C hP I n = color C hP I m) :
    time C hP I a - (time C hP I n + 1) = time C hP I b - (time C hP I m + 1) ∧
    readControl C hP I a = readControl C hP I b := by
  obtain ⟨_,wa,ra⟩ := child_arrival C hP I ha
  obtain ⟨_,wb,rb⟩ := child_arrival C hP I hb
  rw [same_row_post C hP I hq hc] at wa
  exact waits_to_read_unique C wa wb ra rb

/-- A terminal actual row contains exactly one full history. -/
theorem terminal_row_unique [NeZero (3 * P)] {n m : History C hP I}
    (hn : IsLeaf C hP I n)
    (hq : readControl C hP I n = readControl C hP I m)
    (hc : color C hP I n = color C hP I m) : n = m := by
  obtain ⟨x,hx⟩ := support_nonempty C hP I n
  obtain ⟨y,hy⟩ := support_nonempty C hP I m
  have hout := leaf_original C hP I n hn x hx
  have hpost := same_row_post C hP I hq hc
  have hm : IsLeaf C hP I m := (leaf_iff_terminal C hP I m).2 ⟨x,by
    change C.instruction (postControl C hP I m) = .halt x
    rw [← hpost]; exact hout⟩
  have hyout := leaf_original C hP I m hm y hy
  have hxy : x = y := UnitInstruction.halt.inj (by
    change C.instruction (postControl C hP I n) = .halt x at hout
    rw [hpost] at hout
    exact hout.symm.trans hyout)
  subst y
  obtain ⟨_,i, hi⟩ := Finset.mem_filter.mp hx
  obtain ⟨_,j,hj⟩ := Finset.mem_filter.mp hy
  have hil := (terminal_event_iff C hP I ⟨x,i⟩).1
    ((leaf_iff_terminal C hP I (event C hP I ⟨x,i⟩)).1 (by rwa [hi]))
  have hjl := (terminal_event_iff C hP I ⟨x,j⟩).1
    ((leaf_iff_terminal C hP I (event C hP I ⟨x,j⟩)).1 (by rwa [hj]))
  have hij : i = j := Fin.ext (by dsimp only at hil hjl; omega)
  subst j
  exact hi.symm.trans hj

private theorem trace_wait_segment (x : ZMod (3 * P)) (t d : Nat)
    (hw : ∀ k, k < d → IsWait C (C.run hP (x, C.initial) (t + k)).2) :
    trace C hP x (t + d) = trace C hP x t ++ List.replicate d .wait := by
  induction d with
  | zero => simp
  | succ d ih =>
    obtain ⟨q,hq⟩ := hw d (by omega)
    rw [show t + (d + 1) = (t + d) + 1 from by omega,trace,
      ih (fun k hk => hw k (by omega))]
    simp only [action,hq]
    rw [List.replicate_succ',List.append_assoc]

private theorem event_word_successor [NeZero (3 * P)] (x : ZMod (3 * P)) (i : Nat)
    (hi : i + 1 < reads C hP I x) :
    (event C hP I ⟨x,⟨i + 1, hi⟩⟩).val =
      (event C hP I ⟨x,⟨i, by omega⟩⟩).val ++
        List.replicate (readTime C hP I x ⟨i + 1, hi⟩ -
          (readTime C hP I x ⟨i, by omega⟩ + 1)) .wait ++
        [.read (color C hP I (event C hP I ⟨x,⟨i + 1, hi⟩⟩))] := by
  have hp := literal_gap_positive C hP I x i hi
  have hw := trace_wait_segment C hP x (readTime C hP I x ⟨i, by omega⟩ + 1)
    (readTime C hP I x ⟨i + 1, hi⟩ - (readTime C hP I x ⟨i, by omega⟩ + 1))
    (fun k hk => consecutive_waits C hP I x i hi (by omega) (by omega))
  have he : readTime C hP I x ⟨i, by omega⟩ + 1 +
      (readTime C hP I x ⟨i + 1, hi⟩ - (readTime C hP I x ⟨i, by omega⟩ + 1)) =
      readTime C hP I x ⟨i + 1, hi⟩ := by omega
  rw [he] at hw
  change trace C hP x (readTime C hP I x ⟨i + 1, hi⟩ + 1) = _
  rw [trace,hw]
  obtain ⟨row,hr⟩ := event_is_read C hP I ⟨x,⟨i + 1, hi⟩⟩
  simp only [action,hr,event_color]
  rfl

/-- A child's full word retains its parent, every literal wait, and its answer. -/
theorem child_word [NeZero (3 * P)] {n p : History C hP I}
    (hp : parent C hP I n = some p) :
    n.val = p.val ++ List.replicate (time C hP I n - (time C hP I p + 1)) .wait ++
      [.read (color C hP I n)] := by
  obtain ⟨e,he⟩ := event_surjective C hP I n
  subst n
  rcases event_parent_or_first C hP I e with hn | ⟨i, hi,he,hpar⟩
  · rw [hn] at hp; cases hp
  · have hpp := Option.some.inj (hp.symm.trans hpar)
    rw [hpp]
    rcases e with ⟨x,j⟩
    dsimp only at hi he ⊢
    have hei : j = ⟨i + 1, hi⟩ := Fin.ext he
    rw [hei]
    simp only [event_time]
    exact event_word_successor C hP I x i hi

/-- A parent has at most one full-history child with any given absolute digit. -/
theorem child_digit_injective [NeZero (3 * P)] {p n m : History C hP I}
    (hn : parent C hP I n = some p) (hm : parent C hP I m = some p)
    (hc : color C hP I n = color C hP I m) : n = m := by
  have hd := (same_row_arrival C hP I hn hm rfl rfl).1
  apply Subtype.ext
  rw [child_word C hP I hn,child_word C hP I hm,hd,hc]

noncomputable def delay [NeZero (3 * P)] (p : History C hP I) : Nat :=
  if hs : (children C hP I p).Nonempty then
    time C hP I (Classical.choose hs) - (time C hP I p + 1)
  else 0

noncomputable def nextTarget [NeZero (3 * P)] (p : History C hP I) : Q :=
  if hs : (children C hP I p).Nonempty then
    readControl C hP I (Classical.choose hs)
  else readControl C hP I p

private theorem chosen_child [NeZero (3 * P)] (p : History C hP I)
    (hs : (children C hP I p).Nonempty) :
    parent C hP I (Classical.choose hs) = some p :=
  (Finset.mem_filter.mp (Classical.choose_spec hs)).2

/-- Literal delay and target are derived from actual children, and are independent
of the chosen child or of an arbitrary history on the same continuing row. -/
theorem child_delay_target [NeZero (3 * P)] {n p : History C hP I}
    (hp : parent C hP I n = some p) :
    0 < delay C hP I p ∧
    time C hP I n - (time C hP I p + 1) = delay C hP I p ∧
    readControl C hP I n = nextTarget C hP I p ∧
    historyShift C hP I n = historyShift C hP I p + delay C hP I p := by
  have hs : (children C hP I p).Nonempty :=
    ⟨n,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩⟩
  have hc := chosen_child C hP I p hs
  have he := same_row_arrival C hP I hp hc rfl rfl
  have hd : time C hP I n - (time C hP I p + 1) = delay C hP I p := by
    simpa only [delay,dif_pos hs] using he.1
  refine ⟨?_,hd,?_,?_⟩
  · rw [← hd]; exact (child_arrival C hP I hp).1
  · simpa only [nextTarget,dif_pos hs] using he.2
  · have hn := history_time_decomposition C hP I n
    have hpp := history_time_decomposition C hP I p
    have hl := parent_level C hP I hp
    have hpos := (child_arrival C hP I hp).1
    rw [← hd]
    omega

/-- The actual per-history delay and next target are coherent on every continuing
source row; repeated full histories are not merged by this equality. -/
theorem row_delay_target [NeZero (3 * P)] {n m : History C hP I}
    (hn : (children C hP I n).Nonempty)
    (hq : readControl C hP I n = readControl C hP I m)
    (hc : color C hP I n = color C hP I m) :
    delay C hP I n = delay C hP I m ∧ nextTarget C hP I n = nextTarget C hP I m := by
  have hml : ¬IsLeaf C hP I m := by
    intro hl
    have he := terminal_row_unique C hP I hl hq.symm hc.symm
    subst n
    obtain ⟨a,ha⟩ := hn
    exact hl a (Finset.mem_filter.mp ha).2
  have hm : (children C hP I m).Nonempty := by
    by_contra hh
    apply hml
    intro a ha
    exact hh ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩⟩
  obtain ⟨a,ha⟩ := hn
  obtain ⟨b,hb⟩ := hm
  have hpa := (Finset.mem_filter.mp ha).2
  have hpb := (Finset.mem_filter.mp hb).2
  have h := same_row_arrival C hP I hpa hpb hq hc
  rw [(child_delay_target C hP I hpa).2.1,(child_delay_target C hP I hpb).2.1,
    (child_delay_target C hP I hpa).2.2.1,(child_delay_target C hP I hpb).2.2.1] at h
  exact h

private theorem supported_color [NeZero (3 * P)] (n : History C hP I)
    (x : ZMod (3 * P)) (hx : x ∈ support C hP I n) :
    digit hP (x + (historyShift C hP I n : ZMod (3 * P))) = color C hP I n := by
  obtain ⟨_,i, hi⟩ := Finset.mem_filter.mp hx
  have hc := event_color C hP I ⟨x,i⟩
  rw [hi] at hc
  have hs := congrArg Prod.fst (history_configuration C hP I n x hx)
  rw [← hi,event_time] at hs
  dsimp only at hs hc
  rw [hs, hi] at hc
  exact hc.symm

/-- Every parent-support label continues to a child when one actual child exists.
The label's own next read remains indexed at level(parent)+1. -/
theorem support_successor [NeZero (3 * P)] {p : History C hP I}
    (hp : (children C hP I p).Nonempty) (x : ZMod (3 * P))
    (hx : x ∈ support C hP I p) :
    ∃ n, parent C hP I n = some p ∧ x ∈ support C hP I n := by
  obtain ⟨_,i, hi⟩ := Finset.mem_filter.mp hx
  have hn : ¬IsLeaf C hP I p := by
    intro hl
    obtain ⟨n,hn⟩ := hp
    exact hl n (Finset.mem_filter.mp hn).2
  have hb : i.val + 1 < reads C hP I x := by
    have ht : ¬(∃ z, C.instruction (replay C C.initial (eventWord C hP I ⟨x,i⟩)) = .halt z) := by
      intro hh
      apply hn
      rw [← hi]
      exact (leaf_iff_terminal C hP I _).2 hh
    have := i.isLt
    have hf := mt (terminal_event_iff C hP I ⟨x,i⟩).2 ht
    dsimp only at hf
    omega
  refine ⟨event C hP I ⟨x,⟨i.val + 1,hb⟩⟩,?_,?_⟩
  · have hs := parent_successor C hP I x i.val hb
    have hh : (⟨i.val, by omega⟩ : Fin (reads C hP I x)) = i := Fin.ext rfl
    rwa [hh, hi] at hs
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨i.val + 1,hb⟩,rfl⟩

/-- The exact child fiber is the translated parent fiber intersected with its
absolute digit block. No supplied interval or branching premise is used. -/
theorem child_support [NeZero (3 * P)] {n p : History C hP I}
    (hp : parent C hP I n = some p) (x : ZMod (3 * P)) :
    x ∈ support C hP I n ↔ x ∈ support C hP I p ∧
      digit hP (x + (historyShift C hP I n : ZMod (3 * P))) = color C hP I n := by
  constructor
  · intro hx
    exact ⟨support_parent C hP I hp hx,supported_color C hP I n x hx⟩
  · rintro ⟨hx,hc⟩
    have hs : (children C hP I p).Nonempty :=
      ⟨n,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩⟩
    obtain ⟨m,hm,hxm⟩ := support_successor C hP I hs x hx
    have shiftEq : historyShift C hP I m = historyShift C hP I n := by
      rw [(child_delay_target C hP I hm).2.2.2,(child_delay_target C hP I hp).2.2.2]
    have hmc := supported_color C hP I m x hxm
    rw [shiftEq,hc] at hmc
    have hmn := child_digit_injective C hP I hm hp hmc.symm
    rwa [hmn] at hxm

private theorem digit_translate [NeZero (3 * P)] (s : ZMod (3 * P)) (d : Nat) :
    (digit hP (s + (d : ZMod (3 * P)))).val =
      ((digit hP s).val + d / P + if P ≤ s.val % P + d % P then 1 else 0) % 3 := by
  change (s + (d : ZMod (3 * P))).val / P = _
  rw [ZMod.val_add,ZMod.val_natCast,Nat.add_mod_mod,Nat.mod_mul_left_div_self,
    Nat.add_div (by omega : 0 < P)]
  rfl

/-- Every actual history has at most two nonempty children. The literal wait is
unrestricted; its residue creates one common low-phase cut for its source digit. -/
theorem branching [NeZero (3 * P)] (p : History C hP I) :
    (children C hP I p).card ≤ 2 := by
  let a := ((color C hP I p).val + delay C hP I p / P) % 3
  let b := ((color C hP I p).val + delay C hP I p / P + 1) % 3
  have hinj : Set.InjOn (fun n : History C hP I => (color C hP I n).val)
      (children C hP I p) := by
    intro n hn m hm hc
    apply child_digit_injective C hP I (Finset.mem_filter.mp hn).2 (Finset.mem_filter.mp hm).2
    exact Fin.ext hc
  have hsub : (children C hP I p).image (fun n => (color C hP I n).val) ⊆ {a,b} := by
    intro c hc
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hc
    have hp := (Finset.mem_filter.mp hn).2
    obtain ⟨x,hx⟩ := support_nonempty C hP I n
    have hxp := support_parent C hP I hp hx
    have hsc := supported_color C hP I p x hxp
    have hnc := supported_color C hP I n x hx
    have ht := digit_translate hP
      (x + (historyShift C hP I p : ZMod (3 * P))) (delay C hP I p)
    rw [(child_delay_target C hP I hp).2.2.2,Nat.cast_add,← add_assoc] at hnc
    rw [hsc,hnc] at ht
    split at ht
    · simp only [Finset.mem_insert,Finset.mem_singleton]
      exact Or.inr ht
    · simp only [Nat.add_zero,Finset.mem_insert,Finset.mem_singleton] at *
      exact Or.inl ht
  rw [← Finset.card_image_of_injOn hinj]
  exact le_trans (Finset.card_le_card hsub)
    (le_trans (Finset.card_insert_le _ _) (by simp))

open scoped BigOperators

/-- The binary count is forced by the actual parent map, three roots, 3P original
leaves, and the derived branching bound. Unary continuations remain counted. -/
theorem binary_count [NeZero (3 * P)] :
    (Finset.univ.filter (fun n : History C hP I => (children C hP I n).card = 2)).card =
      3 * (P - 1) := by
  let H := History C hP I
  have hroot : (Finset.univ.filter (fun n : H => parent C hP I n = none)).card = 3 := by
    rw [← Fintype.card_subtype]
    exact (actual_history_data C hP I).root_count
  have hleaf : (Finset.univ.filter (IsLeaf C hP I)).card = 3 * P := by
    rw [← Fintype.card_subtype]
    exact (actual_history_data C hP I).leaf_count
  have hz (n : H) : (children C hP I n).card = 0 ↔ IsLeaf C hP I n := by
    simp [Finset.card_eq_zero,Finset.eq_empty_iff_forall_notMem,children,IsLeaf]
  have hp (m : H) :
      (∑ n : H, if parent C hP I m = some n then 1 else 0) +
        (if parent C hP I m = none then 1 else 0) = 1 := by
    cases he : parent C hP I m with
    | none => simp
    | some p =>
      simp only [Option.some.injEq,reduceCtorEq,if_false,Nat.add_zero]
      rw [Finset.sum_eq_single p]
      · simp
      · intro b hb hbp
        simp [Ne.symm hbp]
      · simp
  have hedge : (∑ n : H, (children C hP I n).card) + 3 = Fintype.card H := by
    have he : (∑ n : H, (children C hP I n).card) =
        ∑ m : H, ∑ n : H, if parent C hP I m = some n then 1 else 0 := by
      simp only [children,Finset.card_filter]
      exact Finset.sum_comm
    rw [he,← hroot,Finset.card_filter,← Finset.sum_add_distrib]
    simp only [hp,Finset.sum_const,Finset.card_univ,Nat.nsmul_eq_mul,Nat.mul_one]
  have hlocal (n : H) : (children C hP I n).card + (if IsLeaf C hP I n then 1 else 0) =
      1 + (if (children C hP I n).card = 2 then 1 else 0) := by
    have hb := branching C hP I n
    by_cases hl : IsLeaf C hP I n
    · have hc := (hz n).2 hl
      simp [hl,hc]
    · have hc := mt (hz n).1 hl
      by_cases ht : (children C hP I n).card = 2
      · simp [hl,ht]
      · simp only [if_neg hl,if_neg ht,Nat.add_zero]
        omega
  have hsum := congrArg (fun f : H → Nat => ∑ n : H, f n) (funext hlocal)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
    Nat.nsmul_eq_mul,Nat.mul_one,← Finset.card_filter] at hsum
  rw [hleaf] at hsum
  let total := ∑ n : H, (children C hP I n).card
  let bins := (Finset.univ.filter (fun n : H => (children C hP I n).card = 2)).card
  change total + 3 = Fintype.card H at hedge
  change total + 3 * P = Fintype.card H + bins at hsum
  change bins = 3 * (P - 1)
  omega


end D5.S3.ObserverMemory.Algorithms.StationaryReadHistory
