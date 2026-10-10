/- GID: D5/S3/ObserverMemory/Algorithms/StationaryHistoryContinuation
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/StationaryHistoryContinuation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual original controller histories and their continuation laws. -/

import D5.S3.ObserverMemory.Algorithms.StationaryHistoryPrefix

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.StationaryReadHistory

open StationaryUnitControl
open scoped BigOperators
open private replay_append trace_length shift_append read_time_mem event_time_bound event_is_read
  trace_eq_map trace_take trace_get action_read_iff count_reads_trace reads_pos reads_bound
  first_read_time last_read_time read_rank event_level event_time event_shift support_nonempty
  previous_times_event previous_prefix_actual previous_time_last trace_common digit_block
  first_event_word root_word_actual first_event first_parent event_color trace_counts
  post_event_control final_halt terminal_event_iff event_parent_or_first parent_level
  support_parent from D5.S3.ObserverMemory.Algorithms.StationaryHistoryPrefix
attribute [local instance] Classical.propDecidable

universe u
variable {P ell h : Nat} {Q : Type u} (C : Controller P Q) (hP : 1 < P)
    (I : Initialized C hP ell h)

/-- Indexed event fibers never identify ancestor and descendant occurrences. -/
noncomputable def indexedSupport [NeZero (3 * P)] (n : History C hP I) : Finset (Event C hP I) :=
  Finset.univ.filter (fun e => event C hP I e = n)

private theorem indexed_disjoint [NeZero (3 * P)] {n m : History C hP I} (hn : n ≠ m) :
    Disjoint (indexedSupport C hP I n) (indexedSupport C hP I m) := by
  apply Finset.disjoint_left.mpr
  intro e he hm
  exact hn ((Finset.mem_filter.mp he).2.symm.trans (Finset.mem_filter.mp hm).2)

noncomputable def phaseSupport [NeZero (3 * P)] (n : History C hP I) : Finset (ZMod (3 * P)) :=
  (support C hP I n).image (fun x => x + (historyShift C hP I n : ZMod (3 * P)))

/-- Distinct full histories at one actual read control have disjoint physical phases.
Finite correctness separates the original input and time even across control cycles. -/
theorem same_control_phase_disjoint [NeZero (3 * P)] {n m : History C hP I}
    (hn : n ≠ m) (hq : readControl C hP I n = readControl C hP I m) :
    Disjoint (phaseSupport C hP I n) (phaseSupport C hP I m) := by
  apply Finset.disjoint_left.mpr
  intro s hs ht
  obtain ⟨x,hx,hxs⟩ := Finset.mem_image.mp hs
  obtain ⟨y,hy,hys⟩ := Finset.mem_image.mp ht
  obtain ⟨_,i,hi⟩ := Finset.mem_filter.mp hx
  obtain ⟨_,j,hj⟩ := Finset.mem_filter.mp hy
  have hb : time C hP I n < I.length x := by
    rw [← hi,event_time]; exact event_time_bound C hP I ⟨x,i⟩
  have hc : time C hP I m < I.length y := by
    rw [← hj,event_time]; exact event_time_bound C hP I ⟨y,j⟩
  have hrun : C.run hP (x,C.initial) (time C hP I n) =
      C.run hP (y,C.initial) (time C hP I m) := by
    rw [history_configuration C hP I n x hx,history_configuration C hP I m y hy,hq,hxs,hys]
  obtain ⟨hxy,htime⟩ := initialized_configuration_unique C hP I
    (Nat.le_of_lt hb) (Nat.le_of_lt hc) hrun
  subst y
  have ht' : readTime C hP I x i = readTime C hP I x j := by
    rw [← hi,← hj,event_time,event_time] at htime
    exact htime
  have hij := (readTimes C hP I x).orderEmbOfFin rfl |>.injective ht'
  subst j
  exact hn (hi.symm.trans hj)

private theorem literal_gap_positive (x : ZMod (3 * P)) (i : Nat)
    (hi : i + 1 < reads C hP I x) :
    readTime C hP I x ⟨i,by omega⟩ + 1 < readTime C hP I x ⟨i + 1,hi⟩ := by
  have hs := (readTimes C hP I x).orderEmbOfFin rfl |>.strictMono
    (show (⟨i,by omega⟩ : Fin (reads C hP I x)) < ⟨i + 1,hi⟩ from by change i < i + 1; omega)
  change readTime C hP I x ⟨i,by omega⟩ < readTime C hP I x ⟨i + 1,hi⟩ at hs
  by_contra hn
  have he : readTime C hP I x ⟨i + 1,hi⟩ = readTime C hP I x ⟨i,by omega⟩ + 1 := by omega
  have hb : readTime C hP I x ⟨i + 1,hi⟩ < I.length x := event_time_bound C hP I ⟨x,⟨i + 1,hi⟩⟩
  have hw := (I.shape x).after_read_wait (readTime C hP I x ⟨i,by omega⟩)
    (by omega) (event_is_read C hP I ⟨x,⟨i,by omega⟩⟩)
  rw [← he] at hw
  obtain ⟨q,hwait⟩ := hw
  obtain ⟨row,hread⟩ := event_is_read C hP I ⟨x,⟨i + 1,hi⟩⟩
  rw [hwait] at hread; cases hread

/-- The literal wait between consecutive reads equals their increase in physical shift. -/
theorem literal_shift_gap [NeZero (3 * P)] (x : ZMod (3 * P)) (i : Nat)
    (hi : i + 1 < reads C hP I x) :
    0 < readTime C hP I x ⟨i + 1,hi⟩ - (readTime C hP I x ⟨i,by omega⟩ + 1) ∧
    historyShift C hP I (event C hP I ⟨x,⟨i + 1,hi⟩⟩) =
      historyShift C hP I (event C hP I ⟨x,⟨i,by omega⟩⟩) + 
        (readTime C hP I x ⟨i + 1,hi⟩ - (readTime C hP I x ⟨i,by omega⟩ + 1)) := by
  have hpos := literal_gap_positive C hP I x i hi
  have hnext := history_time_decomposition C hP I (event C hP I ⟨x,⟨i + 1,hi⟩⟩)
  have hprev := history_time_decomposition C hP I (event C hP I ⟨x,⟨i,by omega⟩⟩)
  rw [event_time,event_level] at hnext hprev
  dsimp only at hnext hprev
  constructor <;> omega


/-- Roots have the three original absolute read answers. -/
noncomputable def rootEquiv [NeZero (3 * P)] :
    Fin 3 ≃ {n : History C hP I // parent C hP I n = none} :=
  Equiv.ofBijective (fun c => ⟨root C hP I c,(roots_exact C hP I _).2 ⟨c,rfl⟩⟩) (by
    constructor
    · intro c d he
      have hw := congrArg (fun n => color C hP I n.val) he
      simpa [color,root,rootWord] using hw
    · rintro ⟨n,hn⟩
      obtain ⟨c,he⟩ := (roots_exact C hP I n).1 hn
      subst n
      exact ⟨c,rfl⟩)

/-- Only true graph leaves have a fixed original output label. -/
noncomputable def leafLabel [NeZero (3 * P)] (n : History C hP I) : ZMod (3 * P) :=
  if hn : IsLeaf C hP I n then (leafEquiv C hP I).symm ⟨n,hn⟩ else 0

noncomputable def children [NeZero (3 * P)] (n : History C hP I) : Finset (History C hP I) :=
  Finset.univ.filter (fun m => parent C hP I m = some n)

/-- An actual singleton which continues has one child; it is retained as a unary
history rather than treated as an artificial stopping leaf. -/
theorem singleton_continuation [NeZero (3 * P)] (n : History C hP I)
    (hs : (support C hP I n).card = 1) (hn : ¬IsLeaf C hP I n) :
    (children C hP I n).card = 1 := by
  obtain ⟨x,hx⟩ := Finset.card_eq_one.mp hs
  have hex : ∃ m, parent C hP I m = some n := by
    by_contra hh
    apply hn
    intro m hm
    exact hh ⟨m,hm⟩
  obtain ⟨m,hm⟩ := hex
  apply Finset.card_eq_one.mpr
  refine ⟨m,Finset.ext ?_⟩
  intro p
  simp only [children,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
  constructor
  · intro hp
    obtain ⟨y,hy⟩ := support_nonempty C hP I p
    obtain ⟨z,hz⟩ := support_nonempty C hP I m
    have hy' := support_parent C hP I hp hy
    have hz' := support_parent C hP I hm hz
    rw [hx] at hy' hz'
    have hyx := Finset.mem_singleton.mp hy'
    have hzx := Finset.mem_singleton.mp hz'
    subst y; subst z
    obtain ⟨_,i,hi⟩ := Finset.mem_filter.mp hy
    obtain ⟨_,j,hj⟩ := Finset.mem_filter.mp hz
    have hil : i.val = level C hP I n + 1 := by
      have hl := parent_level C hP I hp
      rw [← hi,event_level] at hl
      exact hl
    have hjl : j.val = level C hP I n + 1 := by
      have hl := parent_level C hP I hm
      rw [← hj,event_level] at hl
      exact hl
    have hij : i = j := Fin.ext (hil.trans hjl.symm)
    subst j
    exact hi.symm.trans hj
  · rintro rfl; exact hm

private theorem root_data [NeZero (3 * P)] (c : Fin 3) :
    color C hP I (root C hP I c) = c ∧
    historyShift C hP I (root C hP I c) = ell ∧ level C hP I (root C hP I c) = 0 := by
  simp [color,root,rootWord,historyShift,level,shift,readNumber,
    List.filter_append,List.filter_replicate,List.filter,Action.isWait,Action.isRead]

/-- The first-answer fibers are exactly the three original digit blocks translated
by the literal common prefix. -/
theorem root_support [NeZero (3 * P)] (c : Fin 3) (x : ZMod (3 * P)) :
    x ∈ support C hP I (root C hP I c) ↔ digit hP (x + (ell : ZMod (3 * P))) = c := by
  constructor
  · intro hx
    obtain ⟨_,i,hi⟩ := Finset.mem_filter.mp hx
    have hl := event_level C hP I ⟨x,i⟩
    rw [hi,(root_data C hP I c).2.2] at hl
    have hz : i = ⟨0,reads_pos C hP I x⟩ := Fin.ext hl.symm
    subst i
    rw [first_event] at hi
    have hc := congrArg (color C hP I) hi
    rw [(root_data C hP I _).1,(root_data C hP I c).1] at hc
    exact hc
  · intro hc
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,⟨0,reads_pos C hP I x⟩,?_⟩
    rw [first_event,hc]


end D5.S3.ObserverMemory.Algorithms.StationaryReadHistory
