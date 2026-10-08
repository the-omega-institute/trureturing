/- GID: D5/S3/ObserverMemory/Algorithms/StationaryHistoryCore
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/StationaryHistoryCore
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual original controller histories and their core laws. -/

import D5.S3.ObserverMemory.Algorithms.StationaryHistoryIncidence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.StationaryHistorySlotGraph

open StationaryUnitControl StationaryReadHistory
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
open private consecutive_waits same_row_post trace_wait_segment event_word_successor chosen_child
  supported_color digit_translate from D5.S3.ObserverMemory.Algorithms.StationaryHistoryRows
open private same_digit_span val_add_cases translation_between digit_block_bounds interval_data
  support_low_bounds from D5.S3.ObserverMemory.Algorithms.StationaryReadHistory
open private mem_edges history_time_bounds root_control nonroot_control root_rows_card
  rows_partition roots_disjoint edge_endpoints outgoing_target outgoing_zero binary_outgoing
  production_card production_subset leaf_rows_card leaf_mem leaf_subset edge_count outgoing_sum
  degree_balance representative_row target_history edge_target B_subset_G G_subset_targets
  incoming_positive target_slots_card target_indegree_balance two_target_edges J_total G_card from
  D5.S3.ObserverMemory.Algorithms.StationaryHistoryIncidence
open private fiber_surplus raw_rows_image from
  D5.S3.ObserverMemory.Algorithms.FixedForestSlotGraph
attribute [local instance] Classical.propDecidable

universe u
variable {P ell h : Nat} {Q : Type u} (C : Controller P Q) (hP : 1 < P)
  (I : Initialized C hP ell h) [NeZero (3 * P)] [DecidableEq Q]

private theorem B_card : (B C hP I).card = 3 * (P - 1) - s C hP I := by
  have hs := fiber_surplus (binaries C hP I) (nextTarget C hP I)
  change s C hP I = (binaries C hP I).card - (B C hP I).card at hs
  have hn : (binaries C hP I).card = 3 * (P - 1) := binary_count C hP I
  have hb := Finset.card_image_le (s := binaries C hP I) (f := nextTarget C hP I)
  change (B C hP I).card ≤ (binaries C hP I).card at hb
  omega

private theorem selection_exists : ∃ D : Finset Q,
    D ⊆ G C hP I \ B C hP I ∧ D.card = s C hP I := by
  have hs := fiber_surplus (binaries C hP I) (nextTarget C hP I)
  change s C hP I = (binaries C hP I).card - (B C hP I).card at hs
  have hn : (binaries C hP I).card = 3 * (P - 1) := binary_count C hP I
  have hG := G_card C hP I
  have hd := Finset.le_card_sdiff (B C hP I) (G C hP I)
  exact Finset.exists_subset_card_eq (by omega : s C hP I ≤ (G C hP I \ B C hP I).card)

noncomputable def selectedTargets : Finset Q := Classical.choose (selection_exists C hP I)
noncomputable def core : Finset Q := B C hP I ∪ selectedTargets C hP I
noncomputable def extras : Finset Q := targets C hP I \ core C hP I
noncomputable def e : Nat := (targets C hP I).card - 3 * (P - 1)
noncomputable def readStates : Finset Q := (rows C hP I).image Prod.fst

private theorem selection_spec :
    selectedTargets C hP I ⊆ G C hP I \ B C hP I ∧
      (selectedTargets C hP I).card = s C hP I := Classical.choose_spec (selection_exists C hP I)

private theorem selected_resolving {q : Q} (hq : q ∈ selectedTargets C hP I) :
    ∃ z ∈ resolvingRows C hP I, target C hP I z = q := by
  have hh := Finset.mem_sdiff.mp ((selection_spec C hP I).1 hq)
  obtain ⟨z,hz,ht⟩ := Finset.mem_image.mp hh.1
  refine ⟨z,Finset.mem_sdiff.mpr ⟨hz,?_⟩,ht⟩
  intro hp
  obtain ⟨n,hn,hr⟩ := Finset.mem_image.mp hp
  have hs : (children C hP I n).Nonempty := Finset.card_pos.mp (by
    have := (Finset.mem_filter.mp hn).2; omega)
  apply hh.2
  exact Finset.mem_image.mpr ⟨n,hn,by rw [← ht,← hr]; exact (target_history C hP I n hs).1.symm⟩

noncomputable def selectedRow (q : Q) : Slot (Q := Q) :=
  if hq : q ∈ selectedTargets C hP I then Classical.choose (selected_resolving C hP I hq)
  else row C hP I (root C hP I 0)

private theorem selected_row_spec {q : Q} (hq : q ∈ selectedTargets C hP I) :
    selectedRow C hP I q ∈ resolvingRows C hP I ∧ target C hP I (selectedRow C hP I q) = q := by
  simp only [selectedRow,dif_pos hq]
  exact Classical.choose_spec (selected_resolving C hP I hq)

private theorem resolving_unary {n : Node C hP I} (hn : row C hP I n ∈ resolvingRows C hP I) :
    (children C hP I n).card = 1 := by
  have hh := Finset.mem_sdiff.mp hn
  have htwo := (Finset.mem_filter.mp hh.1).2
  have hb := branching C hP I n
  have hn0 : (children C hP I n).card ≠ 0 := by
    intro h0
    have hl : IsLeaf C hP I n := by
      intro m hm
      have hh : m ∈ children C hP I n := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hm⟩
      rw [Finset.card_eq_zero.mp h0] at hh
      exact Finset.notMem_empty _ hh
    have hz := (outgoing_zero C hP I n).2 hl
    omega
  have hn2 : (children C hP I n).card ≠ 2 := by
    intro h2
    exact hh.2 (Finset.mem_image.mpr ⟨n,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h2⟩,rfl⟩)
  omega

private theorem core_card : (core C hP I).card = 3 * (P - 1) := by
  have hd : Disjoint (B C hP I) (selectedTargets C hP I) := by
    apply Finset.disjoint_left.mpr
    intro q hB hD
    exact (Finset.mem_sdiff.mp ((selection_spec C hP I).1 hD)).2 hB
  have hs := fiber_surplus (binaries C hP I) (nextTarget C hP I)
  change s C hP I = (binaries C hP I).card - (B C hP I).card at hs
  have hn : (binaries C hP I).card = 3 * (P - 1) := binary_count C hP I
  have hb := Finset.card_image_le (s := binaries C hP I) (f := nextTarget C hP I)
  change (B C hP I).card ≤ (binaries C hP I).card at hb
  rw [core,Finset.card_union_of_disjoint hd,(selection_spec C hP I).2]
  omega

private theorem core_subset : core C hP I ⊆ targets C hP I := by
  apply Finset.union_subset
  · exact fun q hq => G_subset_targets C hP I (B_subset_G C hP I hq)
  · intro q hq
    exact G_subset_targets C hP I (Finset.mem_sdiff.mp ((selection_spec C hP I).1 hq)).1

private theorem first_not_target : prefixState C hP ell ∉ targets C hP I := by
  intro hh
  obtain ⟨z,hz,hq⟩ := Finset.mem_image.mp hh
  obtain ⟨n,hn,hr⟩ := Finset.mem_image.mp hz
  exact nonroot_control C hP I n (Finset.mem_filter.mp hn).2 ((congrArg Prod.fst hr).trans hq)

private theorem read_states_partition :
    readStates C hP I = insert (prefixState C hP ell) (targets C hP I) := by
  rw [readStates,rows_partition,Finset.image_union]
  have hr : (rootRows C hP I).image Prod.fst = {prefixState C hP ell} := by
    ext q
    simp only [rootRows,Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_singleton]
    constructor
    · rintro ⟨z,⟨c,hc⟩,hz⟩
      subst z
      exact hz.symm.trans (root_control C hP I c)
    · intro hq
      subst q
      exact ⟨row C hP I (root C hP I 0),⟨0,rfl⟩,root_control C hP I 0⟩
  rw [hr,Finset.singleton_union]
  rfl

/-- Core and extras are selected from the same actual controller, without any
J/s/Xi restriction or supplied forest, count, injection, or score function. -/
theorem structural_core :
    (B C hP I).card = 3 * (P - 1) - s C hP I ∧
    (core C hP I).card = 3 * (P - 1) ∧
    (extras C hP I).card = e C hP I ∧
    (readStates C hP I).card = 3 * (P - 1) + 1 + e C hP I ∧
    (∀ q ∈ selectedTargets C hP I,
      selectedRow C hP I q ∈ resolvingRows C hP I ∧ target C hP I (selectedRow C hP I q) = q) ∧
    (∀ n : Node C hP I, row C hP I n ∈ resolvingRows C hP I → (children C hP I n).card = 1) := by
  have hc := core_card C hP I
  have ht : 3 * (P - 1) ≤ (targets C hP I).card := by
    exact (G_card C hP I).trans (Finset.card_le_card (G_subset_targets C hP I))
  refine ⟨B_card C hP I,hc,?_,?_,fun q hq => selected_row_spec C hP I hq,
    fun n hn => resolving_unary C hP I hn⟩
  · rw [extras,Finset.card_sdiff_of_subset (core_subset C hP I),hc]; rfl
  · rw [read_states_partition,Finset.card_insert_of_notMem (first_not_target C hP I)]
    unfold e; omega

private theorem read_state_mem (q : Q) : q ∈ readStates C hP I ↔
    IsRead C q ∧ ∃ x t, t < I.length x ∧ (C.run hP (x,C.initial) t).2 = q := by
  constructor
  · intro hq
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨n,_,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨row,hr,_⟩ := history_row_execution C hP I n
    obtain ⟨_,x,ht,hx⟩ := history_time_bounds C hP I n
    exact ⟨⟨row,hr⟩,x,time C hP I n,ht,congrArg Prod.snd (history_configuration C hP I n x hx)⟩
  · rintro ⟨hr,x,t,ht,hq⟩
    have hm : t ∈ readTimes C hP I x :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ht,by rwa [hq]⟩
    let i := ((readTimes C hP I x).orderIsoOfFin rfl).symm ⟨t,hm⟩
    have hi : readTime C hP I x i = t :=
      congrArg Subtype.val ((readTimes C hP I x).orderIsoOfFin rfl |>.apply_symm_apply ⟨t,hm⟩)
    have he := congrArg Prod.snd (event_reconstruction C hP I ⟨x,i⟩).1
    rw [hi,hq] at he
    exact Finset.mem_image.mpr ⟨row C hP I (event C hP I ⟨x,i⟩),
      Finset.mem_image.mpr ⟨event C hP I ⟨x,i⟩,Finset.mem_univ _,rfl⟩,he.symm⟩

noncomputable def readStateEquiv : {q : Q // q ∈ readStates C hP I} ≃ ActualRead C hP I where
  toFun q := ⟨q.val,(read_state_mem C hP I q.val).1 q.property⟩
  invFun q := ⟨q.val,(read_state_mem C hP I q.val).2 q.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def targetRead (q : Q) (hq : q ∈ targets C hP I) : NonrootRead C hP I :=
  ⟨⟨q,(read_state_mem C hP I q).1 (by
    rw [read_states_partition]; exact Finset.mem_insert_of_mem hq)⟩,
    fun he => first_not_target C hP I (he ▸ hq)⟩

noncomputable def tail (q : Q) : Nat :=
  if hq : q ∈ targets C hP I then actualL C hP I (targetRead C hP I q hq) else 1

omit [DecidableEq Q] in
private theorem parent_arrival {n p : Node C hP I} (hp : parent C hP I n = some p) :
    Nonempty (Arrival C hP I (nextTarget C hP I p) (delay C hP I p)) := by
  obtain ⟨_,x,ht,hx⟩ := history_time_bounds C hP I n
  have hxp := support_parent C hP I hp hx
  obtain ⟨_,i,hi⟩ := Finset.mem_filter.mp hxp
  have hpost : (C.run hP (x,C.initial) (time C hP I p + 1)).2 = postControl C hP I p := by
    have he := post_event_control C hP I ⟨x,i⟩
    change (C.run hP (x,C.initial) (readTime C hP I x i + 1)).2 =
      postControl C hP I (event C hP I ⟨x,i⟩) at he
    rw [← (actual_history_data C hP I).event_time ⟨x,i⟩,hi] at he
    exact he
  have hd := child_delay_target C hP I hp
  have ha := child_arrival C hP I hp
  have htime : time C hP I p + 1 + delay C hP I p = time C hP I n := by omega
  obtain ⟨r,hr,_⟩ := history_row_execution C hP I p
  refine ⟨{
    input := x
    time := StationaryReadHistory.time C hP I p
    positive := hd.1
    source_read := ?_
    within := ?_
    waits := ?_
    endpoint := ?_ }⟩
  · rw [history_configuration C hP I p x hxp]; exact ⟨r,hr⟩
  · rwa [htime]
  · rw [hpost]
    rw [← hd.2.1,← hd.2.2.1]
    exact ha.2.1
  · rw [htime,history_configuration C hP I n x hx]
    exact hd.2.2.1

private theorem history_target {n : Node C hP I} (hn : (children C hP I n).Nonempty) :
    nextTarget C hP I n ∈ targets C hP I := by
  obtain ⟨m,hm⟩ := hn
  have hp := (Finset.mem_filter.mp hm).2
  have he := (mem_edges C hP I _ _).2 ⟨m,n,hp,rfl,rfl⟩
  exact Finset.mem_image.mpr ⟨row C hP I m,(edge_endpoints C hP I he).2,
    (child_delay_target C hP I hp).2.2.1⟩

private theorem literal_le_tail (n : Node C hP I) (hn : (children C hP I n).Nonempty) :
    0 < delay C hP I n ∧ delay C hP I n ≤ tail C hP I (nextTarget C hP I n) := by
  have hq := history_target C hP I hn
  obtain ⟨m,hm⟩ := hn
  have hp := (Finset.mem_filter.mp hm).2
  refine ⟨(child_delay_target C hP I hp).1,?_⟩
  rw [tail,dif_pos hq,actualL]
  exact Finset.le_max' _ _ ((mem_arrival_lengths C hP I _ _).2 (parent_arrival C hP I hp))

noncomputable def positiveRepresentative (n : Node C hP I) : Nat := 1 + (delay C hP I n - 1) % P

omit [DecidableEq Q] in
private theorem representative_bounds (n : Node C hP I) (hn : (children C hP I n).Nonempty) :
    1 ≤ positiveRepresentative C hP I n ∧ positiveRepresentative C hP I n ≤ delay C hP I n := by
  obtain ⟨m,hm⟩ := hn
  have hd := (child_delay_target C hP I (Finset.mem_filter.mp hm).2).1
  have hm := Nat.mod_le (delay C hP I n - 1) P
  unfold positiveRepresentative; omega

noncomputable def binaryBaseline (q : Q) : Nat :=
  ((binaries C hP I).filter (fun n => nextTarget C hP I n = q)).sup (positiveRepresentative C hP I)

noncomputable def baseline (q : Q) : Nat :=
  if q ∈ B C hP I then binaryBaseline C hP I q
  else if q ∈ selectedTargets C hP I then literal C hP I (selectedRow C hP I q) else 1

private theorem selected_literal {q : Q} (hq : q ∈ selectedTargets C hP I) :
    1 ≤ literal C hP I (selectedRow C hP I q) ∧
    literal C hP I (selectedRow C hP I q) ≤ tail C hP I q := by
  have hs := selected_row_spec C hP I hq
  have hz := (Finset.mem_sdiff.mp hs.1).1
  have hr := representative_row C hP I (Finset.mem_filter.mp hz).1
  have hu := resolving_unary C hP I (by rw [hr]; exact hs.1)
  have hn : (children C hP I (representative C hP I (selectedRow C hP I q))).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hb := literal_le_tail C hP I _ hn
  change 0 < literal C hP I (selectedRow C hP I q) ∧
    literal C hP I (selectedRow C hP I q) ≤ tail C hP I (target C hP I (selectedRow C hP I q)) at hb
  rw [hs.2] at hb
  exact ⟨hb.1,hb.2⟩

/-- Binary core baselines use the maximum of all binary-parent positive
representatives; resolving cores use the selected row's literal wait. Extras
have baseline one. Each baseline is bounded by the same actual longest tail. -/
theorem baseline_bounds (q : Q) (hq : q ∈ targets C hP I) :
    1 ≤ baseline C hP I q ∧ baseline C hP I q ≤ tail C hP I q ∧
    (q ∈ extras C hP I → baseline C hP I q = 1) := by
  have ht : 1 ≤ tail C hP I q := by
    rw [tail,dif_pos hq]
    exact (longestArrival C hP I (targetRead C hP I q hq)).positive
  by_cases hB : q ∈ B C hP I
  · have hb : 1 ≤ binaryBaseline C hP I q := by
      obtain ⟨n,hn,htarget⟩ := Finset.mem_image.mp hB
      have hs : (children C hP I n).Nonempty := Finset.card_pos.mp (by
        have := (Finset.mem_filter.mp hn).2; omega)
      exact (representative_bounds C hP I n hs).1.trans
        (Finset.le_sup (f := positiveRepresentative C hP I) (Finset.mem_filter.mpr ⟨hn,htarget⟩))
    have hl : binaryBaseline C hP I q ≤ tail C hP I q := by
      apply Finset.sup_le
      intro n hn
      have hs : (children C hP I n).Nonempty := Finset.card_pos.mp (by
        have := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2; omega)
      have hb := (representative_bounds C hP I n hs).2.trans (literal_le_tail C hP I n hs).2
      rwa [(Finset.mem_filter.mp hn).2] at hb
    refine ⟨by simpa [baseline,hB] using hb,by simpa [baseline,hB] using hl,?_⟩
    intro he
    exact False.elim ((Finset.mem_sdiff.mp he).2 (Finset.mem_union_left _ hB))
  · by_cases hD : q ∈ selectedTargets C hP I
    · have hb := selected_literal C hP I hD
      refine ⟨by simpa [baseline,hB,hD] using hb.1,by simpa [baseline,hB,hD] using hb.2,?_⟩
      intro he
      exact False.elim ((Finset.mem_sdiff.mp he).2 (Finset.mem_union_right _ hD))
    · simp [baseline,hB,hD,ht]

def BackgroundParent (n : Node C hP I) : Prop :=
  n ∈ binaries C hP I ∨ ∃ q ∈ selectedTargets C hP I, row C hP I n = selectedRow C hP I q

/-- This is a finite set of full indexed histories, not a set of row/weight
pairs: two histories with the same row and literal wait remain two members. -/
noncomputable def backgroundChildren (q : Q) : Finset (Node C hP I) :=
  Finset.univ.filter (fun n => readControl C hP I n = q ∧
    ∃ p, parent C hP I n = some p ∧ BackgroundParent C hP I p)
noncomputable def backgroundDigits (q : Q) : Finset (Fin 3) :=
  (backgroundChildren C hP I q).image (color C hP I)
noncomputable def k (q : Q) : Nat := 3 - (backgroundDigits C hP I q).card

private theorem background_target {n p : Node C hP I}
    (hp : parent C hP I n = some p) (hb : BackgroundParent C hP I p) :
    readControl C hP I n ∈ core C hP I := by
  have hs : (children C hP I p).Nonempty := ⟨n,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩⟩
  rw [(child_delay_target C hP I hp).2.2.1]
  rcases hb with hb | ⟨q,hq,hr⟩
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p,hb,rfl⟩)
  · have ht := (target_history C hP I p hs).1
    rw [hr,(selected_row_spec C hP I hq).2] at ht
    exact Finset.mem_union_right _ (ht ▸ hq)

private theorem binary_background {q : Q} (hq : q ∈ B C hP I) :
    2 ≤ (backgroundDigits C hP I q).card := by
  obtain ⟨p,hp,ht⟩ := Finset.mem_image.mp hq
  have hc : (children C hP I p).card = 2 := (Finset.mem_filter.mp hp).2
  have hi : Set.InjOn (color C hP I) (children C hP I p) := by
    intro n hn m hm he
    exact child_digit_injective C hP I (Finset.mem_filter.mp hn).2 (Finset.mem_filter.mp hm).2 he
  have sub : (children C hP I p).image (color C hP I) ⊆ backgroundDigits C hP I q := by
    intro c he
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp he
    have hn' := (Finset.mem_filter.mp hn).2
    exact Finset.mem_image.mpr ⟨n,Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,(child_delay_target C hP I hn').2.2.1.trans ht,p,hn',Or.inl hp⟩,rfl⟩
  have hs := Finset.card_le_card sub
  rwa [Finset.card_image_of_injOn hi,hc] at hs

private theorem resolving_background {q : Q} (hq : q ∈ selectedTargets C hP I) :
    2 ≤ (backgroundDigits C hP I q).card := by
  let z := selectedRow C hP I q
  have hz := selected_row_spec C hP I hq
  have ht : (outgoing C hP I z).card = 2 :=
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp hz.1).1).2
  have hi : Set.InjOn (fun a : Slot (Q := Q) × Slot (Q := Q) => a.2.2) (outgoing C hP I z) := by
    intro a ha b hb he
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    apply Prod.ext (ha'.2.trans hb'.2.symm)
    apply Prod.ext
    · have hat := edge_target C hP I ha'.1
      have hbt := edge_target C hP I hb'.1
      rw [ha'.2] at hat
      rw [hb'.2] at hbt
      exact hat.trans hbt.symm
    · exact he
  have sub : (outgoing C hP I z).image (fun a => a.2.2) ⊆ backgroundDigits C hP I q := by
    intro c hc
    obtain ⟨edge,he,rfl⟩ := Finset.mem_image.mp hc
    have hh := Finset.mem_filter.mp he
    obtain ⟨n,p,hp,hr,hn⟩ := (mem_edges C hP I edge.1 edge.2).1 hh.1
    have hpz : row C hP I p = z := hr.trans hh.2
    have htarget := edge_target C hP I hh.1
    rw [hh.2,hz.2] at htarget
    exact Finset.mem_image.mpr ⟨n,Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,(congrArg Prod.fst hn).trans htarget,p,hp,Or.inr ⟨q,hq,hpz⟩⟩,
      congrArg Prod.snd hn⟩
  have hs := Finset.card_le_card sub
  rwa [Finset.card_image_of_injOn hi,ht] at hs

/-- Every core occupies at least two background digits. Extras have no
background histories. Full histories, and hence their indexed events, retain
their original identity regardless of equal row or weight values. -/
theorem background_structure :
    (∀ q ∈ core C hP I, 2 ≤ (backgroundDigits C hP I q).card ∧ k C hP I q ≤ 1) ∧
    (∀ q ∈ extras C hP I, backgroundChildren C hP I q = ∅) ∧
    (∀ q n m, n ∈ backgroundChildren C hP I q → m ∈ backgroundChildren C hP I q →
      n ≠ m → Disjoint (indexedSupport C hP I n) (indexedSupport C hP I m)) := by
  refine ⟨?_,?_,?_⟩
  · intro q hq
    have hb : 2 ≤ (backgroundDigits C hP I q).card := by
      rcases Finset.mem_union.mp hq with hB | hD
      · exact binary_background C hP I hB
      · exact resolving_background C hP I hD
    exact ⟨hb,by unfold k; omega⟩
  · intro q hq
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro n hn
    have hh := (Finset.mem_filter.mp hn).2
    obtain ⟨p,hp,hb⟩ := hh.2
    have hc := background_target C hP I hp hb
    rw [hh.1] at hc
    exact (Finset.mem_sdiff.mp hq).2 hc
  · intro q n m _ _ hne
    exact (actual_history_data C hP I).indexed_disjoint n m hne

/-- Distinct selected targets have distinct actual resolving source rows; s is
therefore bounded by the derived number J of pure resolving rows. -/
theorem resolving_selection : s C hP I ≤ J C hP I ∧
    Set.InjOn (selectedRow C hP I) (selectedTargets C hP I) := by
  have hi : Set.InjOn (selectedRow C hP I) (selectedTargets C hP I) := by
    intro q hq q' hq' he
    have ht := (selected_row_spec C hP I hq).2
    rw [he,(selected_row_spec C hP I hq').2] at ht
    exact ht.symm
  refine ⟨?_,hi⟩
  have sub : (selectedTargets C hP I).image (selectedRow C hP I) ⊆ resolvingRows C hP I := by
    intro z hz
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz
    exact (selected_row_spec C hP I hq).1
  have hc := Finset.card_le_card sub
  rw [Finset.card_image_of_injOn hi,(selection_spec C hP I).2,(two_outgoing_count C hP I).2.2] at hc
  exact hc

omit [DecidableEq Q] in
private theorem positive_rep_binary (n : Node C hP I) (hn : (children C hP I n).card = 2) :
    1 ≤ positiveRepresentative C hP I n ∧ positiveRepresentative C hP I n < P := by
  have hc := binary_crosses_cut C hP I n hn
  have hu := (physicalForest C hP I).interval_bounds n
  change lower C hP I n < upper C hP I n ∧ upper C hP I n ≤ P at hu
  have hmod : delay C hP I n % P ≠ 0 := by
    intro he
    simp only [modularCut,he,Nat.sub_zero] at hc
    omega
  have hb : (children C hP I n).Nonempty := Finset.card_pos.mp (by omega)
  have hr := representative_bounds C hP I n hb
  have hlt := Nat.mod_lt (delay C hP I n - 1) (by omega : 0 < P)
  have he : positiveRepresentative C hP I n % P = delay C hP I n % P := by
    have hd := hr.2
    have hpos : 0 < delay C hP I n := by omega
    unfold positiveRepresentative
    calc
      (1 + (delay C hP I n - 1) % P) % P = (delay C hP I n - 1 + 1) % P := by
        simp only [Nat.add_mod,Nat.mod_mod]; rw [Nat.add_comm]
      _ = delay C hP I n % P := by congr 1; omega
  have hne : positiveRepresentative C hP I n ≠ P := by
    intro hh; rw [hh,Nat.mod_self] at he; exact hmod he.symm
  exact ⟨hr.1,by unfold positiveRepresentative at hne ⊢; omega⟩

private theorem actual_read_count [Fintype Q] :
    Fintype.card (ActualRead C hP I) = 3 * (P - 1) + 1 + e C hP I := by
  calc
    _ = Fintype.card {q : Q // q ∈ readStates C hP I} :=
      (Fintype.card_congr (readStateEquiv C hP I)).symm
    _ = (readStates C hP I).card := Fintype.card_coe _
    _ = _ := (structural_core C hP I).2.2.2.1


end D5.S3.ObserverMemory.Algorithms.StationaryHistorySlotGraph
