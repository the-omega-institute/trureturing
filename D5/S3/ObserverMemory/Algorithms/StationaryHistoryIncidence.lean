/- GID: D5/S3/ObserverMemory/Algorithms/StationaryHistoryIncidence
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/StationaryHistoryIncidence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual original controller histories and their incidence laws. -/

import D5.S3.ObserverMemory.Algorithms.StationaryReadHistory
import D5.S3.ObserverMemory.Algorithms.FixedForestSlotGraph

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
open private fiber_surplus raw_rows_image from
  D5.S3.ObserverMemory.Algorithms.FixedForestSlotGraph
attribute [local instance] Classical.propDecidable

universe u
variable {P ell h : Nat} {Q : Type u} (C : Controller P Q) (hP : 1 < P)
  (I : Initialized C hP ell h) [NeZero (3 * P)] [DecidableEq Q]

abbrev Node := History C hP I
abbrev Slot := Q × Fin 3

def row (n : Node C hP I) : Slot (Q := Q) :=
  (readControl C hP I n, color C hP I n)

noncomputable def rows : Finset (Slot (Q := Q)) := Finset.univ.image (row C hP I)
noncomputable def nonroots : Finset (Node C hP I) :=
  FixedForestSlotGraph.rawNonroots (physicalForest C hP I)
noncomputable def nonrootRows : Finset (Slot (Q := Q)) :=
  FixedForestSlotGraph.rawRows (physicalForest C hP I) (row C hP I)
noncomputable def edges : Finset (Slot (Q := Q) × Slot (Q := Q)) :=
  FixedForestSlotGraph.rawEdges (physicalForest C hP I) (row C hP I)
noncomputable def J : Nat :=
  FixedForestSlotGraph.rawJ (physicalForest C hP I) (row C hP I)
noncomputable def Xi : Nat :=
  FixedForestSlotGraph.rawXi (physicalForest C hP I) (row C hP I)
noncomputable def outgoing (z : Slot (Q := Q)) := (edges C hP I).filter (fun a => a.1 = z)
noncomputable def incoming (z : Slot (Q := Q)) := (edges C hP I).filter (fun a => a.2 = z)
noncomputable def rootRows := Finset.univ.image (fun c : Fin 3 => row C hP I (root C hP I c))
noncomputable def leafRows := (Finset.univ.filter (IsLeaf C hP I)).image (row C hP I)
noncomputable def binaries :=
  Finset.univ.filter (fun n : Node C hP I => (children C hP I n).card = 2)
noncomputable def productionRows := (binaries C hP I).image (row C hP I)
noncomputable def twoRows := (rows C hP I).filter (fun z => (outgoing C hP I z).card = 2)
noncomputable def resolvingRows := twoRows C hP I \ productionRows C hP I

private theorem mem_edges (a b : Slot (Q := Q)) :
    (a,b) ∈ edges C hP I ↔ ∃ n p : Node C hP I,
      parent C hP I n = some p ∧ row C hP I p = a ∧ row C hP I n = b := by
  simp only [edges, FixedForestSlotGraph.rawEdges, Finset.mem_image]
  constructor
  · rintro ⟨n,hn,he⟩
    have hp := (Finset.mem_filter.mp hn).2
    change parent C hP I n ≠ none at hp
    cases hh : parent C hP I n with
    | none => exact False.elim (hp hh)
    | some p =>
      have he' : (row C hP I p,row C hP I n) = (a,b) := by
        simpa [FixedForestSlotGraph.rawEdge,physicalForest,hh] using he
      exact ⟨n,p,hh,congrArg Prod.fst he',congrArg Prod.snd he'⟩
  · rintro ⟨n,p,hp,ha,hb⟩
    refine ⟨n,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
    · change parent C hP I n ≠ none; rw [hp]; simp
    · simp [FixedForestSlotGraph.rawEdge,physicalForest,hp,ha,hb]

omit [DecidableEq Q] in
private theorem history_time_bounds (n : Node C hP I) :
    ell ≤ time C hP I n ∧ ∃ x, time C hP I n < I.length x ∧
      x ∈ support C hP I n := by
  obtain ⟨e,he⟩ := event_surjective C hP I n
  have hx : e.1 ∈ support C hP I n := by
    simp only [support,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨e.2,he⟩
  have ht : time C hP I n < I.length e.1 := by rw [← he,event_time]; exact event_time_bound C hP I e
  refine ⟨?_,e.1,ht,hx⟩
  by_contra hh
  obtain ⟨w,hw⟩ := (I.shape e.1).prefix_wait (time C hP I n) (by omega)
  obtain ⟨r,hr,_⟩ := history_row_execution C hP I n
  rw [history_configuration C hP I n e.1 hx] at hw
  rw [hr] at hw
  cases hw

omit [DecidableEq Q] in
private theorem root_control (c : Fin 3) :
    readControl C hP I (root C hP I c) = prefixState C hP ell := by
  obtain ⟨x,hx⟩ := (actual_history_data C hP I).support_nonempty (root C hP I c)
  have ht : time C hP I (root C hP I c) = ell := by
    rw [history_time_decomposition]
    simp only [(root_data C hP I c).2.1,(root_data C hP I c).2.2,Nat.add_zero]
  have hr := history_configuration C hP I (root C hP I c) x hx
  rw [ht,initialized_prefix C hP I x le_rfl] at hr
  exact (congrArg Prod.snd hr).symm

omit [DecidableEq Q] in
private theorem nonroot_control (n : Node C hP I) (hn : parent C hP I n ≠ none) :
    readControl C hP I n ≠ prefixState C hP ell := by
  cases hp : parent C hP I n with
  | none => exact False.elim (hn hp)
  | some p =>
    obtain ⟨_,x,ht,hx⟩ := history_time_bounds C hP I n
    have hpt := (history_time_bounds C hP I p).1
    have hg := (child_arrival C hP I hp).1
    have hh := prefix_first_read_no_return C hP I x le_rfl
      (by omega : ell < time C hP I n) (Nat.le_of_lt ht)
    rwa [history_configuration C hP I n x hx] at hh

private theorem root_rows_card : (rootRows C hP I).card = 3 := by
  rw [rootRows,Finset.card_image_of_injective]
  · simp
  · intro a b he
    have hc := congrArg Prod.snd he
    simpa only [row,(root_data C hP I a).1,(root_data C hP I b).1] using hc

private theorem rows_partition : rows C hP I = rootRows C hP I ∪ nonrootRows C hP I := by
  ext z
  simp only [rows,rootRows,nonrootRows,FixedForestSlotGraph.rawRows,
    FixedForestSlotGraph.rawNonroots,Finset.mem_union,Finset.mem_image,Finset.mem_univ,
    true_and,Finset.mem_filter]
  constructor
  · rintro ⟨n,rfl⟩
    by_cases hp : parent C hP I n = none
    · obtain ⟨c,rfl⟩ := (roots_exact C hP I n).1 hp; exact Or.inl ⟨c,rfl⟩
    · exact Or.inr ⟨n,hp,rfl⟩
  · rintro (⟨c,hc⟩ | ⟨n,_,hn⟩)
    · exact ⟨root C hP I c,hc⟩
    · exact ⟨n,hn⟩

private theorem roots_disjoint : Disjoint (rootRows C hP I) (nonrootRows C hP I) := by
  apply Finset.disjoint_left.mpr
  intro z hz hn
  obtain ⟨c,_,hc⟩ := Finset.mem_image.mp hz
  obtain ⟨n,hn,hz⟩ := Finset.mem_image.mp hn
  have hp : parent C hP I n ≠ none := (Finset.mem_filter.mp hn).2
  have hq := congrArg Prod.fst (hz.trans hc.symm)
  exact nonroot_control C hP I n hp (hq.trans (root_control C hP I c))

private theorem edge_endpoints {a b : Slot (Q := Q)} (he : (a, b) ∈ edges C hP I) :
    a ∈ rows C hP I ∧ b ∈ nonrootRows C hP I := by
  obtain ⟨n,p,hp,rfl,rfl⟩ := (mem_edges C hP I a b).1 he
  refine ⟨Finset.mem_image.mpr ⟨p,Finset.mem_univ _,rfl⟩,?_⟩
  apply Finset.mem_image.mpr
  refine ⟨n,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,rfl⟩
  change parent C hP I n ≠ none; rw [hp]; simp

/-- Every edge is a distinct actual slot pair. Its history fiber retains every
indexed full word; raw edge multiplicity counts forest edges rather than inputs. -/
theorem actual_edge_incidence :
    (∑ z ∈ nonrootRows C hP I,
      (((nonroots C hP I).filter (fun n => row C hP I n = z)).card - 1)) =
      J C hP I + Xi C hP I := by
  exact FixedForestSlotGraph.raw_history_surplus (physicalForest C hP I) (row C hP I)

private theorem outgoing_target {n : Node C hP I} {b : Slot (Q := Q)}
    (he : (row C hP I n, b) ∈ edges C hP I) : b.1 = nextTarget C hP I n := by
  obtain ⟨m,p,hp,hr,hb⟩ := (mem_edges C hP I _ _).1 he
  have hs : (children C hP I p).Nonempty := ⟨m,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩⟩
  have hco := row_delay_target C hP I hs (congrArg Prod.fst hr) (congrArg Prod.snd hr)
  exact (congrArg Prod.fst hb).symm.trans ((child_delay_target C hP I hp).2.2.1.trans hco.2)

/-- One actual row has at most two different outgoing slot edges, even when it
contains many unary full histories at different levels. Literal wraps remain. -/
theorem outgoing_degree (n : Node C hP I) : (outgoing C hP I (row C hP I n)).card ≤ 2 := by
  let a : Fin 3 := ⟨((color C hP I n).val + delay C hP I n / P) % 3,Nat.mod_lt _ (by omega)⟩
  let b : Fin 3 := ⟨((color C hP I n).val + delay C hP I n / P + 1) % 3,Nat.mod_lt _ (by omega)⟩
  let target := nextTarget C hP I n
  have sub : outgoing C hP I (row C hP I n) ⊆
      {(row C hP I n,(target,a)),(row C hP I n,(target,b))} := by
    intro edge he
    have hh := Finset.mem_filter.mp he
    obtain ⟨m,p,hp,hr,hm⟩ := (mem_edges C hP I edge.1 edge.2).1 hh.1
    have hpr : row C hP I p = row C hP I n := hr.trans hh.2
    have hs : (children C hP I p).Nonempty := ⟨m,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩⟩
    have hco := row_delay_target C hP I hs (congrArg Prod.fst hpr) (congrArg Prod.snd hpr)
    obtain ⟨x,hx⟩ := (actual_history_data C hP I).support_nonempty m
    have hxp := support_parent C hP I hp hx
    have hsc := supported_color C hP I p x hxp
    have hmc := supported_color C hP I m x hx
    have ht := digit_translate hP (x + (historyShift C hP I p : ZMod (3 * P))) (delay C hP I p)
    rw [(child_delay_target C hP I hp).2.2.2,Nat.cast_add,← add_assoc] at hmc
    rw [hsc,hmc,hco.1,show color C hP I p = color C hP I n from congrArg Prod.snd hpr] at ht
    have edgeeq : edge = (row C hP I n,edge.2) := Prod.ext hh.2 rfl
    have htarget : edge.2.1 = target := outgoing_target C hP I (by rw [← edgeeq]; exact hh.1)
    have hcolor : edge.2.2 = a ∨ edge.2.2 = b := by
      have hc : color C hP I m = edge.2.2 := congrArg Prod.snd hm
      rw [hc] at ht
      split at ht
      · exact Or.inr (Fin.ext ht)
      · exact Or.inl (Fin.ext (by simpa [a] using ht))
    rcases hcolor with ha | hb
    · exact Finset.mem_insert.mpr (Or.inl (Prod.ext hh.2 (Prod.ext htarget ha)))
    · exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_singleton.mpr (Prod.ext hh.2 (Prod.ext htarget hb))))
  exact (Finset.card_le_card sub).trans ((Finset.card_insert_le _ _).trans (by simp))

private theorem outgoing_zero (n : Node C hP I) :
    (outgoing C hP I (row C hP I n)).card = 0 ↔ IsLeaf C hP I n := by
  rw [Finset.card_eq_zero]
  constructor
  · intro hz m hp
    have he := (mem_edges C hP I _ _).2 ⟨m,n,hp,rfl,rfl⟩
    have hm : (row C hP I n,row C hP I m) ∈ outgoing C hP I (row C hP I n) :=
      Finset.mem_filter.mpr ⟨he,rfl⟩
    rw [hz] at hm; exact Finset.notMem_empty _ hm
  · intro hl
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro edge he
    obtain ⟨m,p,hp,hr,_⟩ := (mem_edges C hP I edge.1 edge.2).1 (Finset.mem_filter.mp he).1
    have hpr := hr.trans (Finset.mem_filter.mp he).2
    have hnp := terminal_row_unique C hP I hl
      (congrArg Prod.fst hpr).symm (congrArg Prod.snd hpr).symm
    subst p
    exact hl m hp

private theorem binary_outgoing (n : Node C hP I) (hn : n ∈ binaries C hP I) :
    (outgoing C hP I (row C hP I n)).card = 2 := by
  have hcard := (Finset.mem_filter.mp hn).2
  have hi : Set.InjOn (fun m => (row C hP I n,row C hP I m)) (children C hP I n) := by
    intro a ha b hb he
    exact child_digit_injective C hP I (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
      (congrArg (fun e : Slot (Q := Q) × Slot (Q := Q) => e.2.2) he)
  have sub : (children C hP I n).image (fun m => (row C hP I n,row C hP I m)) ⊆
      outgoing C hP I (row C hP I n) := by
    intro e he
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_filter.mpr
      ⟨(mem_edges C hP I _ _).2 ⟨m,n,(Finset.mem_filter.mp hm).2,rfl,rfl⟩,rfl⟩
  have hc := Finset.card_le_card sub
  rw [Finset.card_image_of_injOn hi,hcard] at hc
  exact Nat.le_antisymm (outgoing_degree C hP I n) hc

private theorem production_card : (productionRows C hP I).card = 3 * (P - 1) := by
  rw [productionRows,Finset.card_image_of_injOn]
  · exact binary_count C hP I
  · intro n hn m hm he
    exact binary_row_unique C hP I (Finset.mem_filter.mp hn).2 (Finset.mem_filter.mp hm).2
      (congrArg Prod.fst he) (congrArg Prod.snd he)

private theorem production_subset : productionRows C hP I ⊆ twoRows C hP I := by
  intro z hz
  obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hz
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_image.mpr ⟨n,Finset.mem_univ _,rfl⟩,binary_outgoing C hP I n hn⟩

private theorem leaf_rows_card : (leafRows C hP I).card = 3 * P := by
  rw [leafRows,Finset.card_image_of_injOn]
  · simpa only [Fintype.card_subtype] using (actual_history_data C hP I).leaf_count
  · intro n hn m hm he
    exact terminal_row_unique C hP I (Finset.mem_filter.mp hn).2
      (congrArg Prod.fst he) (congrArg Prod.snd he)

private theorem leaf_mem (n : Node C hP I) :
    row C hP I n ∈ leafRows C hP I ↔ IsLeaf C hP I n := by
  constructor
  · intro hn
    obtain ⟨m,hm,he⟩ := Finset.mem_image.mp hn
    have hl := (Finset.mem_filter.mp hm).2
    have eq := terminal_row_unique C hP I hl (congrArg Prod.fst he) (congrArg Prod.snd he)
    rwa [← eq]
  · intro hn
    exact Finset.mem_image.mpr ⟨n,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩,rfl⟩

private theorem leaf_subset : leafRows C hP I ⊆ rows C hP I := by
  intro z hz
  obtain ⟨n,_,rfl⟩ := Finset.mem_image.mp hz
  exact Finset.mem_image.mpr ⟨n,Finset.mem_univ _,rfl⟩

private theorem edge_count : (edges C hP I).card + 3 = (rows C hP I).card + J C hP I := by
  have img : (edges C hP I).image Prod.snd = nonrootRows C hP I :=
    raw_rows_image (physicalForest C hP I) (row C hP I)
  have hcount := fiber_surplus (edges C hP I) Prod.snd
  rw [img] at hcount
  change J C hP I = (edges C hP I).card - (nonrootRows C hP I).card at hcount
  have hle : (nonrootRows C hP I).card ≤ (edges C hP I).card := by
    rw [← img]; exact Finset.card_image_le
  have hr : (rows C hP I).card = 3 + (nonrootRows C hP I).card := by
    rw [rows_partition,Finset.card_union_of_disjoint (roots_disjoint C hP I),root_rows_card]
  omega

private theorem outgoing_sum :
    ∑ z ∈ rows C hP I, (outgoing C hP I z).card = (edges C hP I).card := by
  symm
  exact Finset.card_eq_sum_card_fiberwise (fun edge he => (edge_endpoints C hP I he).1)

private theorem degree_balance :
    (edges C hP I).card + (leafRows C hP I).card =
      (rows C hP I).card + (twoRows C hP I).card := by
  have point (z : Slot (Q := Q)) (hz : z ∈ rows C hP I) :
      (outgoing C hP I z).card + (if z ∈ leafRows C hP I then 1 else 0) =
        1 + (if z ∈ twoRows C hP I then 1 else 0) := by
    obtain ⟨n,_,rfl⟩ := Finset.mem_image.mp hz
    have hb := outgoing_degree C hP I n
    have hl := (outgoing_zero C hP I n).trans (leaf_mem C hP I n).symm
    have ht : row C hP I n ∈ twoRows C hP I ↔ (outgoing C hP I (row C hP I n)).card = 2 := by
      simp only [twoRows,Finset.mem_filter, hz,true_and]
    by_cases h0 : (outgoing C hP I (row C hP I n)).card = 0
    · rw [if_pos (hl.1 h0),if_neg (by rw [ht]; omega),h0]
    · by_cases h2 : (outgoing C hP I (row C hP I n)).card = 2
      · rw [if_neg (by rw [← hl]; exact h0),if_pos (ht.2 h2),h2]
      · rw [if_neg (by rw [← hl]; exact h0),if_neg (by rw [ht]; exact h2)]
        omega
  have hs := Finset.sum_congr rfl point
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,outgoing_sum] at hs
  have hl' : (rows C hP I).filter (fun z => z ∈ leafRows C hP I) = leafRows C hP I := by
    ext z; simp only [Finset.mem_filter]; exact ⟨And.right,fun hz => ⟨leaf_subset C hP I hz,hz⟩⟩
  have ht' : (rows C hP I).filter (fun z => z ∈ twoRows C hP I) = twoRows C hP I := by
    ext z
    simp only [Finset.mem_filter]
    exact ⟨And.right,fun hz => ⟨(Finset.mem_filter.mp hz).1,hz⟩⟩
  simpa only [Finset.sum_ite,Finset.sum_const,hl',ht',
    Nat.nsmul_eq_mul,Nat.mul_one,Nat.mul_zero,Nat.add_zero] using hs

/-- The actual distinct two-outgoing source rows number N+J. Production rows
number N, and every remaining two-outgoing row contains only unary histories. -/
theorem two_outgoing_count :
    (twoRows C hP I).card = 3 * (P - 1) + J C hP I ∧
    (productionRows C hP I).card = 3 * (P - 1) ∧
    (resolvingRows C hP I).card = J C hP I := by
  have he := edge_count C hP I
  have hd := degree_balance C hP I
  rw [leaf_rows_card] at hd
  have hp := production_card C hP I
  have hr : (resolvingRows C hP I).card =
      (twoRows C hP I).card - (productionRows C hP I).card :=
    Finset.card_sdiff_of_subset (production_subset C hP I)
  have hN : 3 * P = 3 * (P - 1) + 3 := by omega
  exact ⟨by omega,hp,by omega⟩

noncomputable def representative (z : Slot (Q := Q)) : Node C hP I :=
  if hz : ∃ n : Node C hP I, row C hP I n = z then Classical.choose hz else root C hP I 0

noncomputable def target (z : Slot (Q := Q)) : Q := nextTarget C hP I (representative C hP I z)
noncomputable def literal (z : Slot (Q := Q)) : Nat := delay C hP I (representative C hP I z)
noncomputable def targets : Finset Q := (nonrootRows C hP I).image Prod.fst
noncomputable def G : Finset Q := (twoRows C hP I).image (target C hP I)
noncomputable def B : Finset Q := (binaries C hP I).image (nextTarget C hP I)
noncomputable def binaryMultiplicity (q : Q) :=
  ((binaries C hP I).filter (fun n => nextTarget C hP I n = q)).card
noncomputable def s : Nat := ∑ q ∈ B C hP I, (binaryMultiplicity C hP I q - 1)
noncomputable def twoAt (q : Q) := (twoRows C hP I).filter (fun z => target C hP I z = q)
noncomputable def targetSlots (q : Q) := (nonrootRows C hP I).filter (fun z => z.1 = q)
noncomputable def targetEdges (q : Q) := (edges C hP I).filter (fun a => a.2.1 = q)
noncomputable def targetJ (q : Q) := ∑ z ∈ targetSlots C hP I q, ((incoming C hP I z).card - 1)

private theorem representative_row {z : Slot (Q := Q)} (hz : z ∈ rows C hP I) :
    row C hP I (representative C hP I z) = z := by
  have hs : ∃ n : Node C hP I, row C hP I n = z := by
    obtain ⟨n,_,hn⟩ := Finset.mem_image.mp hz; exact ⟨n,hn⟩
  simp only [representative,dif_pos hs]
  exact Classical.choose_spec hs

private theorem target_history (n : Node C hP I) (hn : (children C hP I n).Nonempty) :
    target C hP I (row C hP I n) = nextTarget C hP I n ∧
      literal C hP I (row C hP I n) = delay C hP I n := by
  have hr := representative_row C hP I (Finset.mem_image.mpr ⟨n,Finset.mem_univ _,rfl⟩)
  have hc := row_delay_target C hP I hn (congrArg Prod.fst hr).symm (congrArg Prod.snd hr).symm
  exact ⟨hc.2.symm,hc.1.symm⟩

private theorem edge_target {a : Slot (Q := Q) × Slot (Q := Q)} (ha : a ∈ edges C hP I) :
    a.2.1 = target C hP I a.1 := by
  have hs := (edge_endpoints C hP I ha).1
  have hr := representative_row C hP I hs
  apply outgoing_target C hP I (n := representative C hP I a.1)
  simpa only [hr,Prod.mk.eta] using ha

private theorem B_subset_G : B C hP I ⊆ G C hP I := by
  intro q hq
  obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hq
  have hs : (children C hP I n).Nonempty := Finset.card_pos.mp (by
    have := (Finset.mem_filter.mp hn).2; omega)
  exact Finset.mem_image.mpr ⟨row C hP I n,
    production_subset C hP I (Finset.mem_image.mpr ⟨n,hn,rfl⟩),(target_history C hP I n hs).1⟩

private theorem G_subset_targets : G C hP I ⊆ targets C hP I := by
  intro q hq
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hq
  have hd := (Finset.mem_filter.mp hz).2
  obtain ⟨edge,he⟩ := Finset.card_pos.mp (show 0 < (outgoing C hP I z).card by omega)
  have hh := Finset.mem_filter.mp he
  have ht := edge_target C hP I hh.1
  rw [hh.2] at ht
  exact Finset.mem_image.mpr ⟨edge.2,(edge_endpoints C hP I hh.1).2,ht⟩

private theorem incoming_positive {z : Slot (Q := Q)} (hz : z ∈ nonrootRows C hP I) :
    1 ≤ (incoming C hP I z).card := by
  obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hz
  have hn : parent C hP I n ≠ none := (Finset.mem_filter.mp hn).2
  cases hp : parent C hP I n with
  | none => exact False.elim (hn hp)
  | some p =>
    apply Finset.card_pos.mpr
    exact ⟨(row C hP I p,row C hP I n),
      Finset.mem_filter.mpr ⟨(mem_edges C hP I _ _).2 ⟨n,p,hp,rfl,rfl⟩,rfl⟩⟩

private theorem target_slots_card (q : Q) : (targetSlots C hP I q).card ≤ 3 := by
  have hi : Set.InjOn (fun z : Slot (Q := Q) => z.2) (targetSlots C hP I q) := by
    intro a ha b hb he
    apply Prod.ext
    · exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
    · exact he
  rw [← Finset.card_image_of_injOn hi]
  exact (Finset.card_le_card (Finset.subset_univ _)).trans (by simp)

private theorem target_indegree_balance (q : Q) :
    (targetEdges C hP I q).card = (targetSlots C hP I q).card + targetJ C hP I q := by
  have hs : ∑ z ∈ targetSlots C hP I q, (incoming C hP I z).card =
      (targetEdges C hP I q).card := by
    have hc := Finset.card_eq_sum_card_fiberwise
      (s := targetEdges C hP I q) (t := targetSlots C hP I q) (f := Prod.snd)
      (by
        intro a ha
        exact Finset.mem_filter.mpr
          ⟨(edge_endpoints C hP I (Finset.mem_filter.mp ha).1).2,(Finset.mem_filter.mp ha).2⟩)
    rw [hc]
    apply Finset.sum_congr rfl
    intro z hz
    congr 1
    ext a
    simp only [targetEdges,incoming,Finset.mem_filter]
    constructor
    · rintro ⟨ha,he⟩
      exact ⟨⟨ha,by rw [he]; exact (Finset.mem_filter.mp hz).2⟩,he⟩
    · rintro ⟨⟨ha,_⟩,he⟩; exact ⟨ha,he⟩
  have hj : targetJ C hP I q = (targetEdges C hP I q).card - (targetSlots C hP I q).card := by
    unfold targetJ
    rw [Finset.sum_tsub_distrib]
    · rw [hs]; simp
    · intro z hz
      exact incoming_positive C hP I (Finset.mem_filter.mp hz).1
  have hl : (targetSlots C hP I q).card ≤ (targetEdges C hP I q).card := by
    rw [← hs,Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum (fun z hz => incoming_positive C hP I (Finset.mem_filter.mp hz).1)
  omega

private theorem two_target_edges (q : Q) :
    2 * (twoAt C hP I q).card ≤ (targetEdges C hP I q).card := by
  let a := (edges C hP I).filter (fun edge => edge.1 ∈ twoAt C hP I q)
  have hc : a.card = 2 * (twoAt C hP I q).card := by
    rw [Finset.card_eq_sum_card_fiberwise
      (f := Prod.fst) (t := twoAt C hP I q) (by
        intro edge he; exact (Finset.mem_filter.mp he).2)]
    have hf (z : Slot (Q := Q)) (hz : z ∈ twoAt C hP I q) :
        (a.filter (fun edge => edge.1 = z)).card = 2 := by
      have he : a.filter (fun edge => edge.1 = z) = outgoing C hP I z := by
        ext edge
        simp only [a,outgoing,Finset.mem_filter]
        exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,by rw [h.2]; exact hz⟩,h.2⟩⟩
      rw [he]
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2
    rw [Finset.sum_congr rfl hf]
    simp [Nat.mul_comm]
  have sub : a ⊆ targetEdges C hP I q := by
    intro edge he
    have hh := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨hh.1,
      (edge_target C hP I hh.1).trans (Finset.mem_filter.mp hh.2).2⟩
  rw [← hc]
  exact Finset.card_le_card sub

/-- Distinct two-outgoing rows entering q supply twice as many distinct edges.
Three physical digit slots bound their total indegree surplus from below. -/
theorem target_incidence (q : Q) :
    2 * (twoAt C hP I q).card ≤ 3 + targetJ C hP I q ∧
    (twoAt C hP I q).card - 1 ≤ targetJ C hP I q := by
  have hc := two_target_edges C hP I q
  have hb := target_indegree_balance C hP I q
  have hs := target_slots_card C hP I q
  exact ⟨by omega,by omega⟩

private theorem J_total : ∑ q ∈ targets C hP I, targetJ C hP I q = J C hP I := by
  exact Finset.sum_fiberwise_of_maps_to
    (fun z hz => Finset.mem_image_of_mem Prod.fst hz)
    (fun z => (incoming C hP I z).card - 1)

private theorem G_card : 3 * (P - 1) ≤ (G C hP I).card := by
  have hf := fiber_surplus (twoRows C hP I) (target C hP I)
  change (∑ q ∈ G C hP I, ((twoAt C hP I q).card - 1)) =
    (twoRows C hP I).card - (G C hP I).card at hf
  have hg := Finset.card_image_le (s := twoRows C hP I) (f := target C hP I)
  change (G C hP I).card ≤ (twoRows C hP I).card at hg
  have hs : (∑ q ∈ G C hP I, ((twoAt C hP I q).card - 1)) ≤ J C hP I := by
    calc
      _ ≤ ∑ q ∈ G C hP I, targetJ C hP I q :=
        Finset.sum_le_sum (fun q _ => (target_incidence C hP I q).2)
      _ ≤ ∑ q ∈ targets C hP I, targetJ C hP I q :=
        Finset.sum_le_sum_of_subset_of_nonneg (G_subset_targets C hP I) (by intros; omega)
      _ = J C hP I := J_total C hP I
  have ht := (two_outgoing_count C hP I).1
  omega


end D5.S3.ObserverMemory.Algorithms.StationaryHistorySlotGraph
