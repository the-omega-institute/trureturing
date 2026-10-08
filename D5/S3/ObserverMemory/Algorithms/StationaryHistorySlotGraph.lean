/- GID: D5/S3/ObserverMemory/Algorithms/StationaryHistorySlotGraph
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/StationaryHistorySlotGraph
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual original controller histories and their slotgraph laws. -/

import D5.S3.ObserverMemory.Algorithms.StationaryHistoryCoreData

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
open private B_card selection_exists selection_spec selected_resolving selected_row_spec
  resolving_unary core_card core_subset first_not_target read_states_partition read_state_mem
  parent_arrival history_target literal_le_tail representative_bounds selected_literal
  background_target binary_background resolving_background positive_rep_binary actual_read_count
  from D5.S3.ObserverMemory.Algorithms.StationaryHistoryCore
open private fiber_surplus raw_rows_image from
  D5.S3.ObserverMemory.Algorithms.FixedForestSlotGraph
attribute [local instance] Classical.propDecidable

universe u
variable {P ell h : Nat} {Q : Type u} (C : Controller P Q) (hP : 1 < P)
  (I : Initialized C hP ell h) [NeZero (3 * P)] [DecidableEq Q]

omit [DecidableEq Q] in
private theorem mem_nonroots (n : Node C hP I) : n ∈ nonroots C hP I ↔ parent C hP I n ≠ none := by
  change n ∈ Finset.univ.filter (fun n => parent C hP I n ≠ none) ↔ _
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]

private theorem binary_edge_realized {a : Node C hP I}
    (ha : (children C hP I a).card = 2) {z : Slot (Q := Q)}
    (hz : (row C hP I a, z) ∈ edges C hP I) :
    ∃ n, parent C hP I n = some a ∧ row C hP I n = z := by
  let S := (children C hP I a).image (fun n => (row C hP I a,row C hP I n))
  have sub : S ⊆ outgoing C hP I (row C hP I a) := by
    intro e he
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_filter.mpr ⟨(mem_edges C hP I _ _).2
      ⟨n,a,(Finset.mem_filter.mp hn).2,rfl,rfl⟩,rfl⟩
  have hi : Set.InjOn (fun n => (row C hP I a,row C hP I n)) (children C hP I a) := by
    intro n hn m hm he
    exact child_digit_injective C hP I (Finset.mem_filter.mp hn).2
      (Finset.mem_filter.mp hm).2 (congrArg (fun e => e.2.2) he)
  have sc : S.card = 2 := by rw [Finset.card_image_of_injOn hi]; exact ha
  have oc := binary_outgoing C hP I a (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩)
  have eq := Finset.eq_of_subset_of_card_le sub (by omega)
  have mem : (row C hP I a,z) ∈ S := eq.symm ▸ Finset.mem_filter.mpr ⟨hz,rfl⟩
  obtain ⟨n,hn,he⟩ := Finset.mem_image.mp mem
  exact ⟨n,(Finset.mem_filter.mp hn).2,congrArg Prod.snd he⟩

private theorem resolving_double {v : Slot (Q := Q)} (hv : v ∈ resolvingRows C hP I) :
    ∃ n m : Node C hP I, n ≠ m ∧ row C hP I n = v ∧ row C hP I m = v := by
  have vc : (outgoing C hP I v).card = 2 := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).2
  obtain ⟨a,b,hab,he⟩ := Finset.card_eq_two.mp vc
  have am : a ∈ outgoing C hP I v := he.symm ▸ (by simp)
  have bm : b ∈ outgoing C hP I v := he.symm ▸ (by simp)
  obtain ⟨x,n,hxn,hn,ha⟩ := (mem_edges C hP I a.1 a.2).1 (Finset.mem_filter.mp am).1
  obtain ⟨y,m,hym,hm,hb⟩ := (mem_edges C hP I b.1 b.2).1 (Finset.mem_filter.mp bm).1
  have nr : row C hP I n = v := hn.trans (Finset.mem_filter.mp am).2
  have mr : row C hP I m = v := hm.trans (Finset.mem_filter.mp bm).2
  refine ⟨n,m,?_,nr,mr⟩
  intro eq
  subst m
  have hu := resolving_unary C hP I (nr ▸ hv)
  have xy := FixedForestTargetInventory.unary_child_unique (physicalForest C hP I) hu hxn hym
  apply hab
  exact Prod.ext ((Finset.mem_filter.mp am).2.trans (Finset.mem_filter.mp bm).2.symm)
    (ha.symm.trans ((congrArg (row C hP I) xy).trans hb))

private theorem row_nonroot {w : Slot (Q := Q)} (hw : w ∈ nonrootRows C hP I)
    {n : Node C hP I} (hn : row C hP I n = w) : parent C hP I n ≠ none := by
  intro hp
  obtain ⟨c,hc⟩ := (roots_exact C hP I n).mp hp
  have hr : w ∈ rootRows C hP I := by
    apply Finset.mem_image.mpr
    exact ⟨c,Finset.mem_univ _,(congrArg (row C hP I) hc.symm).trans hn⟩
  exact Finset.disjoint_left.mp (roots_disjoint C hP I) hr hw

private theorem two_double_fibers {w v : Slot (Q := Q)}
    (hw : w ∈ nonrootRows C hP I) (hv : v ∈ nonrootRows C hP I) (hd : w ≠ v)
    (w2 : ∃ n m : Node C hP I, n ≠ m ∧ row C hP I n = w ∧ row C hP I m = w)
    (v2 : ∃ n m : Node C hP I, n ≠ m ∧ row C hP I n = v ∧ row C hP I m = v)
    (hJ : StationaryHistorySlotGraph.J C hP I = 1)
    (hX : StationaryHistorySlotGraph.Xi C hP I = 1) :
    ((nonroots C hP I).filter (fun n => row C hP I n = w)).card = 2 ∧
    ((nonroots C hP I).filter (fun n => row C hP I n = v)).card = 2 ∧
    ∀ n m : Node C hP I, n ≠ m → row C hP I n = row C hP I m →
      row C hP I n = w ∨ row C hP I n = v := by
  let count := fun z => ((nonroots C hP I).filter (fun n => row C hP I n = z)).card
  have double {z : Slot (Q := Q)} (hz : z ∈ nonrootRows C hP I)
      (d : ∃ n m : Node C hP I, n ≠ m ∧ row C hP I n = z ∧ row C hP I m = z) : 2 ≤ count z := by
    obtain ⟨n,m,ne,hn,hm⟩ := d
    have sub : {n,m} ⊆ (nonroots C hP I).filter (fun n => row C hP I n = z) := by
      simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff,Finset.mem_filter]
      exact ⟨⟨(mem_nonroots C hP I n).2 (row_nonroot C hP I hz hn),hn⟩,
        ⟨(mem_nonroots C hP I m).2 (row_nonroot C hP I hz hm),hm⟩⟩
    simpa [count,ne] using Finset.card_le_card sub
  have dw := double hw w2
  have dv := double hv v2
  have total : ∑ z ∈ nonrootRows C hP I, (count z - 1) = 2 := by
    simpa [count,hJ,hX] using actual_edge_incidence C hP I
  have pair : count w - 1 + (count v - 1) ≤ 2 := by
    have hh := Finset.sum_le_sum_of_subset (f := fun z => count z - 1)
      (show {w,v} ⊆ nonrootRows C hP I by simp [Finset.insert_subset_iff,hw,hv])
    simpa [hd,total] using hh
  refine ⟨by change count w = 2; omega,by change count v = 2; omega,?_⟩
  intro n m ne he
  by_contra hh
  have nw : row C hP I n ≠ w := fun h => hh (Or.inl h)
  have nv : row C hP I n ≠ v := fun h => hh (Or.inr h)
  have nr : row C hP I n ∈ nonrootRows C hP I := by
    have rmem : row C hP I n ∈ rows C hP I := Finset.mem_image.mpr ⟨n,Finset.mem_univ _,rfl⟩
    by_cases hp : parent C hP I n = none
    · obtain ⟨c,hc⟩ := (roots_exact C hP I n).mp hp
      have nc : n = root C hP I c := hc
      have mc : m = root C hP I c := by
        have mr : parent C hP I m = none := by
          by_contra hm
          have mm : row C hP I m ∈ nonrootRows C hP I :=
            Finset.mem_image.mpr ⟨m,(mem_nonroots C hP I m).2 hm,rfl⟩
          have rm : row C hP I m ∈ rootRows C hP I := by
            apply Finset.mem_image.mpr
            exact ⟨c,Finset.mem_univ _,(congrArg (row C hP I) nc.symm).trans he⟩
          exact Finset.disjoint_left.mp (roots_disjoint C hP I) rm mm
        obtain ⟨d,md⟩ := (roots_exact C hP I m).mp mr
        have cd : c = d := by
          have col := congrArg Prod.snd he
          rw [nc,md] at col
          change color C hP I (root C hP I c) = color C hP I (root C hP I d) at col
          have cc : color C hP I (root C hP I c) = c := (physicalForest C hP I).root_color c
          have dd : color C hP I (root C hP I d) = d := (physicalForest C hP I).root_color d
          rwa [cc,dd] at col
        simpa [cd] using md
      exact False.elim (ne (nc.trans mc.symm))
    · exact Finset.mem_image.mpr ⟨n,(mem_nonroots C hP I n).2 hp,rfl⟩
  have dn := double nr ⟨n,m,ne,rfl,he.symm⟩
  have triple : count w - 1 + (count v - 1) + (count (row C hP I n) - 1) ≤ 2 := by
    have ss : {w,v,row C hP I n} ⊆ nonrootRows C hP I := by
      simp [Finset.insert_subset_iff,hw,hv,nr]
    have hh := Finset.sum_le_sum_of_subset (f := fun z => count z - 1) ss
    simpa [hd,nw.symm,nv.symm,total,Nat.add_assoc] using hh
  omega

private theorem collision_nonroot {n m : Node C hP I} (hne : n ≠ m)
    (he : row C hP I n = row C hP I m) :
    row C hP I n ∈ nonrootRows C hP I := by
  by_cases hp : parent C hP I n = none
  · obtain ⟨c,hc⟩ := (roots_exact C hP I n).mp hp
    have mr : parent C hP I m = none := by
      by_contra hm
      have mm : row C hP I m ∈ nonrootRows C hP I :=
        Finset.mem_image.mpr ⟨m,(mem_nonroots C hP I m).2 hm,rfl⟩
      have rm : row C hP I m ∈ rootRows C hP I :=
        Finset.mem_image.mpr ⟨c,Finset.mem_univ _,(congrArg (row C hP I) hc.symm).trans he⟩
      exact Finset.disjoint_left.mp (roots_disjoint C hP I) rm mm
    obtain ⟨d,md⟩ := (roots_exact C hP I m).mp mr
    have col := congrArg Prod.snd he
    change color C hP I n = color C hP I m at col
    rw [hc,md] at col
    have cc : color C hP I (root C hP I c) = c := (physicalForest C hP I).root_color c
    have dd : color C hP I (root C hP I d) = d := (physicalForest C hP I).root_color d
    rw [cc,dd] at col
    exact False.elim (hne (hc.trans (col ▸ md).symm))
  · exact Finset.mem_image.mpr ⟨n,(mem_nonroots C hP I n).2 hp,rfl⟩

private theorem double_row_exact {z : Slot (Q := Q)} (hz : z ∈ nonrootRows C hP I)
    (hc : ((nonroots C hP I).filter (fun n => row C hP I n = z)).card = 2)
    {n m : Node C hP I} (hne : n ≠ m) (hn : row C hP I n = z) (hm : row C hP I m = z)
    {a : Node C hP I} (ha : row C hP I a = z) : a = n ∨ a = m := by
  have sub : {n,m} ⊆ (nonroots C hP I).filter (fun n => row C hP I n = z) := by
    simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff,Finset.mem_filter]
    exact ⟨⟨(mem_nonroots C hP I n).2 (row_nonroot C hP I hz hn),hn⟩,
      ⟨(mem_nonroots C hP I m).2 (row_nonroot C hP I hz hm),hm⟩⟩
  have eq := Finset.eq_of_subset_of_card_le sub (by simp [hc,hne])
  have am : a ∈ (nonroots C hP I).filter (fun n => row C hP I n = z) :=
    Finset.mem_filter.mpr ⟨(mem_nonroots C hP I a).2 (row_nonroot C hP I hz ha),ha⟩
  rw [← eq] at am
  simpa only [Finset.mem_insert,Finset.mem_singleton] using am

private theorem single_incoming {w : Slot (Q := Q)} (hw : w ∈ nonrootRows C hP I)
    (h2 : 2 ≤ (incoming C hP I w).card) (hJ : StationaryHistorySlotGraph.J C hP I = 1)
    {z : Slot (Q := Q)} (hz : z ∈ nonrootRows C hP I) (hne : z ≠ w) :
    (incoming C hP I z).card ≤ 1 := by
  have total : ∑ z ∈ nonrootRows C hP I, ((incoming C hP I z).card - 1) = 1 := hJ
  have hh := Finset.sum_le_sum_of_subset (f := fun z => (incoming C hP I z).card - 1)
    (show {w,z} ⊆ nonrootRows C hP I by simp [Finset.insert_subset_iff,hw,hz])
  have le : (incoming C hP I w).card - 1 + ((incoming C hP I z).card - 1) ≤ 1 := by
    simpa [hne.symm,total] using hh
  omega

private theorem shared_sources {w : Slot (Q := Q)}
    (hw : 2 ≤ ((incoming C hP I w).filter (fun a => a.1 ∈ productionRows C hP I)).card) :
    ∃ A B n m : Node C hP I,
      (children C hP I A).card = 2 ∧ (children C hP I B).card = 2 ∧
      row C hP I A ≠ row C hP I B ∧ parent C hP I n = some A ∧
      parent C hP I m = some B ∧ n ≠ m ∧ row C hP I n = w ∧ row C hP I m = w := by
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (show 1 <
    ((incoming C hP I w).filter (fun a => a.1 ∈ productionRows C hP I)).card by omega)
  have ai := Finset.mem_filter.mp ha
  have bi := Finset.mem_filter.mp hb
  have ar := (Finset.mem_filter.mp ai.1).2
  have br := (Finset.mem_filter.mp bi.1).2
  obtain ⟨A,hA,haA⟩ := Finset.mem_image.mp ai.2
  obtain ⟨B,hB,hbB⟩ := Finset.mem_image.mp bi.2
  have ac := (Finset.mem_filter.mp hA).2
  have bc := (Finset.mem_filter.mp hB).2
  have ab : row C hP I A ≠ row C hP I B := by
    intro he
    apply hab
    exact Prod.ext (haA.symm.trans (he.trans hbB)) (ar.trans br.symm)
  have ae : (row C hP I A,w) ∈ edges C hP I := by
    rw [haA,← ar]; exact (Finset.mem_filter.mp ai.1).1
  have be : (row C hP I B,w) ∈ edges C hP I := by
    rw [hbB,← br]; exact (Finset.mem_filter.mp bi.1).1
  obtain ⟨n,hn,nr⟩ := binary_edge_realized C hP I ac ae
  obtain ⟨m,hm,mr⟩ := binary_edge_realized C hP I bc be
  have nm : n ≠ m := by
    intro he; subst m
    have aa := Option.some.inj (hn.symm.trans hm)
    exact ab (congrArg (row C hP I) aa)
  exact ⟨A,B,n,m,ac,bc,ab,hn,hm,nm,nr,mr⟩

private theorem incoming_pair {w : Slot (Q := Q)} {A B n m : Node C hP I}
    (ab : row C hP I A ≠ row C hP I B) (hn : parent C hP I n = some A)
    (hm : parent C hP I m = some B) (nr : row C hP I n = w) (mr : row C hP I m = w) :
    2 ≤ (incoming C hP I w).card := by
  have am : (row C hP I A,w) ∈ incoming C hP I w :=
    Finset.mem_filter.mpr ⟨(mem_edges C hP I _ _).2 ⟨n,A,hn,rfl,nr⟩,rfl⟩
  have bm : (row C hP I B,w) ∈ incoming C hP I w :=
    Finset.mem_filter.mpr ⟨(mem_edges C hP I _ _).2 ⟨m,B,hm,rfl,mr⟩,rfl⟩
  have ne : (row C hP I A,w) ≠ (row C hP I B,w) := fun he => ab (congrArg Prod.fst he)
  have hh := Finset.card_le_card (show {(row C hP I A,w),(row C hP I B,w)} ⊆ incoming C hP I w by
    simp [Finset.insert_subset_iff,am,bm])
  simpa [ne] using hh

omit [DecidableEq Q] in
private theorem other_binary_child {A H : Node C hP I} (hA : (children C hP I A).card = 2)
    (hH : parent C hP I H = some A) :
    ∃ a, parent C hP I a = some A ∧ color C hP I a ≠ color C hP I H := by
  have hm : H ∈ children C hP I A := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hH⟩
  have ex : ∃ a, a ∈ children C hP I A ∧ a ≠ H := by
    by_contra he
    push Not at he
    have sub : children C hP I A ⊆ {H} := by intro a ha; simpa using he a ha
    have hc := Finset.card_le_card sub
    simp only [Finset.card_singleton,hA] at hc
    omega
  obtain ⟨a,ha,ne⟩ := ex
  have hp := (Finset.mem_filter.mp ha).2
  exact ⟨a,hp,fun hc => ne (child_digit_injective C hP I hp hH hc)⟩

private theorem shared_three_actual {w : Slot (Q := Q)} {A B H K : Node C hP I}
    (hA : (children C hP I A).card = 2) (hB : (children C hP I B).card = 2)
    (ab : row C hP I A ≠ row C hP I B) (hpH : parent C hP I H = some A)
    (hpK : parent C hP I K = some B) (hrH : row C hP I H = w) (hrK : row C hP I K = w)
    (hJ : StationaryHistorySlotGraph.J C hP I = 1) :
    ((children C hP I A ∪ children C hP I B).image (color C hP I)).card = 3 := by
  obtain ⟨a,ha,ac⟩ := other_binary_child C hP I hA hpH
  obtain ⟨b,hb,bc⟩ := other_binary_child C hP I hB hpK
  have hk : color C hP I H = color C hP I K := congrArg Prod.snd (hrH.trans hrK.symm)
  have aq : readControl C hP I a = readControl C hP I H :=
    (child_delay_target C hP I ha).2.2.1.trans (child_delay_target C hP I hpH).2.2.1.symm
  have bq : readControl C hP I b = readControl C hP I K :=
    (child_delay_target C hP I hb).2.2.1.trans (child_delay_target C hP I hpK).2.2.1.symm
  have abc : color C hP I a ≠ color C hP I b := by
    intro hc
    have eq : row C hP I a = row C hP I b := Prod.ext
      (aq.trans ((congrArg Prod.fst (hrH.trans hrK.symm)).trans bq.symm)) hc
    have ne : a ≠ b := by
      intro he; subst b
      exact ab (congrArg (row C hP I) (Option.some.inj (ha.symm.trans hb)))
    have az := collision_nonroot C hP I ne eq
    have wm : w ∈ nonrootRows C hP I :=
      Finset.mem_image.mpr ⟨H,(mem_nonroots C hP I H).2 (by rw [hpH]; simp),hrH⟩
    have aw : row C hP I a ≠ w := fun he => ac (congrArg Prod.snd (he.trans hrH.symm))
    have atwo := incoming_pair C hP I ab ha hb rfl eq.symm
    have aone := single_incoming C hP I wm (incoming_pair C hP I ab hpH hpK hrH hrK) hJ az aw
    omega
  let D := (children C hP I A ∪ children C hP I B).image (color C hP I)
  have sub : {color C hP I H,color C hP I a,color C hP I b} ⊆ D := by
    simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
    refine ⟨?_,?_,?_⟩
    · exact Finset.mem_image.mpr ⟨H,
        Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpH⟩),rfl⟩
    · exact Finset.mem_image.mpr ⟨a,
        Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩),rfl⟩
    · exact Finset.mem_image.mpr ⟨b,
        Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩),rfl⟩
  have hbc : color C hP I H ≠ color C hP I b := fun he => bc (he.symm.trans hk)
  have low : 3 ≤ D.card := by
    simpa [ac.symm,hbc,abc] using Finset.card_le_card sub
  have high : D.card ≤ 3 := by
    have hh := Finset.card_le_card (Finset.subset_univ D)
    simpa using hh
  exact Nat.le_antisymm high low

private theorem resolving_colors_actual {v : Slot (Q := Q)}
    (hv : v ∈ resolvingRows C hP I) (vm : v ∈ nonrootRows C hP I)
    (vc : ((nonroots C hP I).filter (fun n => row C hP I n = v)).card = 2)
    {H1 K1 : Node C hP I} (hne : H1 ≠ K1)
    (hrH : row C hP I H1 = v) (hrK : row C hP I K1 = v)
    {a b : Node C hP I} (ha : parent C hP I a = some H1) (hb : parent C hP I b = some K1) :
    color C hP I a ≠ color C hP I b := by
  intro hc
  have eq : row C hP I a = row C hP I b := Prod.ext
    (same_row_arrival C hP I ha hb (congrArg Prod.fst (hrH.trans hrK.symm))
      (congrArg Prod.snd (hrH.trans hrK.symm))).2 hc
  have sub : outgoing C hP I v ⊆ {(v,row C hP I a)} := by
    intro edge he
    obtain ⟨x,p,hp,pr,xr⟩ := (mem_edges C hP I edge.1 edge.2).1 (Finset.mem_filter.mp he).1
    have pv : row C hP I p = v := pr.trans (Finset.mem_filter.mp he).2
    have px := double_row_exact C hP I vm vc hne hrH hrK pv
    have out : row C hP I x = row C hP I a := by
      rcases px with rfl | rfl
      · have ux := FixedForestTargetInventory.unary_child_unique (physicalForest C hP I)
          (resolving_unary C hP I (hrH ▸ hv)) hp ha
        exact congrArg (row C hP I) ux
      · have ux := FixedForestTargetInventory.unary_child_unique (physicalForest C hP I)
          (resolving_unary C hP I (hrK ▸ hv)) hp hb
        exact (congrArg (row C hP I) ux).trans eq.symm
    apply Finset.mem_singleton.mpr
    exact Prod.ext (Finset.mem_filter.mp he).2 (xr.symm.trans out)
  have bound := Finset.card_le_card sub
  have two := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).2
  simp only [Finset.card_singleton,two] at bound
  omega

private theorem prescribed_at_unmarked_rows (w v : Slot (Q := Q))
    (hJ : StationaryHistorySlotGraph.J C hP I = 1)
    (hX : StationaryHistorySlotGraph.Xi C hP I = 1)
    (hw : 2 ≤ ((incoming C hP I w).filter (fun a => a.1 ∈ productionRows C hP I)).card)
    (hwprod : w ∈ productionRows C hP I) (hv : v ∈ resolvingRows C hP I) (hd : w ≠ v)
    (hsw : ∀ n : Node C hP I, row C hP I n = w →
      (children C hP I n).card ≠ 2 → (support C hP I n).card = 1)
    (hsv : ∀ n : Node C hP I, row C hP I n = v → (support C hP I n).card = 1) :
    ∃ R : FixedForestTargetInventory.Prescribed (physicalForest C hP I),
      row C hP I R.H = w ∧ row C hP I R.K = w ∧
      row C hP I R.H1 = v ∧ row C hP I R.K1 = v ∧
      (support C hP I R.K).card = 1 ∧ (support C hP I R.H1).card = 1 ∧
      (support C hP I R.K1).card = 1 := by
  obtain ⟨A,B,n,m,hA,hB,ab,np,mp,nm,nr,mr⟩ := shared_sources C hP I hw
  have wm : w ∈ nonrootRows C hP I :=
    Finset.mem_image.mpr ⟨n,(mem_nonroots C hP I n).2 (by rw [np]; simp),nr⟩
  obtain ⟨x,y,xy,xr,yr⟩ := resolving_double C hP I hv
  have vm : v ∈ nonrootRows C hP I := xr ▸ collision_nonroot C hP I xy (xr.trans yr.symm)
  have counts := two_double_fibers C hP I wm vm hd ⟨n,m,nm,nr,mr⟩ ⟨x,y,xy,xr,yr⟩ hJ hX
  obtain ⟨H,hH,Hr⟩ := Finset.mem_image.mp hwprod
  have Hc := (Finset.mem_filter.mp hH).2
  have side := double_row_exact C hP I wm counts.1 nm nr mr Hr
  have marked : ∃ A B H K : Node C hP I,
      (children C hP I A).card = 2 ∧ (children C hP I B).card = 2 ∧
      row C hP I A ≠ row C hP I B ∧ (children C hP I H).card = 2 ∧
      parent C hP I H = some A ∧ parent C hP I K = some B ∧
      H ≠ K ∧ row C hP I H = w ∧ row C hP I K = w := by
    rcases side with hn | hm
    · exact ⟨A,B,n,m,hA,hB,ab,hn ▸ Hc,np,mp,nm,nr,mr⟩
    · exact ⟨B,A,m,n,hB,hA,ab.symm,hm ▸ Hc,mp,np,nm.symm,mr,nr⟩
  obtain ⟨A,B,H,K,hA,hB,ab,Hc,Hp,Kp,HK,Hr,Kr⟩ := marked
  have Knb : (children C hP I K).card ≠ 2 := by
    intro hK
    exact HK (binary_row_unique C hP I Hc hK
      (congrArg Prod.fst (Hr.trans Kr.symm)) (congrArg Prod.snd (Hr.trans Kr.symm)))
  have Kpos : 0 < (children C hP I K).card := by
    by_contra hp
    have zero : (children C hP I K).card = 0 := by omega
    have leaf : IsLeaf C hP I K := by
      intro a ha
      have mem : a ∈ children C hP I K := Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩
      rw [Finset.card_eq_zero.mp zero] at mem
      exact Finset.notMem_empty _ mem
    have oz := (outgoing_zero C hP I K).2 leaf
    have ht := binary_outgoing C hP I H (Finset.mem_filter.mpr ⟨Finset.mem_univ _,Hc⟩)
    rw [Kr] at oz
    rw [Hr] at ht
    omega
  have Ku : (children C hP I K).card = 1 := by
    have hh := branching C hP I K
    omega
  obtain ⟨K1,km⟩ := Finset.card_pos.mp (show 0 < (children C hP I K).card by omega)
  have K1p := (Finset.mem_filter.mp km).2
  have he : (row C hP I H,row C hP I K1) ∈ edges C hP I :=
    (mem_edges C hP I _ _).2 ⟨K1,K,K1p,Kr.trans Hr.symm,rfl⟩
  obtain ⟨H1,H1p,eq⟩ := binary_edge_realized C hP I Hc he
  have childne : H1 ≠ K1 := by
    intro hc; subst K1
    exact HK (Option.some.inj (H1p.symm.trans K1p))
  have target := counts.2.2 H1 K1 childne eq
  have notw : row C hP I H1 ≠ w := by
    intro hh
    have sideH := double_row_exact C hP I wm counts.1 HK Hr Kr hh
    have sideK := double_row_exact C hP I wm counts.1 HK Hr Kr (eq.symm.trans hh)
    -- The incoming binary-parent rows differ; both continuing histories use w.
    rcases sideH with hHH | hHK <;> rcases sideK with hKH | hKK
    · exact childne (hHH.trans hKH.symm)
    · have aa := Option.some.inj (Hp.symm.trans (hHH ▸ H1p))
      have bb := Option.some.inj (Kp.symm.trans (hKK ▸ K1p))
      exact ab ((congrArg (row C hP I) aa).trans (Hr.trans Kr.symm)
        |>.trans (congrArg (row C hP I) bb).symm)
    · have aa := Option.some.inj (Kp.symm.trans (hHK ▸ H1p))
      have bb := Option.some.inj (Hp.symm.trans (hKH ▸ K1p))
      exact ab ((congrArg (row C hP I) bb).trans (Kr.trans Hr.symm)
        |>.trans (congrArg (row C hP I) aa).symm)
    · exact childne (hHK.trans hKK.symm)
  have H1r : row C hP I H1 = v := target.resolve_left notw
  have K1r : row C hP I K1 = v := eq.symm.trans H1r
  have H1u := resolving_unary C hP I (H1r ▸ hv)
  have K1u := resolving_unary C hP I (K1r ▸ hv)
  have unequal {a b : Node C hP I} (ha : row C hP I a = w) (hb : row C hP I b = v) : a ≠ b := by
    intro he; subst b; exact hd (ha.symm.trans hb)
  have Hdelay := row_delay_target C hP I
    (Finset.card_pos.mp (by omega : 0 < (children C hP I H).card))
    (congrArg Prod.fst (Hr.trans Kr.symm)) (congrArg Prod.snd (Hr.trans Kr.symm))
  have vdelay := row_delay_target C hP I
    (Finset.card_pos.mp (by omega : 0 < (children C hP I H1).card))
    (congrArg Prod.fst (H1r.trans K1r.symm)) (congrArg Prod.snd (H1r.trans K1r.symm))
  let R : FixedForestTargetInventory.Prescribed (physicalForest C hP I) := {
    A := A, B := B, H := H, K := K, H1 := H1, K1 := K1
    A_binary := hA, B_binary := hB, H_binary := Hc
    K_unary := Ku, H1_unary := H1u, K1_unary := K1u
    AB_distinct := fun he => ab (congrArg (row C hP I) he)
    marked_distinct := by simp [List.pairwise_cons,HK,childne,
      unequal Hr H1r,unequal Hr K1r,unequal Kr H1r,unequal Kr K1r]
    HK_parents := Or.inl ⟨Hp,Kp⟩
    HK_color := congrArg Prod.snd (Hr.trans Kr.symm)
    HK_disjoint := same_control_phase_disjoint C hP I HK (congrArg Prod.fst (Hr.trans Kr.symm))
    first_children := ⟨H1p,K1p⟩
    child_color := congrArg Prod.snd eq
    child_disjoint := same_control_phase_disjoint C hP I childne (congrArg Prod.fst eq)
    production_wait := Hdelay.1.symm
    resolving_wait := vdelay.1.symm
    resolving_colors := fun a b ha hb =>
      resolving_colors_actual C hP I hv vm counts.2.1 childne H1r K1r ha hb
    shared_three := shared_three_actual C hP I hA hB ab Hp Kp Hr Kr hJ }
  exact ⟨R,Hr,Kr,H1r,K1r,hsw K Kr Knb,hsv H1 H1r,hsv K1 K1r⟩

theorem single_collision_rows
    (hJ : StationaryHistorySlotGraph.J C hP I = 1)
    (hs : StationaryHistorySlotGraph.s C hP I = 1) :
    ∃ q : Q, ∃ w v : Slot (Q := Q),
      binaryMultiplicity C hP I q = 2 ∧ w.1 = q ∧
      (∀ q', q' ≠ q → binaryMultiplicity C hP I q' ≤ 1) ∧
      2 ≤ ((incoming C hP I w).filter (fun a => a.1 ∈ productionRows C hP I)).card ∧
      (∀ w', 2 ≤ (incoming C hP I w').card → w' = w) ∧
      resolvingRows C hP I = {v} := by
  have ex : ∃ q, q ∈ B C hP I ∧ 2 ≤ binaryMultiplicity C hP I q := by
    by_contra he
    push Not at he
    have zero : StationaryHistorySlotGraph.s C hP I = 0 := by
      apply Finset.sum_eq_zero
      intro q hq
      have hq' := he q hq
      omega
    omega
  obtain ⟨q,hq,bq⟩ := ex
  have qterm : binaryMultiplicity C hP I q - 1 ≤ 1 := by
    have ht := Finset.single_le_sum (f := fun q => binaryMultiplicity C hP I q - 1)
      (fun q _ => Nat.zero_le _) hq
    change binaryMultiplicity C hP I q - 1 ≤ StationaryHistorySlotGraph.s C hP I at ht
    simpa only [hs] using ht
  have qcount : binaryMultiplicity C hP I q = 2 := by omega
  have others : ∀ q', q' ≠ q → binaryMultiplicity C hP I q' ≤ 1 := by
    intro q' hne
    by_cases hm : q' ∈ B C hP I
    · have ht := Finset.sum_le_sum_of_subset (f := fun q => binaryMultiplicity C hP I q - 1)
        (show {q,q'} ⊆ B C hP I by simp [Finset.insert_subset_iff,hq,hm])
      have hh : binaryMultiplicity C hP I q - 1 + (binaryMultiplicity C hP I q' - 1) ≤ 1 := by
        have hh : binaryMultiplicity C hP I q - 1 + (binaryMultiplicity C hP I q' - 1) ≤
            StationaryHistorySlotGraph.s C hP I := by
          simpa [hne.symm,StationaryHistorySlotGraph.s] using ht
        simpa only [hs] using hh
      omega
    · have empty : (binaries C hP I).filter (fun n => nextTarget C hP I n = q') = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro n hn
        have hh := Finset.mem_filter.mp hn
        exact hm (Finset.mem_image.mpr ⟨n,hh.1,hh.2⟩)
      simp [binaryMultiplicity,empty]
  obtain ⟨A,hA,B,hB,AB⟩ := Finset.one_lt_card.mp (show 1 <
    ((binaries C hP I).filter (fun n => nextTarget C hP I n = q)).card by
      change 1 < binaryMultiplicity C hP I q; omega)
  have Ab := (Finset.mem_filter.mp (Finset.mem_filter.mp hA).1).2
  have Bb := (Finset.mem_filter.mp (Finset.mem_filter.mp hB).1).2
  have Aq := (Finset.mem_filter.mp hA).2
  have Bq := (Finset.mem_filter.mp hB).2
  have rowsne : row C hP I A ≠ row C hP I B := by
    intro he
    exact AB (binary_row_unique C hP I Ab Bb (congrArg Prod.fst he) (congrArg Prod.snd he))
  let DA := (children C hP I A).image (color C hP I)
  let DB := (children C hP I B).image (color C hP I)
  have cardA : DA.card = 2 := by
    rw [Finset.card_image_of_injOn]
    · exact Ab
    · intro a ha b hb he
      exact child_digit_injective C hP I (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 he
  have cardB : DB.card = 2 := by
    rw [Finset.card_image_of_injOn]
    · exact Bb
    · intro a ha b hb he
      exact child_digit_injective C hP I (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 he
  have union : (DA ∪ DB).card ≤ 3 := by
    have ht := Finset.card_le_card (Finset.subset_univ (DA ∪ DB))
    simpa using ht
  have inter : (DA ∩ DB).Nonempty := by
    apply Finset.card_pos.mp
    have count := Finset.card_union_add_card_inter DA DB
    omega
  obtain ⟨c,hc⟩ := inter
  obtain ⟨n,hn,nc⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hc).1
  obtain ⟨m,hm,mc⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hc).2
  have np := (Finset.mem_filter.mp hn).2
  have mp := (Finset.mem_filter.mp hm).2
  let w : Slot (Q := Q) := (q,c)
  have nr : row C hP I n = w := Prod.ext ((child_delay_target C hP I np).2.2.1.trans Aq) nc
  have mr : row C hP I m = w := Prod.ext ((child_delay_target C hP I mp).2.2.1.trans Bq) mc
  have inc : 2 ≤ ((incoming C hP I w).filter (fun a => a.1 ∈ productionRows C hP I)).card := by
    have am : (row C hP I A,w) ∈
        (incoming C hP I w).filter (fun a => a.1 ∈ productionRows C hP I) :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨(mem_edges C hP I _ _).2 ⟨n,A,np,rfl,nr⟩,rfl⟩,
        Finset.mem_image.mpr ⟨A,(Finset.mem_filter.mp hA).1,rfl⟩⟩
    have bm : (row C hP I B,w) ∈
        (incoming C hP I w).filter (fun a => a.1 ∈ productionRows C hP I) :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨(mem_edges C hP I _ _).2 ⟨m,B,mp,rfl,mr⟩,rfl⟩,
        Finset.mem_image.mpr ⟨B,(Finset.mem_filter.mp hB).1,rfl⟩⟩
    have ne : (row C hP I A,w) ≠ (row C hP I B,w) := fun he => rowsne (congrArg Prod.fst he)
    have ht := Finset.card_le_card (show {(row C hP I A,w),(row C hP I B,w)} ⊆
        (incoming C hP I w).filter (fun a => a.1 ∈ productionRows C hP I) by
      simp [Finset.insert_subset_iff,am,bm])
    simpa [ne] using ht
  have wm : w ∈ nonrootRows C hP I :=
    Finset.mem_image.mpr ⟨n,(mem_nonroots C hP I n).2 (by rw [np]; simp),nr⟩
  have unique : ∀ w', 2 ≤ (incoming C hP I w').card → w' = w := by
    intro w' htwo
    by_contra he
    obtain ⟨edge,hmem⟩ := Finset.card_pos.mp (show 0 < (incoming C hP I w').card by omega)
    obtain ⟨child,par,hpar,_,hr⟩ := (mem_edges C hP I edge.1 edge.2).1 (Finset.mem_filter.mp hmem).1
    have wr : row C hP I child = w' := hr.trans (Finset.mem_filter.mp hmem).2
    have wm' : w' ∈ nonrootRows C hP I :=
      Finset.mem_image.mpr ⟨child,(mem_nonroots C hP I child).2 (by rw [hpar]; simp),wr⟩
    have hle := single_incoming C hP I wm (incoming_pair C hP I rowsne np mp nr mr) hJ wm' he
    omega
  have rescard := (two_outgoing_count C hP I).2.2
  rw [hJ] at rescard
  obtain ⟨v,hv⟩ := Finset.card_eq_one.mp rescard
  exact ⟨q,w,v,qcount,rfl,others,inc,unique,hv⟩

theorem prescribed_of_single_collision
    (hJ : StationaryHistorySlotGraph.J C hP I = 1)
    (hs : StationaryHistorySlotGraph.s C hP I = 1)
    (hX : StationaryHistorySlotGraph.Xi C hP I = 1)
    (hshape : ∀ w v : Slot (Q := Q),
      2 ≤ ((incoming C hP I w).filter (fun a => a.1 ∈ productionRows C hP I)).card →
      v ∈ resolvingRows C hP I →
      w ∈ productionRows C hP I ∧ w ≠ v ∧
      (∀ n : Node C hP I, row C hP I n = w → (children C hP I n).card ≠ 2 →
        (support C hP I n).card = 1) ∧
      (∀ n : Node C hP I, row C hP I n = v → (support C hP I n).card = 1)) :
    ∃ R : FixedForestTargetInventory.Prescribed (physicalForest C hP I),
      row C hP I R.H = row C hP I R.K ∧
      row C hP I R.H1 = row C hP I R.K1 ∧
      row C hP I R.H ≠ row C hP I R.H1 ∧
      (support C hP I R.K).card = 1 ∧ (support C hP I R.H1).card = 1 ∧
      (support C hP I R.K1).card = 1 := by
  obtain ⟨q,w,v,_,_,_,inc,_,res⟩ := single_collision_rows C hP I hJ hs
  have hv : v ∈ resolvingRows C hP I := res ▸ (Finset.mem_singleton_self v)
  obtain ⟨prod,hd,sw,sv⟩ := hshape w v inc hv
  obtain ⟨R,Hr,Kr,H1r,K1r,sk,sh1,sk1⟩ :=
    prescribed_at_unmarked_rows C hP I w v hJ hX inc prod hv hd sw sv
  exact ⟨R,Hr.trans Kr.symm,H1r.trans K1r.symm,
    fun he => hd (Hr.symm.trans (he.trans H1r)),sk,sh1,sk1⟩


end D5.S3.ObserverMemory.Algorithms.StationaryHistorySlotGraph
