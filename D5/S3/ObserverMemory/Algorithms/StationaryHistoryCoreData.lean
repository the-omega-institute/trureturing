/- GID: D5/S3/ObserverMemory/Algorithms/StationaryHistoryCoreData
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/StationaryHistoryCoreData
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual original controller histories and their coredata laws. -/

import D5.S3.ObserverMemory.Algorithms.StationaryHistoryCore

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

/-- A controller-derived interface for the subsequent multiplicity-preserving
weighted inventory. All fields are conclusions, rather than supplied data. -/
structure CoreData [Fintype Q] : Prop where
  edge_surplus : (∑ z ∈ nonrootRows C hP I,
    (((nonroots C hP I).filter (fun n => row C hP I n = z)).card - 1)) = J C hP I + Xi C hP I
  out_degree : ∀ n, (outgoing C hP I (row C hP I n)).card ≤ 2
  two_count : (twoRows C hP I).card = 3 * (P - 1) + J C hP I
  production_count : (productionRows C hP I).card = 3 * (P - 1)
  resolving_count : (resolvingRows C hP I).card = J C hP I
  target_incidence : ∀ q, 2 * (twoAt C hP I q).card ≤ 3 + targetJ C hP I q ∧
    (twoAt C hP I q).card - 1 ≤ targetJ C hP I q
  binary_targets : (B C hP I).card = 3 * (P - 1) - s C hP I
  selected_count : (selectedTargets C hP I).card = s C hP I
  selected_outside : selectedTargets C hP I ⊆ G C hP I \ B C hP I
  selected_row : ∀ q ∈ selectedTargets C hP I,
    selectedRow C hP I q ∈ resolvingRows C hP I ∧ target C hP I (selectedRow C hP I q) = q
  selected_distinct : Set.InjOn (selectedRow C hP I) (selectedTargets C hP I)
  sharing_bound : s C hP I ≤ J C hP I
  pure_unary : ∀ n, row C hP I n ∈ resolvingRows C hP I → (children C hP I n).card = 1
  core_count : (core C hP I).card = 3 * (P - 1)
  extra_count : (extras C hP I).card = e C hP I
  actual_reads : Fintype.card (ActualRead C hP I) = 3 * (P - 1) + 1 + e C hP I
  target_partition : targets C hP I = core C hP I ∪ extras C hP I
  target_disjoint : Disjoint (core C hP I) (extras C hP I)
  binary_representative : ∀ n, (children C hP I n).card = 2 →
    1 ≤ positiveRepresentative C hP I n ∧ positiveRepresentative C hP I n < P
  binary_baseline : ∀ q ∈ B C hP I, baseline C hP I q = binaryBaseline C hP I q
  resolving_baseline : ∀ q ∈ selectedTargets C hP I,
    baseline C hP I q = literal C hP I (selectedRow C hP I q)
  baseline_bounds : ∀ q ∈ targets C hP I, 1 ≤ baseline C hP I q ∧
    baseline C hP I q ≤ tail C hP I q ∧ (q ∈ extras C hP I → baseline C hP I q = 1)
  core_background : ∀ q ∈ core C hP I, 2 ≤ (backgroundDigits C hP I q).card ∧ k C hP I q ≤ 1
  extra_background : ∀ q ∈ extras C hP I, backgroundChildren C hP I q = ∅
  indexed_disjoint : ∀ q n m, n ∈ backgroundChildren C hP I q → m ∈ backgroundChildren C hP I q →
    n ≠ m → Disjoint (indexedSupport C hP I n) (indexedSupport C hP I m)

/-- Every finite nominal original controller supplies the unrestricted slot
graph, exact core/extras cardinalities, and score-independent baselines. -/
theorem actual_core_data [Fintype Q] : CoreData C hP I where
  edge_surplus := actual_edge_incidence C hP I
  out_degree := outgoing_degree C hP I
  two_count := (two_outgoing_count C hP I).1
  production_count := (two_outgoing_count C hP I).2.1
  resolving_count := (two_outgoing_count C hP I).2.2
  target_incidence := target_incidence C hP I
  binary_targets := (structural_core C hP I).1
  selected_count := (selection_spec C hP I).2
  selected_outside := (selection_spec C hP I).1
  selected_row := (structural_core C hP I).2.2.2.2.1
  selected_distinct := (resolving_selection C hP I).2
  sharing_bound := (resolving_selection C hP I).1
  pure_unary := (structural_core C hP I).2.2.2.2.2
  core_count := (structural_core C hP I).2.1
  extra_count := (structural_core C hP I).2.2.1
  actual_reads := actual_read_count C hP I
  target_partition := by rw [extras,Finset.union_sdiff_of_subset (core_subset C hP I)]
  target_disjoint := by
    apply Finset.disjoint_left.mpr
    intro q hq he
    exact (Finset.mem_sdiff.mp he).2 hq
  binary_representative := positive_rep_binary C hP I
  binary_baseline := by intro q hq; simp only [baseline,if_pos hq]
  resolving_baseline := by
    intro q hq
    have hb := (Finset.mem_sdiff.mp ((selection_spec C hP I).1 hq)).2
    simp only [baseline,if_neg hb,if_pos hq]
  baseline_bounds := baseline_bounds C hP I
  core_background := (background_structure C hP I).1
  extra_background := (background_structure C hP I).2.1
  indexed_disjoint := (background_structure C hP I).2.2


end D5.S3.ObserverMemory.Algorithms.StationaryHistorySlotGraph
