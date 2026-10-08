/- GID: D5/S3/ObserverMemory/Algorithms/StationaryHistoryData
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/StationaryHistoryData
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual original controller histories and their data laws. -/

import D5.S3.ObserverMemory.Algorithms.StationaryHistoryContinuation

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
open private indexed_disjoint literal_gap_positive root_data from
  D5.S3.ObserverMemory.Algorithms.StationaryHistoryContinuation
attribute [local instance] Classical.propDecidable

universe u
variable {P ell h : Nat} {Q : Type u} (C : Controller P Q) (hP : 1 < P)
    (I : Initialized C hP ell h)

/-- The derived data records the actual history image before any interval or
branch-count assertions are added. No forest or numeric inventory is supplied. -/
structure HistoryData [NeZero (3 * P)] : Prop where
  root_data : ∀ c, color C hP I (root C hP I c) = c ∧
    historyShift C hP I (root C hP I c) = ell ∧ level C hP I (root C hP I c) = 0
  root_support : ∀ c x, x ∈ support C hP I (root C hP I c) ↔
    digit hP (x + (ell : ZMod (3 * P))) = c
  reads_pos : ∀ x, 0 < reads C hP I x
  reads_bound : ∀ x, reads C hP I x ≤ h
  event_fiber : Nonempty (Event C hP I ≃
    Σ n : History C hP I, {x : ZMod (3 * P) // x ∈ support C hP I n})
  first : ∀ x, event C hP I ⟨x,⟨0,reads_pos x⟩⟩ =
    root C hP I (digit hP (x + (ell : ZMod (3 * P))))
  event_level : ∀ e, level C hP I (event C hP I e) = e.2.val
  event_time : ∀ e, time C hP I (event C hP I e) = readTime C hP I e.1 e.2
  event_color : ∀ e, color C hP I (event C hP I e) =
    digit hP (C.run hP (e.1,C.initial) (readTime C hP I e.1 e.2)).1
  support_nonempty : ∀ n, (support C hP I n).Nonempty
  parent_level : ∀ n p, parent C hP I n = some p → level C hP I n = level C hP I p + 1
  parent_support : ∀ n p, parent C hP I n = some p → support C hP I n ⊆ support C hP I p
  indexed_disjoint : ∀ n m, n ≠ m →
    Disjoint (indexedSupport C hP I n) (indexedSupport C hP I m)
  singleton_unary : ∀ n, (support C hP I n).card = 1 → ¬IsLeaf C hP I n →
    (children C hP I n).card = 1
  root_count : Fintype.card {n : History C hP I // parent C hP I n = none} = 3
  leaf_count : Fintype.card {n : History C hP I // IsLeaf C hP I n} = 3 * P
  leaf_original : ∀ n x, IsLeaf C hP I n → x ∈ support C hP I n → leafLabel C hP I n = x
  phase_disjoint : ∀ n m, n ≠ m → readControl C hP I n = readControl C hP I m →
    Disjoint (phaseSupport C hP I n) (phaseSupport C hP I m)
  time_decomposition : ∀ n, time C hP I n = historyShift C hP I n + level C hP I n
  literal_gap : ∀ x i (hi : i + 1 < reads C hP I x),
    0 < readTime C hP I x ⟨i + 1,hi⟩ - (readTime C hP I x ⟨i,by omega⟩ + 1) ∧
    historyShift C hP I (event C hP I ⟨x,⟨i + 1,hi⟩⟩) =
      historyShift C hP I (event C hP I ⟨x,⟨i,by omega⟩⟩) + 
        (readTime C hP I x ⟨i + 1,hi⟩ - (readTime C hP I x ⟨i,by omega⟩ + 1))

/-- All fields are obtained from the one original initialized implementation. -/
theorem actual_history_data [NeZero (3 * P)] : HistoryData C hP I where
  root_data := root_data C hP I
  root_support := root_support C hP I
  reads_pos := reads_pos C hP I
  reads_bound := reads_bound C hP I
  event_fiber := ⟨eventIncidenceEquiv C hP I⟩
  first := first_event C hP I
  event_level := event_level C hP I
  event_time := event_time C hP I
  event_color := event_color C hP I
  support_nonempty := support_nonempty C hP I
  parent_level := fun _ _ hp => parent_level C hP I hp
  parent_support := fun _ _ hp => support_parent C hP I hp
  indexed_disjoint := fun _ _ hn => indexed_disjoint C hP I hn
  phase_disjoint := fun _ _ hn hq => same_control_phase_disjoint C hP I hn hq
  time_decomposition := history_time_decomposition C hP I
  literal_gap := literal_shift_gap C hP I
  singleton_unary := singleton_continuation C hP I
  root_count := by simpa using (Fintype.card_congr (rootEquiv C hP I)).symm
  leaf_count := by simpa using (Fintype.card_congr (leafEquiv C hP I)).symm
  leaf_original := by
    intro n x hn hx
    simp only [leafLabel,dif_pos hn]
    let y := (leafEquiv C hP I).symm ⟨n,hn⟩
    have hy : event C hP I (finalEvent C hP I y) = n :=
      congrArg Subtype.val ((leafEquiv C hP I).apply_symm_apply ⟨n,hn⟩)
    have hout := leaf_original C hP I n hn x hx
    have hyout := final_halt C hP I y
    have hw := congrArg Subtype.val hy
    change eventWord C hP I (finalEvent C hP I y) = n.val at hw
    rw [hw] at hyout
    exact UnitInstruction.halt.inj (hyout.symm.trans hout)



end D5.S3.ObserverMemory.Algorithms.StationaryReadHistory
