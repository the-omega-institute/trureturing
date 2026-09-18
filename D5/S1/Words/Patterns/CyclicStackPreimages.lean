/- GID: D5/S1/Words/Patterns/CyclicStackPreimages
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/CyclicStackPreimages
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [D5/S1/Words/Patterns/CyclicStackPreimagesFinalLow]
   utility: none
   digest: Exact even and odd fibre cardinalities for the consecutive cyclic stack map. -/

import D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow

/-! # Exact consecutive cyclic-stack fibre cardinalities -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Patterns.CyclicStackPreimages

private lemma successful_even_eq_candidate {m : ℕ} (hm : 0 < m) {input : List ℕ}
    (houtput : cyclicStackSort input = target (2 * m)) :
    input = candidate m m m := by
  have hhalf : 2 * m / 2 = m := by
    rw [Nat.mul_comm, Nat.mul_div_left m (by omega : 0 < 2)]
  have hgappedN := successful_gapped (n := 2 * m) (by omega) houtput
  have hgapped : Gapped m input := by simpa only [hhalf] using hgappedN
  have hlowsPair : (lowEntries m input).Pairwise (fun x y => x < y) := by
    simpa only [hhalf] using successful_lows_pairwise hgappedN houtput
  have hperm : input.Perm (List.range' 1 (m + m)) := by
    simpa [show 2 * m = m + m by omega] using success_perm_range houtput
  have hlows : lowEntries m input = List.range' 1 m :=
    successful_low_entries hperm hlowsPair
  have hdata := gapped_filters_slots hgapped
  have hhighLen : (highEntries m input).length = m := successful_high_length hperm
  have hslotLen : (gapSlots m input).length =
      ((gapSlots m input).filterMap id).length := by
    rw [hdata.2.1, hdata.2.2, hlows]
    simp [hhighLen]
  have hslots : gapSlots m input = (List.range' 1 m).map some := by
    rw [options_all_some hslotLen, hdata.2.2, hlows]
  have hfilled : FilledUntilLast (gapSlots m input) := by
    rw [hslots]
    exact filledUntilLast_map_some _
  have hfilledN : FilledUntilLast (gapSlots (2 * m / 2) input) := by
    simpa only [hhalf] using hfilled
  have hhighPair : (highEntries m input).Pairwise (fun x y => x < y) := by
    simpa only [hhalf] using
      successful_highs_of_filled_until_last hgappedN hfilledN houtput
  have hhighs : highEntries m input = List.range' (m + 1) m :=
    successful_high_entries hperm hhighPair
  calc
    input = assembleGaps (highEntries m input) (gapSlots m input) := hdata.1.symm
    _ = assembleGaps (List.range' (m + 1) m) (candidateSlots m 0 m) := by
      rw [hhighs, hslots, candidateSlots_even]
    _ = candidate m m m := (candidate_eq_assemble m m m).symm

private lemma successful_odd_eq_candidate {m : ℕ} (hm : 0 < m) {input : List ℕ}
    (houtput : cyclicStackSort input = target (2 * m + 1)) :
    ∃ omitted < m + 1, input = candidate m (m + 1) omitted := by
  have hhalf : (2 * m + 1) / 2 = m := by
    rw [Nat.add_comm, Nat.add_mul_div_left 1 m (by omega : 0 < 2)]
    simp
  have hgappedN := successful_gapped (n := 2 * m + 1) (by omega) houtput
  have hgapped : Gapped m input := by simpa only [hhalf] using hgappedN
  have hlowsPair : (lowEntries m input).Pairwise (fun x y => x < y) := by
    simpa only [hhalf] using successful_lows_pairwise hgappedN houtput
  have hperm : input.Perm (List.range' 1 (m + (m + 1))) := by
    simpa [show 2 * m + 1 = m + (m + 1) by omega] using success_perm_range houtput
  have hlows : lowEntries m input = List.range' 1 m :=
    successful_low_entries hperm hlowsPair
  have hdata := gapped_filters_slots hgapped
  have hhighLen : (highEntries m input).length = m + 1 := successful_high_length hperm
  have hslotLen : (gapSlots m input).length = (List.range' 1 m).length + 1 := by
    rw [hdata.2.1, hhighLen]
    simp
  have hslotFilter : (gapSlots m input).filterMap id = List.range' 1 m := by
    rw [hdata.2.2, hlows]
  obtain ⟨omitted, homitted, hslots⟩ := options_one_none hslotFilter hslotLen
  have homitted' : omitted < m + 1 := by simpa using homitted
  have hhighs : highEntries m input = List.range' (m + 1) (m + 1) := by
    by_cases hfinal : omitted = m
    · subst omitted
      have hfilled : FilledUntilLast (gapSlots m input) := by
        rw [hslots]
        simpa using filledUntilLast_insertNone_last (List.range' 1 m)
      have hfilledN : FilledUntilLast (gapSlots ((2 * m + 1) / 2) input) := by
        simpa only [hhalf] using hfilled
      exact successful_high_entries hperm
        (by simpa only [hhalf] using
          successful_highs_of_filled_until_last hgappedN hfilledN houtput)
    · have homittedLt : omitted < m := by omega
      have hends : EndsWithLow m input := by
        rw [← hdata.1, hslots]
        apply assemble_insert_none_ends (by simpa using hhighLen) (by simpa using homittedLt)
        intro low hmem
        rw [List.mem_range'] at hmem
        obtain ⟨i, hi, rfl⟩ := hmem
        omega
      have hendsN : EndsWithLow ((2 * m + 1) / 2) input := by
        simpa only [hhalf] using hends
      have hglobal := successful_high_entries_final_low hgappedN hendsN houtput
      simpa only [hhalf, show 2 * m + 1 - m = m + 1 by omega] using hglobal
  refine ⟨omitted, homitted', ?_⟩
  calc
    input = assembleGaps (highEntries m input) (gapSlots m input) := hdata.1.symm
    _ = assembleGaps (List.range' (m + 1) (m + 1))
        (candidateSlots omitted 0 (m + 1)) := by
      rw [hhighs, hslots, candidateSlots_odd m omitted homitted']
    _ = candidate m (m + 1) omitted :=
      (candidate_eq_assemble m (m + 1) omitted).symm

private lemma fibre_nodup (n : ℕ) : (fibre n).Nodup := by
  unfold fibre
  exact (List.nodup_permutations _ List.nodup_range').filter _

/-- Zhan--Bie Conjectures 3 and 4: for every `m ≥ 2`, the full fibre over
the target of size `2m` has one element, while the full fibre over the target
of size `2m+1` has `m+1` elements. -/
theorem zhan_bie_conjectures_3_4 (m : ℕ) (hm : 2 ≤ m) :
    (fibre (2 * m)).length = 1 ∧ (fibre (2 * m + 1)).length = m + 1 := by
  have hevenSubset : fibre (2 * m) ⊆ [candidate m m m] := by
    intro input hinput
    have houtput : cyclicStackSort input = target (2 * m) := by
      simpa [fibre] using (List.mem_filter.mp hinput).2
    simp [successful_even_eq_candidate (by omega) houtput]
  have hevenUpper := (fibre_nodup (2 * m)).length_le_of_subset hevenSubset
  have hevenLower := evenCandidate_lower_bound m (by omega)
  have hoddSubset : fibre (2 * m + 1) ⊆
      (List.range (m + 1)).map (candidate m (m + 1)) := by
    intro input hinput
    have houtput : cyclicStackSort input = target (2 * m + 1) := by
      simpa [fibre] using (List.mem_filter.mp hinput).2
    obtain ⟨omitted, homitted, rfl⟩ := successful_odd_eq_candidate (by omega) houtput
    apply List.mem_map.mpr
    exact ⟨omitted, by simpa using homitted, rfl⟩
  have hoddUpper := (fibre_nodup (2 * m + 1)).length_le_of_subset hoddSubset
  have hoddLower := oddCandidate_lower_bound m (by omega)
  have hevenUpper' : (fibre (2 * m)).length ≤ 1 := by simpa using hevenUpper
  have hoddUpper' : (fibre (2 * m + 1)).length ≤ m + 1 := by
    simpa using hoddUpper
  constructor
  · omega
  · omega


end D5.S1.Words.Patterns.CyclicStackPreimages
