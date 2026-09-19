/- GID: D5/S1/Words/Patterns/CyclicStackPreimagesCandidates
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/CyclicStackPreimagesCandidates
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Candidate fibres and lower bounds for the consecutive cyclic stack map. -/

import D5.S1.Words.Patterns.CyclicStackPreimagesCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Patterns.CyclicStackPreimages

/-- The complete fibre over `target n`, filtered from all permutations of
`(1,...,n)`. -/
def fibre (n : ℕ) : List (List ℕ) :=
  (List.range' 1 n).permutations.filter fun input =>
    decide (cyclicStackSort input = target n)

private def highStack (m : ℕ) : ℕ → List ℕ
  | 0 => []
  | i + 1 => (m + i + 1) :: highStack m i

def gapLow (omitted i : ℕ) : ℕ :=
  if i < omitted then i + 1 else i

/-- Input following the first high, with `remaining` later highs and therefore
`remaining + 1` gaps still to decide. -/
def candidateTail (m omitted i : ℕ) : ℕ → List ℕ
  | 0 => if i = omitted then [] else [gapLow omitted i]
  | remaining + 1 =>
      (if i = omitted then [] else [gapLow omitted i]) ++
        (m + i + 2) :: candidateTail m omitted (i + 1) remaining

def candidate (m highCount omitted : ℕ) : List ℕ :=
  match highCount with
  | 0 => []
  | remaining + 1 => (m + 1) :: candidateTail m omitted 0 remaining

private def decodeOmittedGap (m : ℕ) : ℕ → List ℕ → ℕ
  | i, [] => i
  | i, [_] => i
  | i, _ :: next :: rest =>
      if m < next then i else decodeOmittedGap m (i + 1) rest

private def candidateLows (omitted i : ℕ) : ℕ → List ℕ
  | 0 => []
  | gapCount + 1 =>
      (if i = omitted then [] else [gapLow omitted i]) ++
        candidateLows omitted (i + 1) gapCount

private lemma highStack_eq (m i : ℕ) :
    highStack m i = (List.range' (m + 1) i).reverse := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [highStack, List.range'_1_concat, List.reverse_append, ih]
      simp only [List.reverse_singleton, List.singleton_append]
      congr 1
      omega

private lemma drain_next_high (m i : ℕ) :
    drain (m + i + 1) (highStack m i) = ([], highStack m i) := by
  cases i with
  | zero => rfl
  | succ i =>
      cases i with
      | zero => rfl
      | succ i =>
          have hf : forbidden (m + (i + 1 + 1) + 1) (m + (i + 1) + 1)
              (m + i + 1) = false := by
            simp [forbidden]
          simp [highStack, drain, hf]

private lemma drain_low (m i low : ℕ) (_hlow : low ≤ m) :
    drain low (highStack m i) = ([], highStack m i) := by
  cases i with
  | zero => rfl
  | succ i =>
      cases i with
      | zero => rfl
      | succ i =>
          have hf : forbidden low (m + (i + 1) + 1) (m + i + 1) = false := by
            simp [forbidden]
            omega
          simp [highStack, drain, hf]

private lemma drain_pending_low (m i low : ℕ) (hlow : low ≤ m) :
    drain (m + i + 2) (low :: highStack m (i + 1)) =
      ([low], highStack m (i + 1)) := by
  have ht : forbidden (m + i + 2) low (m + i + 1) = true := by
    simp [forbidden]
    omega
  have hd : drain (m + i + 2) ((m + i + 1) :: highStack m i) =
      ([], (m + i + 1) :: highStack m i) := by
    simpa only [highStack, Nat.add_assoc] using drain_next_high m (i + 1)
  simp [highStack, drain, ht, hd]

private lemma candidateTail_process (m omitted i remaining : ℕ)
    (hlows : ∀ j, i ≤ j → j ≤ i + remaining → j ≠ omitted → gapLow omitted j ≤ m) :
    process (candidateTail m omitted i remaining) (highStack m (i + 1)) =
      candidateLows omitted i (remaining + 1) ++ highStack m (i + remaining + 1) := by
  induction remaining generalizing i with
  | zero =>
      by_cases hi : i = omitted
      · simp [candidateTail, candidateLows, hi, process]
      · have hlow := hlows i (by omega) (by omega) hi
        simp [candidateTail, candidateLows, hi, process, drain_low, hlow]
  | succ remaining ih =>
      have hnext : ∀ j, i + 1 ≤ j → j ≤ i + 1 + remaining → j ≠ omitted →
          gapLow omitted j ≤ m := by
        intro j hj hbound hne
        exact hlows j (by omega) (by omega) hne
      by_cases hi : i = omitted
      · subst i
        rw [candidateTail, candidateLows]
        simp
        change process ((m + omitted + 2) ::
            candidateTail m omitted (omitted + 1) remaining) (highStack m (omitted + 1)) =
          candidateLows omitted (omitted + 1) (remaining + 1) ++
            highStack m (omitted + (remaining + 1) + 1)
        rw [process]
        have hd : drain (m + omitted + 2) (highStack m (omitted + 1)) =
            ([], highStack m (omitted + 1)) := by
          simpa only [Nat.add_assoc] using drain_next_high m (omitted + 1)
        rw [hd]
        simp only [List.nil_append]
        change process (candidateTail m omitted (omitted + 1) remaining)
            (highStack m (omitted + 2)) = _
        rw [ih (i := omitted + 1) hnext]
        congr 2
        all_goals omega
      · have hlow := hlows i (by omega) (by omega) hi
        rw [candidateTail, candidateLows]
        simp [hi]
        change process (gapLow omitted i :: (m + i + 2) ::
            candidateTail m omitted (i + 1) remaining) (highStack m (i + 1)) =
          gapLow omitted i ::
            (candidateLows omitted (i + 1) (remaining + 1) ++
              highStack m (i + (remaining + 1) + 1))
        rw [process, drain_low _ _ _ hlow]
        simp only [List.nil_append]
        rw [process, drain_pending_low _ _ _ hlow]
        simp only [List.cons_append, List.nil_append]
        change gapLow omitted i ::
            process (candidateTail m omitted (i + 1) remaining) (highStack m (i + 2)) = _
        rw [ih (i := i + 1) hnext]
        congr 1
        rw [List.append_right_inj]
        congr 1
        omega

private lemma candidateLows_append (omitted i left right : ℕ) :
    candidateLows omitted i (left + right) =
      candidateLows omitted i left ++ candidateLows omitted (i + left) right := by
  induction left generalizing i with
  | zero => simp [candidateLows]
  | succ left ih =>
      rw [Nat.succ_add, candidateLows, candidateLows, ih]
      simp only [List.append_assoc]
      congr 1
      rw [List.append_right_inj]
      congr 1
      omega

private lemma decode_candidate_aux (m omitted i remaining : ℕ)
    (hleft : i ≤ omitted) (hright : omitted ≤ i + remaining)
    (hend : i + remaining = m) :
    decodeOmittedGap m i
      ((m + i + 1) :: candidateTail m omitted i remaining) = omitted := by
  induction remaining generalizing i with
  | zero =>
      have hi : i = omitted := by omega
      subst omitted
      simp [candidateTail, decodeOmittedGap]
  | succ remaining ih =>
      by_cases hi : i = omitted
      · subst omitted
        simp [candidateTail, decodeOmittedGap]
        omega
      · have hlt : i < omitted := by omega
        have hgap : gapLow omitted i = i + 1 := by simp [gapLow, hlt]
        rw [candidateTail, if_neg hi]
        simp only [hgap, List.singleton_append, decodeOmittedGap]
        rw [if_neg (by omega : ¬m < i + 1)]
        apply ih (i := i + 1) <;> omega

private lemma decode_odd_candidate (m omitted : ℕ) (homitted : omitted < m + 1) :
    decodeOmittedGap m 0 (candidate m (m + 1) omitted) = omitted := by
  unfold candidate
  exact decode_candidate_aux m omitted 0 m (by omega) (by omega) (by omega)

private lemma oddCandidate_injective (m : ℕ) :
    Function.Injective fun omitted : Fin (m + 1) =>
      candidate m (m + 1) omitted.val := by
  intro a b hab
  apply Fin.ext
  have := congrArg (decodeOmittedGap m 0) hab
  simpa only [decode_odd_candidate m a.val a.isLt,
    decode_odd_candidate m b.val b.isLt] using this

private lemma candidateLows_before (omitted i count : ℕ) (h : i + count ≤ omitted) :
    candidateLows omitted i count = List.range' (i + 1) count := by
  induction count generalizing i with
  | zero => rfl
  | succ count ih =>
      have hi : i < omitted := by omega
      rw [candidateLows, if_neg (by omega : i ≠ omitted), gapLow, if_pos hi,
        List.range'_succ]
      simp only [List.singleton_append]
      congr 1
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (i := i + 1) (by omega)

private lemma candidateLows_after (omitted i count : ℕ) (h : omitted < i) :
    candidateLows omitted i count = List.range' i count := by
  induction count generalizing i with
  | zero => rfl
  | succ count ih =>
      rw [candidateLows, if_neg (by omega : i ≠ omitted), gapLow, if_neg (by omega : ¬i < omitted),
        List.range'_succ]
      simp only [List.singleton_append]
      congr 1
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (i := i + 1) (by omega)

private lemma candidateLows_even (m : ℕ) :
    candidateLows m 0 m = List.range' 1 m := by
  simpa using candidateLows_before m 0 m (by omega)

private lemma candidateLows_odd (m omitted : ℕ) (homitted : omitted < m + 1) :
    candidateLows omitted 0 (m + 1) = List.range' 1 m := by
  have hsplit := candidateLows_append omitted 0 omitted (m + 1 - omitted)
  rw [Nat.add_sub_of_le (by omega : omitted ≤ m + 1)] at hsplit
  rw [hsplit, candidateLows_before omitted 0 omitted (by omega)]
  have htail : candidateLows omitted omitted (m + 1 - omitted) =
      List.range' (omitted + 1) (m - omitted) := by
    have hcount : m + 1 - omitted = (m - omitted) + 1 := by omega
    rw [hcount, candidateLows, if_pos rfl, List.nil_append]
    exact candidateLows_after omitted (omitted + 1) (m - omitted) (by omega)
  rw [show candidateLows omitted (0 + omitted) (m + 1 - omitted) =
      List.range' (omitted + 1) (m - omitted) by simpa using htail]
  have hadd : omitted + (m - omitted) = m := Nat.add_sub_of_le (by omega)
  simpa only [Nat.zero_add, Nat.add_comm, hadd] using
    (List.range'_append_1 (s := 1) (m := omitted) (n := m - omitted))

private lemma candidate_process (m highCount omitted : ℕ) (hcount : 0 < highCount)
    (hlows : ∀ j < highCount, j ≠ omitted → gapLow omitted j ≤ m) :
    cyclicStackSort (candidate m highCount omitted) =
      candidateLows omitted 0 highCount ++ highStack m highCount := by
  obtain ⟨remaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : highCount ≠ 0)
  have htail := candidateTail_process m omitted 0 remaining (by
    intro j hj hbound hne
    apply hlows j <;> omega)
  simpa [cyclicStackSort, candidate, process, drain, highStack] using htail

private lemma evenCandidate_maps_to_target (m : ℕ) (hm : 0 < m) :
    cyclicStackSort (candidate m m m) = target (2 * m) := by
  rw [candidate_process m m m hm (by
    intro j hj _
    simp [gapLow, if_pos hj]
    omega), candidateLows_even, highStack_eq]
  have hhalf : 2 * m / 2 = m := by
    rw [Nat.mul_comm, Nat.mul_div_left m (by omega : 0 < 2)]
  unfold target
  simp only [hhalf]
  rw [show 2 * m - m = m by omega]

private lemma oddCandidate_maps_to_target (m omitted : ℕ) (hm : 0 < m)
    (homitted : omitted < m + 1) :
    cyclicStackSort (candidate m (m + 1) omitted) = target (2 * m + 1) := by
  rw [candidate_process m (m + 1) omitted (by omega) (by
    intro j hj hne
    unfold gapLow
    split <;> omega), candidateLows_odd m omitted homitted, highStack_eq]
  have hhalf : (2 * m + 1) / 2 = m := by
    rw [Nat.add_comm, Nat.add_mul_div_left 1 m (by omega : 0 < 2)]
    simp
  unfold target
  simp only [hhalf]
  rw [show 2 * m + 1 - m = m + 1 by omega]

lemma target_perm_range (n : ℕ) :
    let _sourceObject := cyclicStackSourceWord
    (target n).Perm (List.range' 1 n) := by
  let m := n / 2
  have hm : m ≤ n := Nat.div_le_self n 2
  have hreverse : (List.range' (m + 1) (n - m)).reverse.Perm
      (List.range' (m + 1) (n - m)) := List.reverse_perm _
  have happ := hreverse.append_left (List.range' 1 m)
  have hrange : List.range' 1 m ++ List.range' (m + 1) (n - m) =
      List.range' 1 n := by
    rw [show m + 1 = 1 + m by omega, List.range'_append_1]
    congr 1
    omega
  simpa only [target, m] using happ.trans (List.Perm.of_eq hrange)

private lemma evenCandidate_mem_fibre (m : ℕ) (hm : 0 < m) :
    candidate m m m ∈ fibre (2 * m) := by
  have hmaps := evenCandidate_maps_to_target m hm
  have hpermOutput := process_perm (candidate m m m) []
  have hp : (target (2 * m)).Perm (candidate m m m) := by
    have hp0 : (cyclicStackSort (candidate m m m)).Perm (candidate m m m) := by
      simpa only [cyclicStackSort, List.append_nil] using hpermOutput
    rw [hmaps] at hp0
    exact hp0
  have hperm : (candidate m m m).Perm (List.range' 1 (2 * m)) :=
    hp.symm.trans (target_perm_range (2 * m))
  simp [fibre, List.mem_permutations.mpr hperm, hmaps]

private lemma oddCandidate_mem_fibre (m omitted : ℕ) (hm : 0 < m)
    (homitted : omitted < m + 1) :
    candidate m (m + 1) omitted ∈ fibre (2 * m + 1) := by
  have hmaps := oddCandidate_maps_to_target m omitted hm homitted
  have hpermOutput := process_perm (candidate m (m + 1) omitted) []
  have hp : (target (2 * m + 1)).Perm (candidate m (m + 1) omitted) := by
    have hp0 : (cyclicStackSort (candidate m (m + 1) omitted)).Perm
        (candidate m (m + 1) omitted) := by
      simpa only [cyclicStackSort, List.append_nil] using hpermOutput
    rw [hmaps] at hp0
    exact hp0
  have hperm : (candidate m (m + 1) omitted).Perm (List.range' 1 (2 * m + 1)) :=
    hp.symm.trans (target_perm_range (2 * m + 1))
  simp [fibre, List.mem_permutations.mpr hperm, hmaps]

private lemma oddCandidate_nodup (m : ℕ) :
    ((List.range (m + 1)).map (candidate m (m + 1))).Nodup := by
  apply List.Nodup.map_on _ List.nodup_range
  intro a ha b hb hab
  simp only [List.mem_range] at ha hb
  have hdecoded := congrArg (decodeOmittedGap m 0) hab
  simpa only [decode_odd_candidate m a ha, decode_odd_candidate m b hb] using hdecoded

lemma oddCandidate_lower_bound (m : ℕ) (hm : 0 < m) :
    let _sourceObject := cyclicStackSourceWord
    m + 1 ≤ (fibre (2 * m + 1)).length := by
  have hsubset : (List.range (m + 1)).map (candidate m (m + 1)) ⊆
      fibre (2 * m + 1) := by
    intro word hword
    rw [List.mem_map] at hword
    obtain ⟨omitted, homitted, rfl⟩ := hword
    exact oddCandidate_mem_fibre m omitted hm (by simpa using homitted)
  simpa using (oddCandidate_nodup m).length_le_of_subset hsubset

lemma evenCandidate_lower_bound (m : ℕ) (hm : 0 < m) :
    let _sourceObject := cyclicStackSourceWord
    1 ≤ (fibre (2 * m)).length := by
  exact List.length_pos_of_mem (evenCandidate_mem_fibre m hm)

private def candidates (n : ℕ) : List (List ℕ) :=
  if Even n then [candidate (n / 2) (n - n / 2) (n - n / 2)]
  else (List.range (n - n / 2)).map (candidate (n / 2) (n - n / 2))

end D5.S1.Words.Patterns.CyclicStackPreimages
