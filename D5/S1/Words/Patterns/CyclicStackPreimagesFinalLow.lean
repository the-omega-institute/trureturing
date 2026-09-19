/- GID: D5/S1/Words/Patterns/CyclicStackPreimagesFinalLow
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/CyclicStackPreimagesFinalLow
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Final-low residual-stack classification for cyclic-stack preimages. -/

import D5.S1.Words.Patterns.CyclicStackPreimagesInvariants

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Patterns.CyclicStackPreimages

def EndsWithLow (m : ℕ) (input : List ℕ) : Prop :=
  ∃ pre low, input = pre ++ [low] ∧ low ≤ m

private lemma successful_run_final_low {n : ℕ} {suffix : List ℕ}
    (hgapped : Gapped (n / 2) suffix) (hlast : EndsWithLow (n / 2) suffix) :
    ∀ (prior : List ℕ) (pending : Option ℕ),
      (∀ high ∈ prior, n / 2 < high) →
      (∀ low, pending = some low → low ≤ n / 2) →
      (pending.isSome → prior ≠ []) →
      (process suffix (pending.toList ++ prior)).Sublist (target n) →
      ∃ finalLow, finalLow ≤ n / 2 ∧
        (run suffix (pending.toList ++ prior)).2 =
          finalLow :: (highEntries (n / 2) suffix).reverse ++ prior := by
  induction hgapped with
  | nil => simp [EndsWithLow] at hlast
  | @last high hhigh =>
      obtain ⟨pre, low, heq, hlow⟩ := hlast
      cases pre with
      | nil => simp at heq; omega
      | cons first pre => simp at heq
  | @empty high next rest hhigh tail ih =>
      intro prior pending hprior hpending hpendingPrior houtput
      obtain ⟨finalLow, hfinalMem, hfinalLow⟩ :
          ∃ finalLow ∈ next :: rest, finalLow ≤ n / 2 := by
        obtain ⟨pre, finalLow, heq, hfinalLow⟩ := hlast
        refine ⟨finalLow, ?_, hfinalLow⟩
        have hmem : finalLow ∈ high :: next :: rest := by rw [heq]; simp
        apply (List.mem_cons.mp hmem).resolve_left
        omega
      have htailLast : EndsWithLow (n / 2) (next :: rest) := by
        obtain ⟨pre, finalLow, heq, hfinalLow⟩ := hlast
        cases pre with
        | nil => simp at heq
        | cons first pre =>
            simp only [List.cons_append, List.cons.injEq] at heq
            exact ⟨pre, finalLow, heq.2, hfinalLow⟩
      have hdrain : drain high (pending.toList ++ prior) =
          (pending.toList, prior) := by
        cases pending with
        | none =>
            simp only [Option.toList_none, List.nil_append]
            cases prior with
            | nil => rfl
            | cons top below =>
                have htop := hprior top (by simp)
                exact drain_high_while_low_remains htop hfinalLow hfinalMem houtput
        | some low =>
            simp only [Option.toList_some, List.singleton_append]
            cases prior with
            | nil => exact (hpendingPrior (by simp) rfl).elim
            | cons top below =>
                have hlow := hpending low rfl
                have htop := hprior top (by simp)
                exact pending_low_drains_only_low_while_low_remains hlow htop hhigh
                  hfinalLow hfinalMem houtput
      have htailOutput : (process (next :: rest) (high :: prior)).Sublist (target n) := by
        rw [process, hdrain] at houtput
        have hsub := List.sublist_append_right pending.toList
          (process (next :: rest) (high :: prior))
        exact hsub.trans houtput
      have hnewPrior : ∀ value ∈ high :: prior, n / 2 < value := by
        intro value hmem
        by_cases hEq : value = high
        · omega
        · exact hprior value ((List.mem_cons.mp hmem).resolve_left hEq)
      obtain ⟨last, hlastLow, hrun⟩ := ih htailLast (high :: prior) none hnewPrior
        (by simp) (by simp) (by simpa using htailOutput)
      refine ⟨last, hlastLow, ?_⟩
      rw [run, hdrain]
      change (run (next :: rest) (high :: prior)).2 = _
      have hrun' : (run (next :: rest) (high :: prior)).2 =
          last :: (highEntries (n / 2) (next :: rest)).reverse ++ high :: prior := by
        simpa using hrun
      rw [hrun']
      simp [highEntries, hhigh, List.reverse_cons, List.append_assoc]
  | @filled high low rest hhigh hlow tail ih =>
      intro prior pending hprior hpending hpendingPrior houtput
      obtain ⟨finalLow, hfinalMem, hfinalLow⟩ :
          ∃ finalLow ∈ low :: rest, finalLow ≤ n / 2 := by
        obtain ⟨pre, finalLow, heq, hfinalLow⟩ := hlast
        refine ⟨finalLow, ?_, hfinalLow⟩
        have hmem : finalLow ∈ high :: low :: rest := by rw [heq]; simp
        apply (List.mem_cons.mp hmem).resolve_left
        omega
      have hdrain : drain high (pending.toList ++ prior) =
          (pending.toList, prior) := by
        cases pending with
        | none =>
            simp only [Option.toList_none, List.nil_append]
            cases prior with
            | nil => rfl
            | cons top below =>
                have htop := hprior top (by simp)
                exact drain_high_while_low_remains htop hfinalLow hfinalMem houtput
        | some previousLow =>
            simp only [Option.toList_some, List.singleton_append]
            cases prior with
            | nil => exact (hpendingPrior (by simp) rfl).elim
            | cons top below =>
                have hpreviousLow := hpending previousLow rfl
                have htop := hprior top (by simp)
                exact pending_low_drains_only_low_while_low_remains hpreviousLow htop hhigh
                  hfinalLow hfinalMem houtput
      have hafterHigh : (process (low :: rest) (high :: prior)).Sublist (target n) := by
        rw [process, hdrain] at houtput
        have hsub := List.sublist_append_right pending.toList
          (process (low :: rest) (high :: prior))
        exact hsub.trans houtput
      have hlowDrain := drain_low_over_high hlow hhigh hafterHigh
      have hafterLow : (process rest (low :: high :: prior)).Sublist (target n) := by
        simpa only [process, hlowDrain, List.nil_append] using hafterHigh
      have hnewPrior : ∀ value ∈ high :: prior, n / 2 < value := by
        intro value hmem
        by_cases hEq : value = high
        · omega
        · exact hprior value ((List.mem_cons.mp hmem).resolve_left hEq)
      cases rest with
      | nil =>
          refine ⟨low, hlow, ?_⟩
          rw [run, hdrain, run, hlowDrain]
          simp [run, highEntries, hhigh, show ¬ n / 2 < low by omega]
      | cons next rest =>
          have hrestLast : EndsWithLow (n / 2) (next :: rest) := by
            obtain ⟨pre, finalLow, heq, hfinalLow⟩ := hlast
            cases pre with
            | nil => simp at heq
            | cons first pre =>
                cases pre with
                | nil => simp at heq
                | cons second pre =>
                    simp only [List.cons_append, List.cons.injEq] at heq
                    exact ⟨pre, finalLow, heq.2.2, hfinalLow⟩
          obtain ⟨last, hlastLow, hrun⟩ := ih hrestLast (high :: prior) (some low)
            hnewPrior (by intro value hEq; cases hEq; exact hlow) (by simp)
            (by simpa using hafterLow)
          refine ⟨last, hlastLow, ?_⟩
          rw [run, hdrain, run, hlowDrain]
          change (run (next :: rest) (low :: high :: prior)).2 = _
          have hrun' : (run (next :: rest) (low :: high :: prior)).2 =
              last :: (highEntries (n / 2) (next :: rest)).reverse ++ high :: prior := by
            simpa using hrun
          rw [hrun']
          simp [highEntries, hhigh, show ¬ n / 2 < low by omega,
            List.reverse_cons, List.append_assoc]

lemma successful_high_entries_final_low {n : ℕ} {input : List ℕ}
    (hgapped : Gapped (n / 2) input) (hlast : EndsWithLow (n / 2) input)
    (houtput : cyclicStackSort input = target n) :
    highEntries (n / 2) input = List.range' (n / 2 + 1) (n - n / 2) := by
  have hprocess : (process input []).Sublist (target n) := by
    change (cyclicStackSort input).Sublist (target n)
    rw [houtput]
  obtain ⟨last, hlastLow, hrun⟩ := successful_run_final_low hgapped hlast [] none
    (by simp) (by simp) (by simp) (by simpa using hprocess)
  have hstackSub : (run input []).2.Sublist (target n) := by
    have hsub := List.sublist_append_right (run input []).1 (run input []).2
    rw [← process_eq_run] at hsub
    exact hsub.trans hprocess
  have hhighReverseSub : (highEntries (n / 2) input).reverse.Sublist (target n) := by
    have hrun' : (run input []).2 = last :: (highEntries (n / 2) input).reverse := by
      simpa using hrun
    rw [hrun'] at hstackSub
    exact (List.sublist_cons_self last _).trans hstackSub
  have hfilteredSub := hhighReverseSub.filter (fun x => decide (n / 2 < x))
  have hleft : highEntries (n / 2) (highEntries (n / 2) input).reverse =
      (highEntries (n / 2) input).reverse := by
    unfold highEntries
    apply List.filter_eq_self.mpr
    intro x hx
    rw [List.mem_reverse] at hx
    have hx' := (List.mem_filter.mp hx).2
    exact hx'
  change (highEntries (n / 2) (highEntries (n / 2) input).reverse).Sublist
    (highEntries (n / 2) (target n)) at hfilteredSub
  have htarget : highEntries (n / 2) (target n) =
      (List.range' (n / 2 + 1) (n - n / 2)).reverse := by
    unfold highEntries target
    rw [List.filter_append, List.filter_reverse]
    have hlow : (List.range' 1 (n / 2)).filter
        (fun x => decide (n / 2 < x)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro x hx
      rw [List.mem_range'] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      simp
      omega
    have hhigh : (List.range' (n / 2 + 1) (n - n / 2)).filter
        (fun x => decide (n / 2 < x)) = List.range' (n / 2 + 1) (n - n / 2) := by
      apply List.filter_eq_self.mpr
      intro x hx
      rw [decide_eq_true_eq]
      rw [List.mem_range'] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      omega
    rw [hlow, hhigh, List.nil_append]
  rw [hleft, htarget] at hfilteredSub
  have hp := (success_perm_range houtput).filter (fun x => decide (n / 2 < x))
  have hm : n / 2 + (n - n / 2) = n := Nat.add_sub_of_le (Nat.div_le_self n 2)
  change (highEntries (n / 2) input).Perm
    (highEntries (n / 2) (List.range' 1 n)) at hp
  have hrange : List.range' 1 n = List.range' 1 (n / 2 + (n - n / 2)) := by
    rw [hm]
  have hhighRange : highEntries (n / 2) (List.range' 1 (n / 2 + (n - n / 2))) =
      List.range' (n / 2 + 1) (n - n / 2) := by
    let m := n / 2
    let q := n - n / 2
    change highEntries m (List.range' 1 (m + q)) = List.range' (m + 1) q
    have hsplit : List.range' 1 (m + q) =
        List.range' 1 m ++ List.range' (m + 1) q := by
      simpa [Nat.add_comm] using
        (List.range'_append_1 (s := 1) (m := m) (n := q)).symm
    rw [hsplit, highEntries, List.filter_append]
    have hleft : (List.range' 1 m).filter (fun x => decide (m < x)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro x hx
      rw [List.mem_range'] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      simp
      omega
    have hright : (List.range' (m + 1) q).filter (fun x => decide (m < x)) =
        List.range' (m + 1) q := by
      apply List.filter_eq_self.mpr
      intro x hx
      rw [decide_eq_true_eq]
      rw [List.mem_range'] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      omega
    rw [hleft, hright, List.nil_append]
  rw [hrange, hhighRange] at hp
  have hlen : (highEntries (n / 2) input).reverse.length =
      ((List.range' (n / 2 + 1) (n - n / 2)).reverse).length := by
    simpa using hp.length_eq
  have heq := hfilteredSub.eq_of_length hlen
  simpa using congrArg List.reverse heq

private lemma assemble_map_some_ends {m : ℕ} {highs lows : List ℕ}
    (hlen : highs.length = lows.length) (hne : lows ≠ [])
    (hlow : ∀ low ∈ lows, low ≤ m) :
    EndsWithLow m (assembleGaps highs (lows.map some)) := by
  induction lows generalizing highs with
  | nil => exact (hne rfl).elim
  | cons low lows ih =>
      cases highs with
      | nil => simp at hlen
      | cons high highs =>
          have hlowHead := hlow low (by simp)
          cases lows with
          | nil =>
              have hhighsNil : highs = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
              subst highs
              exact ⟨[high], low, by simp [assembleGaps], hlowHead⟩
          | cons next rest =>
              have htail := ih (highs := highs) (by simpa using hlen) (by simp) (by
                intro value hmem
                exact hlow value (by simp [hmem]))
              obtain ⟨pre, low', heq, hlow'⟩ := htail
              refine ⟨high :: low :: pre, low', ?_, hlow'⟩
              simp only [assembleGaps, List.map_cons]
              have heq' : assembleGaps highs (some next :: List.map some rest) =
                  pre ++ [low'] := by
                simpa only [List.map_cons] using heq
              rw [heq']
              simp only [List.cons_append]

lemma assemble_insert_none_ends {m omitted : ℕ} {highs lows : List ℕ}
    (hlen : highs.length = lows.length + 1) (homitted : omitted < lows.length)
    (hlow : ∀ low ∈ lows, low ≤ m) :
    EndsWithLow m (assembleGaps highs (insertNone omitted lows)) := by
  induction lows generalizing highs omitted with
  | nil => simp at homitted
  | cons low lows ih =>
      cases highs with
      | nil => simp at hlen
      | cons high highs =>
          cases omitted with
          | zero =>
              simp only [insertNone, assembleGaps]
              have htail := assemble_map_some_ends (m := m) (highs := highs)
                (lows := low :: lows) (by simpa using hlen) (by simp) hlow
              have htail' : EndsWithLow m
                  (assembleGaps highs (some low :: lows.map some)) := by
                simpa only [List.map_cons] using htail
              obtain ⟨pre, low', heq, hlow'⟩ := htail'
              exact ⟨high :: pre, low', by simp [heq], hlow'⟩
          | succ omitted =>
              simp only [insertNone, assembleGaps]
              have htail := ih (highs := highs) (omitted := omitted) (by simpa using hlen)
                (by simpa using homitted) (by
                  intro value hmem
                  exact hlow value (by simp [hmem]))
              obtain ⟨pre, low', heq, hlow'⟩ := htail
              exact ⟨high :: low :: pre, low', by simp [heq], hlow'⟩

end D5.S1.Words.Patterns.CyclicStackPreimages
