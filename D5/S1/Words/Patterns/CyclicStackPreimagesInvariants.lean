/- GID: D5/S1/Words/Patterns/CyclicStackPreimagesInvariants
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/CyclicStackPreimagesInvariants
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Global gap decomposition and high-stack invariants for cyclic-stack preimages. -/

import D5.S1.Words.Patterns.CyclicStackPreimagesCandidates

/-! # Global cyclic-stack preimage invariants -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Patterns.CyclicStackPreimages

def lowEntries (m : ℕ) (input : List ℕ) : List ℕ :=
  input.filter fun x => decide (x ≤ m)

def highEntries (m : ℕ) (input : List ℕ) : List ℕ :=
  input.filter fun x => decide (m < x)

/-- A word split into chronological high entries, each followed by zero or one
low entry. This records exactly the gap structure relevant to the fibre. -/
inductive Gapped (m : ℕ) : List ℕ → Prop
  | nil : Gapped m []
  | last {high : ℕ} (hhigh : m < high) : Gapped m [high]
  | empty {high next : ℕ} {rest : List ℕ} (hhigh : m < high)
      (tail : Gapped m (next :: rest)) : Gapped m (high :: next :: rest)
  | filled {high low : ℕ} {rest : List ℕ} (hhigh : m < high)
      (hlow : low ≤ m) (tail : Gapped m rest) : Gapped m (high :: low :: rest)

def gapSlots (m : ℕ) : List ℕ → List (Option ℕ)
  | [] => []
  | [_] => [none]
  | _ :: next :: rest =>
      if next ≤ m then some next :: gapSlots m rest
      else none :: gapSlots m (next :: rest)

def assembleGaps : List ℕ → List (Option ℕ) → List ℕ
  | [], _ => []
  | high :: highs, [] => high :: assembleGaps highs []
  | high :: highs, none :: slots => high :: assembleGaps highs slots
  | high :: highs, some low :: slots => high :: low :: assembleGaps highs slots

private def assembleTail : List (Option ℕ) → List ℕ → List ℕ
  | [], highs => highs
  | none :: _, [] => []
  | some low :: _, [] => [low]
  | none :: slots, high :: highs => high :: assembleTail slots highs
  | some low :: slots, high :: highs => low :: high :: assembleTail slots highs

private lemma assembleGaps_nil_slots (highs : List ℕ) :
    assembleGaps highs [] = highs := by
  induction highs with
  | nil => rfl
  | cons high highs ih => simp [assembleGaps, ih]

private lemma assembleGaps_cons (high : ℕ) (highs : List ℕ)
    (slots : List (Option ℕ)) :
    assembleGaps (high :: highs) slots = high :: assembleTail slots highs := by
  induction highs generalizing high slots with
  | nil =>
      cases slots with
      | nil => rfl
      | cons slot slots => cases slot <;> rfl
  | cons next highs ih =>
      cases slots with
      | nil => simp [assembleGaps, assembleTail, assembleGaps_nil_slots]
      | cons slot slots =>
          cases slot <;> simp [assembleGaps, assembleTail, ih]

lemma gapped_filters_slots {m : ℕ} {input : List ℕ}
    (hgapped : Gapped m input) :
    assembleGaps (highEntries m input) (gapSlots m input) = input ∧
      (gapSlots m input).length = (highEntries m input).length ∧
      (gapSlots m input).filterMap id = lowEntries m input := by
  induction hgapped with
  | nil => simp [assembleGaps, gapSlots, highEntries, lowEntries]
  | @last high hhigh =>
      simp_all [assembleGaps, gapSlots, highEntries, lowEntries]
  | @empty high next rest hhigh tail ih =>
      have hnext : m < next := by
        cases tail with
        | last hnext => exact hnext
        | empty hnext _ => exact hnext
        | filled hnext _ _ => exact hnext
      have hnle : ¬next ≤ m := by omega
      have ihAssemble : assembleGaps
          (next :: (highEntries m rest)) (gapSlots m (next :: rest)) = next :: rest := by
        simpa [highEntries, hnext] using ih.1
      have ihLows : (gapSlots m (next :: rest)).filterMap id = lowEntries m rest := by
        simpa [lowEntries, hnle] using ih.2.2
      constructor
      · simp [gapSlots, highEntries, assembleGaps, hhigh, hnext, hnle]
        simpa only [highEntries] using ihAssemble
      · constructor
        · simp [gapSlots, highEntries, hhigh, hnext, hnle, ih.2.1]
        · simp [gapSlots, lowEntries, hhigh, hnext, hnle]
          change (gapSlots m (next :: rest)).filterMap id = lowEntries m rest
          exact ihLows
  | @filled high low rest hhigh hlow _ ih =>
      simp_all [gapSlots, highEntries, lowEntries, assembleGaps]

lemma success_perm_range {n : ℕ} {input : List ℕ}
    (houtput : cyclicStackSort input = target n) :
    input.Perm (List.range' 1 n) := by
  have hp : (cyclicStackSort input).Perm input := by
    simpa only [cyclicStackSort, List.append_nil] using process_perm input []
  rw [houtput] at hp
  have htarget : (target n).Perm (List.range' 1 n) := by
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
  exact hp.symm.trans htarget

private lemma success_entry_bounds {n x : ℕ} {input : List ℕ}
    (houtput : cyclicStackSort input = target n) (hx : x ∈ input) :
    1 ≤ x ∧ x < n + 1 := by
  have hp := success_perm_range houtput
  have : x ∈ List.range' 1 n := hp.mem_iff.mp hx
  rw [List.mem_range'] at this
  obtain ⟨i, hi, rfl⟩ := this
  omega

private lemma successful_head_high {n : ℕ} (hn : 2 ≤ n) {input : List ℕ}
    (houtput : cyclicStackSort input = target n) :
    ∃ high rest, input = high :: rest ∧ n / 2 < high := by
  let isLow : ℕ → Bool := fun x => decide (x ≤ n / 2)
  let pre := input.takeWhile isLow
  let suffix := input.dropWhile isLow
  have hnMemRange : n ∈ List.range' 1 n := by
    rw [List.mem_range']
    refine ⟨n - 1, by omega, ?_⟩
    omega
  have hnMem : n ∈ input := (success_perm_range houtput).mem_iff.mpr hnMemRange
  have hnHigh : ¬isLow n = true := by
    simp only [isLow, decide_eq_true_eq, not_le]
    omega
  have hsuffix : suffix ≠ [] := by
    intro hempty
    have hall := List.dropWhile_eq_nil_iff.mp hempty n hnMem
    exact hnHigh hall
  obtain ⟨high, rest, hsuffixEq⟩ : ∃ high rest, suffix = high :: rest := by
    cases hs : suffix with
    | nil => exact (hsuffix hs).elim
    | cons high rest => exact ⟨high, rest, rfl⟩
  have hhighNotLow : ¬isLow high := by
    have hlen : 0 < suffix.length := by simp [hsuffixEq]
    have hnot := List.dropWhile_get_zero_not isLow input hlen
    simpa only [suffix, hsuffixEq, List.get_eq_getElem, List.getElem_cons_zero] using hnot
  have hhigh : n / 2 < high := by
    simp only [isLow, Bool.not_eq_true, decide_eq_false_iff_not, not_le] at hhighNotLow
    exact hhighNotLow
  have hpre : ∀ low ∈ pre, low ≤ n / 2 := by
    intro low hlow
    have := List.mem_takeWhile_imp hlow
    simpa only [isLow, decide_eq_true_eq] using this
  have hsplit : input = pre ++ high :: rest := by
    rw [← hsuffixEq]
    simpa only [pre, suffix] using
      (List.takeWhile_append_dropWhile (p := isLow) (l := input)).symm
  have hpreNil : pre = [] := no_lows_before_first_high hpre hhigh (by
    simpa only [hsplit] using houtput)
  exact ⟨high, rest, by simpa only [hsplit, hpreNil, List.nil_append], hhigh⟩

private lemma no_high_low_low_factor {n high low₁ low₂ : ℕ}
    (hhigh : n / 2 < high) (hlow₁ : low₁ ≤ n / 2)
    (hlow₂ : low₂ ≤ n / 2) (hne : low₁ ≠ low₂)
    {pre rest input : List ℕ}
    (hinput : input = pre ++ high :: low₁ :: low₂ :: rest)
    (houtput : cyclicStackSort input = target n) : False := by
  let first := run pre []
  let step := drain high first.2
  have hsuffix : (process (low₁ :: low₂ :: rest) (high :: step.2)).Sublist
      (target n) := by
    unfold cyclicStackSort at houtput
    rw [hinput, process_append] at houtput
    simp only [process] at houtput
    change first.1 ++ (step.1 ++
      process (low₁ :: low₂ :: rest) (high :: step.2)) = target n at houtput
    have hsub := List.sublist_append_right (first.1 ++ step.1)
      (process (low₁ :: low₂ :: rest) (high :: step.2))
    simpa only [List.append_assoc, houtput] using hsub
  exact no_two_lows_after_high hlow₁ hlow₂ hne hhigh hsuffix

lemma successful_gapped {n : ℕ} (hn : 2 ≤ n) {input : List ℕ}
    (houtput : cyclicStackSort input = target n) :
    Gapped (n / 2) input := by
  obtain ⟨high, rest, rfl, hhigh⟩ := successful_head_high hn houtput
  have hnodup : (high :: rest).Nodup :=
    (success_perm_range houtput).nodup_iff.mpr List.nodup_range'
  have build : ∀ (pre suffix : List ℕ),
      high :: rest = pre ++ suffix →
      (∀ x ∈ suffix, x ≤ n / 2 ∨ n / 2 < x) →
      (∀ hne : suffix ≠ [], n / 2 < suffix.head hne) →
      Gapped (n / 2) suffix := by
    intro pre suffix
    induction suffix using List.twoStepInduction generalizing pre with
    | nil => intro _ _ _; exact Gapped.nil
    | singleton x =>
        intro _ _ hhead
        exact Gapped.last (by simpa using hhead (by simp))
    | cons_cons x y tail ih ihCons =>
        intro hwhole hall hhead
        have hx : n / 2 < x := by simpa using hhead (by simp)
        rcases hall y (by simp) with hy | hy
        · cases tail with
          | nil => exact Gapped.filled hx hy Gapped.nil
          | cons z zs =>
              have hzClass := hall z (by simp)
              have hz : n / 2 < z := by
                rcases hzClass with hzLow | hzHigh
                · have hne : y ≠ z := by
                    intro heq
                    subst z
                    have hsub : [y, y].Sublist (high :: rest) := by
                      rw [hwhole]
                      have htail : [y, y].Sublist ([y, y] ++ zs) :=
                        List.sublist_append_left [y, y] zs
                      have hprefix := htail.trans
                        (List.sublist_append_right (pre ++ [x]) ([y, y] ++ zs))
                      simpa [List.append_assoc] using hprefix
                    have := hsub.nodup hnodup
                    simp at this
                  exact (no_high_low_low_factor hx hy hzLow hne
                    (pre := pre) (rest := zs) (input := high :: rest) hwhole houtput).elim
                · exact hzHigh
              apply Gapped.filled hx hy
              apply ih (pre := pre ++ [x, y])
              · simpa [List.append_assoc] using hwhole
              · intro a ha
                exact hall a (by simp only [List.mem_cons] at ha ⊢; aesop)
              · intro _
                simpa using hz
        · apply Gapped.empty hx
          apply ihCons y (pre := pre ++ [x])
          · simpa [List.append_assoc] using hwhole
          · intro a ha
            exact hall a (by simp only [List.mem_cons] at ha ⊢; aesop)
          · intro _
            simpa using hy
  apply build [] (high :: rest) rfl
  · intro x hx
    have hb := success_entry_bounds houtput hx
    omega
  · intro _
    simpa using hhigh

private lemma filled_gap_low_precedes {n high low later : ℕ}
    (hhigh : n / 2 < high) (hlow : low ≤ n / 2)
    {pre rest input : List ℕ} (hgapped : Gapped (n / 2) rest)
    (hlaterMem : later ∈ lowEntries (n / 2) rest)
    (hinput : input = pre ++ high :: low :: rest)
    (houtput : cyclicStackSort input = target n) : low < later := by
  obtain ⟨next, tail, rfl⟩ : ∃ next tail, rest = next :: tail := by
    cases rest with
    | nil => simp [lowEntries] at hlaterMem
    | cons next tail => exact ⟨next, tail, rfl⟩
  have hnext : n / 2 < next := by
    cases hgapped with
    | last hnext => exact hnext
    | empty hnext _ => exact hnext
    | filled hnext _ _ => exact hnext
  have hlaterData : later ∈ next :: tail ∧ later ≤ n / 2 := by
    simpa only [lowEntries, List.mem_filter, decide_eq_true_eq] using hlaterMem
  have hlaterLow : later ≤ n / 2 := hlaterData.2
  have hlaterTail : later ∈ tail := by
    apply (List.mem_cons.mp hlaterData.1).resolve_left
    omega
  let first := run pre []
  let highStep := drain high first.2
  have hafterHigh : (process (low :: next :: tail) (high :: highStep.2)).Sublist
      (target n) := by
    unfold cyclicStackSort at houtput
    rw [hinput, process_append] at houtput
    simp only [process] at houtput
    change first.1 ++ (highStep.1 ++
      process (low :: next :: tail) (high :: highStep.2)) = target n at houtput
    have hsub := List.sublist_append_right (first.1 ++ highStep.1)
      (process (low :: next :: tail) (high :: highStep.2))
    simpa only [List.append_assoc, houtput] using hsub
  have hlowDrain := drain_low_over_high hlow hhigh hafterHigh
  have hafterLow : (process (next :: tail) (low :: high :: highStep.2)).Sublist
      (target n) := by
    simpa only [process, hlowDrain, List.nil_append] using hafterHigh
  have hshape := process_pending_low_while_low_remains hlow hhigh hnext hlaterLow
    hlaterTail hafterLow
  have hlaterOut : later ∈ process tail (next :: high :: highStep.2) := by
    apply (process_perm tail (next :: high :: highStep.2)).mem_iff.mpr
    exact List.mem_append_left _ hlaterTail
  have hpair : [low, later].Sublist
      (low :: process tail (next :: high :: highStep.2)) := by
    exact (List.singleton_sublist.mpr hlaterOut).cons_cons low
  rw [← hshape] at hpair
  have htargetLows : (target n).Pairwise fun earlier later =>
      earlier ≤ n / 2 → later ≤ n / 2 → earlier < later := by
    let m := n / 2
    let lows := List.range' 1 m
    let highs := (List.range' (m + 1) (n - m)).reverse
    have hlows : lows.Pairwise fun earlier later =>
        earlier ≤ m → later ≤ m → earlier < later := by
      apply (List.pairwise_lt_range' (s := 1) (n := m)).imp
      intro earlier later hlt _ _
      exact hlt
    have hhighs : highs.Pairwise fun earlier later =>
        earlier ≤ m → later ≤ m → earlier < later := by
      apply List.pairwise_of_forall_mem_list
      intro earlier hearlier
      simp only [highs, List.mem_reverse, List.mem_range'] at hearlier
      omega
    rw [show target n = lows ++ highs by rfl, List.pairwise_append]
    refine ⟨hlows, hhighs, ?_⟩
    intro earlier _ later hlater _ hlaterLow
    simp only [highs, List.mem_reverse, List.mem_range'] at hlater
    omega
  exact htargetLows.forall_sublist (hpair.trans hafterLow) hlow hlaterLow

lemma successful_lows_pairwise {n : ℕ} {input : List ℕ}
    (hgapped : Gapped (n / 2) input)
    (houtput : cyclicStackSort input = target n) :
    (lowEntries (n / 2) input).Pairwise (fun x y => x < y) := by
  have go : ∀ {suffix : List ℕ}, Gapped (n / 2) suffix →
      ∀ pre, input = pre ++ suffix →
        (lowEntries (n / 2) suffix).Pairwise (fun x y => x < y) := by
    intro suffix hs
    induction hs with
    | nil => intro _ _; simp [lowEntries]
    | @last high hhigh =>
        intro _ _
        simp [lowEntries, show ¬ high ≤ n / 2 by omega]
    | @empty high next rest hhigh tail ih =>
        intro pre hwhole
        have hnext : n / 2 < next := by
          cases tail with
          | last hnext => exact hnext
          | empty hnext _ => exact hnext
          | filled hnext _ _ => exact hnext
        simpa [lowEntries, hhigh, hnext] using ih (pre ++ [high]) (by
          simpa [List.append_assoc] using hwhole)
    | @filled high low rest hhigh hlow tail ih =>
        intro pre hwhole
        have htail := ih (pre ++ [high, low]) (by
          simpa [List.append_assoc] using hwhole)
        have hhighNot : ¬high ≤ n / 2 := by omega
        simp [lowEntries, hhighNot, hlow]
        constructor
        · intro later hlater hlaterLow
          apply filled_gap_low_precedes hhigh hlow tail
          · simp [lowEntries, hlater, hlaterLow]
          · exact hwhole
          · exact houtput
        · exact htail
  exact go hgapped [] (by simp)

def insertNone : ℕ → List ℕ → List (Option ℕ)
  | 0, lows => none :: lows.map some
  | _ + 1, [] => [none]
  | i + 1, low :: lows => some low :: insertNone i lows

lemma options_one_none {slots : List (Option ℕ)} {lows : List ℕ}
    (hfilter : slots.filterMap id = lows)
    (hlen : slots.length = lows.length + 1) :
    ∃ omitted < lows.length + 1, slots = insertNone omitted lows := by
  induction slots generalizing lows with
  | nil => simp at hlen
  | cons slot slots ih =>
      cases slot with
      | none =>
          change slots.filterMap id = lows at hfilter
          subst lows
          have htailLen : slots.length = (slots.filterMap id).length := by
            simp only [List.length_cons] at hlen
            omega
          refine ⟨0, by simp, ?_⟩
          change none :: slots = none :: (slots.filterMap id).map some
          apply congrArg (none :: ·)
          symm
          rw [List.map_filterMap_some_eq_filter_map_isSome, List.map_id]
          exact List.filter_eq_self.mpr (List.filterMap_length_eq_length.mp htailLen.symm)
      | some low =>
          change low :: slots.filterMap id = lows at hfilter
          subst lows
          simp only [List.length_cons] at hlen
          have htailLen : slots.length = (slots.filterMap id).length + 1 := by omega
          obtain ⟨omitted, homitted, hslots⟩ := ih rfl htailLen
          refine ⟨omitted + 1, ?_, ?_⟩
          · change omitted + 1 < (slots.filterMap id).length + 1 + 1
            omega
          change some low :: slots = some low :: insertNone omitted (slots.filterMap id)
          exact congrArg (some low :: ·) hslots

def candidateSlots (omitted i : ℕ) : ℕ → List (Option ℕ)
  | 0 => []
  | count + 1 =>
      (if i = omitted then none else some (gapLow omitted i)) ::
        candidateSlots omitted (i + 1) count

private lemma candidateSlots_append (omitted i left right : ℕ) :
    candidateSlots omitted i (left + right) =
      candidateSlots omitted i left ++ candidateSlots omitted (i + left) right := by
  induction left generalizing i with
  | zero => simp [candidateSlots]
  | succ left ih =>
      rw [Nat.succ_add, candidateSlots, candidateSlots]
      simp only [List.cons_append, List.cons.injEq, true_and]
      rw [show i + (left + 1) = (i + 1) + left by omega]
      exact ih (i := i + 1)

private lemma candidateSlots_before (omitted i count : ℕ)
    (h : i + count ≤ omitted) :
    candidateSlots omitted i count =
      (List.range' (i + 1) count).map some := by
  induction count generalizing i with
  | zero => rfl
  | succ count ih =>
      have hi : i < omitted := by omega
      rw [candidateSlots, if_neg (by omega : i ≠ omitted), gapLow, if_pos hi,
        List.range'_succ, List.map_cons]
      congr 1
      exact ih (i := i + 1) (by omega)

private lemma candidateSlots_after (omitted i count : ℕ) (h : omitted < i) :
    candidateSlots omitted i count = (List.range' i count).map some := by
  induction count generalizing i with
  | zero => rfl
  | succ count ih =>
      rw [candidateSlots, if_neg (by omega : i ≠ omitted), gapLow,
        if_neg (by omega : ¬i < omitted), List.range'_succ, List.map_cons]
      congr 1
      exact ih (i := i + 1) (by omega)

lemma candidateSlots_even (m : ℕ) :
    candidateSlots m 0 m = (List.range' 1 m).map some := by
  exact candidateSlots_before m 0 m (by omega)

private lemma insertNone_range (start omitted count : ℕ) (h : omitted ≤ count) :
    insertNone omitted (List.range' start count) =
      (List.range' start omitted).map some ++ none ::
        (List.range' (start + omitted) (count - omitted)).map some := by
  induction omitted generalizing start count with
  | zero => simp [insertNone]
  | succ omitted ih =>
      cases count with
      | zero => omega
      | succ count =>
          rw [List.range'_succ, insertNone, ih (start := start + 1) (count := count) (by omega)]
          simp only [List.range'_succ, List.map_cons, List.cons_append, List.cons.injEq, true_and]
          simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

lemma candidateSlots_odd (m omitted : ℕ) (homitted : omitted < m + 1) :
    candidateSlots omitted 0 (m + 1) = insertNone omitted (List.range' 1 m) := by
  have hsplit := candidateSlots_append omitted 0 omitted (m + 1 - omitted)
  rw [Nat.add_sub_of_le (by omega : omitted ≤ m + 1)] at hsplit
  simp only [Nat.zero_add] at hsplit
  rw [hsplit, candidateSlots_before omitted 0 omitted (by omega)]
  have hcount : m + 1 - omitted = (m - omitted) + 1 := by omega
  rw [hcount, candidateSlots, if_pos rfl]
  have htail := candidateSlots_after omitted (omitted + 1) (m - omitted) (by omega)
  rw [htail]
  rw [insertNone_range 1 omitted m (by omega)]
  simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

lemma candidate_eq_assemble (m highCount omitted : ℕ) :
    candidate m highCount omitted =
      assembleGaps (List.range' (m + 1) highCount)
        (candidateSlots omitted 0 highCount) := by
  cases highCount with
  | zero => rfl
  | succ remaining =>
      have go : ∀ i count,
          candidateTail m omitted i count =
            assembleTail (candidateSlots omitted i (count + 1))
              (List.range' (m + i + 2) count) := by
        intro i count
        induction count generalizing i with
        | zero =>
            by_cases hi : i = omitted
            · simp [candidateTail, candidateSlots, assembleTail, hi]
            · simp [candidateTail, candidateSlots, assembleTail, hi]
        | succ count ih =>
            rw [candidateTail, candidateSlots, List.range'_succ]
            by_cases hi : i = omitted
            · subst i
              simp only [if_pos, assembleTail]
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                ih (i := omitted + 1)
            · simp only [hi, List.singleton_append]
              change gapLow omitted i :: (m + i + 2) :: candidateTail m omitted (i + 1) count =
                gapLow omitted i :: (m + i + 2) ::
                  assembleTail (candidateSlots omitted (i + 1) (count + 1))
                    (List.range' (m + i + 3) count)
              congr 2
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (i := i + 1)
      rw [candidate, List.range'_succ, assembleGaps_cons]
      congr 1
      simpa using go 0 remaining

inductive FilledUntilLast : List (Option ℕ) → Prop
  | nil : FilledUntilLast []
  | last_none : FilledUntilLast [none]
  | last_some (low : ℕ) : FilledUntilLast [some low]
  | cons_some (low : ℕ) {rest : List (Option ℕ)}
      (tail : FilledUntilLast rest) : FilledUntilLast (some low :: rest)

lemma filledUntilLast_map_some (lows : List ℕ) :
    FilledUntilLast (lows.map some) := by
  induction lows with
  | nil => exact FilledUntilLast.nil
  | cons low lows ih =>
      cases lows with
      | nil => exact FilledUntilLast.last_some low
      | cons next rest => exact FilledUntilLast.cons_some low ih

lemma filledUntilLast_insertNone_last (lows : List ℕ) :
    FilledUntilLast (insertNone lows.length lows) := by
  induction lows with
  | nil => exact FilledUntilLast.last_none
  | cons low lows ih =>
      simp only [List.length_cons, insertNone]
      exact FilledUntilLast.cons_some low ih

private lemma filled_gap_high_increase {n high low next : ℕ}
    (hhigh : n / 2 < high) (hlow : low ≤ n / 2)
    (hnext : n / 2 < next) {pre rest input : List ℕ}
    (hinput : input = pre ++ high :: low :: next :: rest)
    (houtput : cyclicStackSort input = target n) : high < next := by
  let first := run pre []
  let highStep := drain high first.2
  have hafterHigh : (process (low :: next :: rest) (high :: highStep.2)).Sublist
      (target n) := by
    unfold cyclicStackSort at houtput
    rw [hinput, process_append] at houtput
    simp only [process] at houtput
    change first.1 ++ (highStep.1 ++
      process (low :: next :: rest) (high :: highStep.2)) = target n at houtput
    have hsub := List.sublist_append_right (first.1 ++ highStep.1)
      (process (low :: next :: rest) (high :: highStep.2))
    simpa only [List.append_assoc, houtput] using hsub
  have hlowDrain := drain_low_over_high hlow hhigh hafterHigh
  have hafterLow : (process (next :: rest) (low :: high :: highStep.2)).Sublist
      (target n) := by
    simpa only [process, hlowDrain, List.nil_append] using hafterHigh
  exact pending_low_forces_high_increase hlow hnext hafterLow

lemma successful_highs_of_filled_until_last {n : ℕ} {input : List ℕ}
    (hgapped : Gapped (n / 2) input)
    (hfilled : FilledUntilLast (gapSlots (n / 2) input))
    (houtput : cyclicStackSort input = target n) :
    (highEntries (n / 2) input).Pairwise (fun x y => x < y) := by
  have go : ∀ {suffix : List ℕ}, Gapped (n / 2) suffix →
      FilledUntilLast (gapSlots (n / 2) suffix) →
      ∀ pre, input = pre ++ suffix →
        (highEntries (n / 2) suffix).Pairwise (fun x y => x < y) := by
    intro suffix hs hslots
    induction hs with
    | nil => intro _ _; simp [highEntries]
    | @last high hhigh =>
        intro _ _
        simp [highEntries, hhigh]
    | @empty high next rest hhigh tail ih =>
        have hnext : n / 2 < next := by
          cases tail with
          | last hnext => exact hnext
          | empty hnext _ => exact hnext
          | filled hnext _ _ => exact hnext
        have htailSlots : gapSlots (n / 2) (next :: rest) ≠ [] := by
          cases rest with
          | nil => simp [gapSlots]
          | cons value rest =>
              simp only [gapSlots]
              split <;> simp
        simp only [gapSlots, if_neg (by omega : ¬next ≤ n / 2)] at hslots
        have hfalse : False := by
          generalize hslotsEq : gapSlots (n / 2) (next :: rest) = slots at hslots
          cases hslots with
          | last_none => exact htailSlots hslotsEq
        exact hfalse.elim
    | @filled high low rest hhigh hlow tail ih =>
        intro pre hwhole
        cases rest with
        | nil => simp [highEntries, hhigh, show ¬ n / 2 < low by omega]
        | cons next rest =>
            have hnext : n / 2 < next := by
              cases tail with
              | last hnext => exact hnext
              | empty hnext _ => exact hnext
              | filled hnext _ _ => exact hnext
            have htailSlots : FilledUntilLast (gapSlots (n / 2) (next :: rest)) := by
              have hslots' : FilledUntilLast
                  (some low :: gapSlots (n / 2) (next :: rest)) := by
                simpa only [gapSlots, if_pos hlow] using hslots
              have tailSome : ∀ {slots : List (Option ℕ)},
                  FilledUntilLast (some low :: slots) → FilledUntilLast slots := by
                intro slots h
                cases h with
                | last_some => exact FilledUntilLast.nil
                | cons_some _ tail => exact tail
              exact tailSome hslots'
            have htail := ih htailSlots (pre ++ [high, low]) (by
              simpa [List.append_assoc] using hwhole)
            have hadj := filled_gap_high_increase hhigh hlow hnext hwhole houtput
            simp only [highEntries, List.filter_cons]
            simp [hhigh, show ¬ n / 2 < low by omega]
            simp [hnext]
            constructor
            · constructor
              · exact hadj
              · intro later hlaterMem hlaterHigh
                have htail' : (next :: List.filter (fun x => decide (n / 2 < x)) rest).Pairwise
                    (fun x y => x < y) := by
                  simpa [highEntries, hnext] using htail
                have hmemFilter : later ∈ List.filter (fun x => decide (n / 2 < x)) rest := by
                  simp [hlaterMem, hlaterHigh]
                have hnextLater := (List.pairwise_cons.mp htail').1 later hmemFilter
                omega
            · simpa [highEntries, hnext] using htail
  exact go hgapped hfilled [] (by simp)

end D5.S1.Words.Patterns.CyclicStackPreimages
