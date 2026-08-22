/- GID: D5/S1/Words/NegativeExpansions/BasePhiNegativePrefixTridentPreservation
   generality: I
   mirror-B: D5/B/S1/Words/NegativeExpansions/BasePhiNegativePrefixTridentPreservation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Preserve Lucas-gap core classifications through the three occurrence-set lifts. -/

import D5.S1.Words.NegativeExpansions.BasePhiNegativePrefixTridentCore

namespace D5.X_Frontier.BasePhiNegativePrefixTrident

open D5.S1.Words.Expansions.BasePhiNegative
open D5.S1.Words.Expansions.BasePhiCanonicalExpansion
open D5.S1.Words.Expansions.BasePhiCarryTransducer
open D5.S1.Scale

noncomputable section

def v_translate_initial_value (family : GapFamily) (a b r : Int) : Prop :=
  ∀ j : Nat,
    (fun n => vForFamily family a b r n + (j : Int)) =
      vForFamily family a b (r + (j : Int))

theorem v_translate_initial_value_proved (family : GapFamily) (a b r : Int) :
    v_translate_initial_value family a b r := by
  intro j
  funext n
  cases family <;> induction n with
  | zero => rfl
  | succ n ih =>
      simp only [vForFamily, vF, vG, vH, gapSequence] at ih ⊢
      rw [← ih]
      ring

def three_arms_pairwise_disjoint {w : List Bool} (hw : w ≠ [])
    (hadmissible : AdmissibleNegativePrefix canonicalExpansion w)
    (hfibers : negative_tail_fiber_shape hw hadmissible)
    (hlift : core_occurrence_unique_lift hw hadmissible hfibers)
    {family : GapFamily} {a b r : Int}
    (hcore : LucasPair a b ∧ 0 < r ∧
      Core w = sequenceRange (vForFamily family a b r))
    (htranslate : v_translate_initial_value family a b r) : Prop :=
  w.head? = some false →
    ∀ i j : Fin 3, i ≠ j →
      Disjoint
        (sequenceRange (vForFamily family a b (r + (i.1 : Int))))
        (sequenceRange (vForFamily family a b (r + (j.1 : Int))))

def occurrenceSet_lucas_gap_classification {w : List Bool} (hw : w ≠ [])
    (hadmissible : AdmissibleNegativePrefix canonicalExpansion w)
    (hfibers : negative_tail_fiber_shape hw hadmissible)
    (hlift : core_occurrence_unique_lift hw hadmissible hfibers)
    {family : GapFamily} {a b r : Int}
    (hcore : LucasPair a b ∧ 0 < r ∧
      Core w = sequenceRange (vForFamily family a b r))
    (htranslate : v_translate_initial_value family a b r)
    (hdisjoint : three_arms_pairwise_disjoint hw hadmissible hfibers hlift
      hcore htranslate) : Prop :=
  ∃ (family : GapFamily) (a b r : Int),
      LucasPair a b ∧ 0 < r ∧
      if w.head? = some true then
        occurrenceSet canonicalExpansion w =
          sequenceRange (vForFamily family a b r)
      else
        occurrenceSet canonicalExpansion w =
          ⋃ j : Fin 3,
            sequenceRange (vForFamily family a b (r + (j.1 : Int)))

def occurrenceSet_lucas_gap_classification_exact {w : List Bool} (hw : w ≠ [])
    (hadmissible : AdmissibleNegativePrefix canonicalExpansion w)
    (hfibers : negative_tail_fiber_shape hw hadmissible)
    (hlift : core_occurrence_unique_lift hw hadmissible hfibers)
    {family : GapFamily} {a b r : Int}
    (hcore : LucasPair a b ∧ 0 < r ∧
      Core w = sequenceRange (vForFamily family a b r))
    (htranslate : v_translate_initial_value family a b r)
    (hdisjoint : three_arms_pairwise_disjoint hw hadmissible hfibers hlift
      hcore htranslate) : Prop :=
  if w.head? = some true then
    occurrenceSet canonicalExpansion w =
      sequenceRange (vForFamily family a b r)
  else
    occurrenceSet canonicalExpansion w =
      ⋃ j : Fin 3,
        sequenceRange (vForFamily family a b (r + (j.1 : Int)))

theorem LucasPair.parameters {a b : Int} (h : LucasPair a b) :
    lucasParameter a ∧ lucasParameter b := by
  obtain ⟨k, _, ha, hb⟩ := h
  exact ⟨⟨k + 1, ha⟩, ⟨k, hb⟩⟩

private theorem vForFamily_pos {family : GapFamily} {a b r : Int}
    (hpair : LucasPair a b) (hr : 0 < r) (n : Nat) :
    0 < vForFamily family a b r n := by
  have hparameters := hpair.parameters
  have ha := lucas_parameter_pos hparameters.1
  have hb := lucas_parameter_pos hparameters.2
  have hmono : StrictMono (vForFamily family a b r) := by
    cases family <;> exact gap_sequence_strict_mono _ ha hb
  cases n with
  | zero => cases family <;> exact hr
  | succ n =>
      have hfirst := hmono (Nat.zero_lt_succ n)
      cases family <;> simpa [vForFamily, vF, vG, vH, gapSequence] using
        lt_trans hr hfirst

private theorem prefix_head_false {w : List Bool} (hw : w ≠ [])
    (hhead : w.head? = some false) {q : Nat}
    (hq : q ∈ Core w) :
    negativeDigit canonicalExpansion q 0 = false := by
  cases w with
  | nil => contradiction
  | cons bit tail =>
      have hzero := hq.2.2 ⟨0, by simp⟩
      simpa using hzero.trans (show bit = false by simpa using hhead)

private theorem core_shift_occurs_of_head_false {w : List Bool} (hw : w ≠ [])
    (hadmissible : AdmissibleNegativePrefix canonicalExpansion w)
    (hfibers : negative_tail_fiber_shape hw hadmissible)
    (hhead : w.head? = some false) {q j : Nat}
    (hq : q ∈ Core w) (hj : j < 3) :
    q + j ∈ occurrenceSet canonicalExpansion w := by
  have hqOccurrence : q ∈ occurrenceSet canonicalExpansion w :=
    ⟨hq.1.1.1, hq.2⟩
  obtain ⟨s, hs, _⟩ :=
    (hfibers q hqOccurrence).2 (prefix_head_false hw hhead hq)
  have hsMem : s ∈ negativeTailFiber q := by
    rw [hs.2.2]
    simp
  have hsEq : s = q := by
    have hqs := hq.1.2 s hsMem
    omega
  have hshiftMem : q + j ∈ negativeTailFiber q := by
    rw [hs.2.2, hsEq]
    change q + j = q ∨ q + j = q + 1 ∨ q + j = q + 2
    omega
  exact ⟨hshiftMem.1, prefix_occurs_of_same_tail hshiftMem.2 hq.2⟩

private theorem shifted_sequence_lift {w : List Bool} (hw : w ≠ [])
    (hadmissible : AdmissibleNegativePrefix canonicalExpansion w)
    (hfibers : negative_tail_fiber_shape hw hadmissible)
    {family : GapFamily} {a b r : Int}
    (hcore : LucasPair a b ∧ 0 < r ∧
      Core w = sequenceRange (vForFamily family a b r))
    (htranslate : v_translate_initial_value family a b r)
    (hhead : w.head? = some false) {i : Fin 3} {N : Nat}
    (hN : N ∈ sequenceRange
      (vForFamily family a b (r + (i.1 : Int)))) :
    ∃ q : Nat, q ∈ Core w ∧ N = q + i.1 ∧
      N ∈ occurrenceSet canonicalExpansion w := by
  obtain ⟨n, hn⟩ := hN
  have hbasePos := vForFamily_pos (family := family) hcore.1 hcore.2.1 n
  let q := (vForFamily family a b r n).toNat
  have hqCast : (q : Int) = vForFamily family a b r n := by
    exact Int.toNat_of_nonneg hbasePos.le
  have hNInt : (N : Int) = (q : Int) + (i.1 : Int) := by
    rw [hqCast]
    exact hn.trans (congrFun (htranslate i.1) n).symm
  have hNq : N = q + i.1 := by exact_mod_cast hNInt
  have hqCore : q ∈ Core w := by
    rw [hcore.2.2]
    exact ⟨n, hqCast⟩
  refine ⟨q, hqCore, hNq, ?_⟩
  rw [hNq]
  exact core_shift_occurs_of_head_false hw hadmissible hfibers hhead
    hqCore i.2

theorem three_arms_pairwise_disjoint_proved {w : List Bool} (hw : w ≠ [])
    (hadmissible : AdmissibleNegativePrefix canonicalExpansion w)
    (hfibers : negative_tail_fiber_shape hw hadmissible)
    (hlift : core_occurrence_unique_lift hw hadmissible hfibers)
    {family : GapFamily} {a b r : Int}
    (hcore : LucasPair a b ∧ 0 < r ∧
      Core w = sequenceRange (vForFamily family a b r))
    (htranslate : v_translate_initial_value family a b r) :
    three_arms_pairwise_disjoint hw hadmissible hfibers hlift
      hcore htranslate := by
  intro hhead i j hij
  rw [Set.disjoint_left]
  intro N hNi hNj
  rcases shifted_sequence_lift hw hadmissible hfibers hcore htranslate hhead hNi with
    ⟨qi, hqiCore, hNqi, hNiOccurrence⟩
  rcases shifted_sequence_lift hw hadmissible hfibers hcore htranslate hhead hNj with
    ⟨qj, hqjCore, hNqj, _hNjOccurrence⟩
  have hiBound : i.1 < prefixMultiplicity w := by
    simp [prefixMultiplicity, hhead, i.2]
  have hjBound : j.1 < prefixMultiplicity w := by
    simp [prefixMultiplicity, hhead, j.2]
  obtain ⟨qk, _hqk, hunique⟩ := hlift N hNiOccurrence
  have hiEq : (qi, i.1) = qk := hunique (qi, i.1) ⟨hqiCore, hiBound, hNqi⟩
  have hjEq : (qj, j.1) = qk := hunique (qj, j.1) ⟨hqjCore, hjBound, hNqj⟩
  apply hij
  apply Fin.ext
  exact congrArg Prod.snd (hiEq.trans hjEq.symm)

theorem occurrenceSet_lucas_gap_classification_exact_proved {w : List Bool}
    (hw : w ≠ [])
    (hadmissible : AdmissibleNegativePrefix canonicalExpansion w)
    (hfibers : negative_tail_fiber_shape hw hadmissible)
    (hlift : core_occurrence_unique_lift hw hadmissible hfibers)
    {family : GapFamily} {a b r : Int}
    (hcore : LucasPair a b ∧ 0 < r ∧
      Core w = sequenceRange (vForFamily family a b r))
    (htranslate : v_translate_initial_value family a b r)
    (hdisjoint : three_arms_pairwise_disjoint hw hadmissible hfibers hlift
      hcore htranslate) :
    occurrenceSet_lucas_gap_classification_exact hw hadmissible hfibers hlift
      hcore htranslate hdisjoint := by
  classical
  unfold occurrenceSet_lucas_gap_classification_exact
  split_ifs with hhead
  · ext N
    constructor
    · intro hN
      obtain ⟨qj, hqj, _hunique⟩ := hlift N hN
      have hjZero : qj.2 = 0 := by
        have := hqj.2.1
        simp [prefixMultiplicity, hhead] at this
        omega
      have hqN : qj.1 = N := by omega
      rw [← hcore.2.2]
      simpa [hqN] using hqj.1
    · intro hN
      rw [← hcore.2.2] at hN
      exact ⟨hN.1.1.1, hN.2⟩
  · have hheadFalse : w.head? = some false := by
      cases w with
      | nil => contradiction
      | cons bit tail =>
          cases bit <;> simp_all
    ext N
    constructor
    · intro hN
      obtain ⟨qj, hqj, _hunique⟩ := hlift N hN
      have hjBound : qj.2 < 3 := by
        simpa [prefixMultiplicity, hheadFalse] using hqj.2.1
      let j : Fin 3 := ⟨qj.2, hjBound⟩
      rw [Set.mem_iUnion]
      refine ⟨j, ?_⟩
      rw [sequenceRange]
      rw [hcore.2.2] at hqj
      obtain ⟨n, hn⟩ := hqj.1
      refine ⟨n, ?_⟩
      rw [← congrFun (htranslate j.1) n, ← hn]
      exact_mod_cast hqj.2.2
    · rw [Set.mem_iUnion]
      rintro ⟨j, hNj⟩
      rcases shifted_sequence_lift hw hadmissible hfibers hcore htranslate
        hheadFalse hNj with ⟨q, hqCore, hNq, hNOccurrence⟩
      exact hNOccurrence

theorem occurrenceSet_lucas_gap_classification_proved {w : List Bool}
    (hw : w ≠ [])
    (hadmissible : AdmissibleNegativePrefix canonicalExpansion w)
    (hfibers : negative_tail_fiber_shape hw hadmissible)
    (hlift : core_occurrence_unique_lift hw hadmissible hfibers)
    {family : GapFamily} {a b r : Int}
    (hcore : LucasPair a b ∧ 0 < r ∧
      Core w = sequenceRange (vForFamily family a b r))
    (htranslate : v_translate_initial_value family a b r)
    (hdisjoint : three_arms_pairwise_disjoint hw hadmissible hfibers hlift
      hcore htranslate) :
    occurrenceSet_lucas_gap_classification hw hadmissible hfibers hlift
      hcore htranslate hdisjoint := by
  refine ⟨family, a, b, r, hcore.1, hcore.2.1, ?_⟩
  exact occurrenceSet_lucas_gap_classification_exact_proved hw hadmissible
    hfibers hlift hcore htranslate hdisjoint

end

end D5.X_Frontier.BasePhiNegativePrefixTrident
