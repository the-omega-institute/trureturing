/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundarySafePrice
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundarySafePrice
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Safe optimal common scripts retain their own actual original-source paid archives. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryPrice

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundarySafePrice
open D5.S0.Tower.DBonacci.Names
open D5.S3.ObserverMemory.Algorithms.KBonacciIrreversibleAcquisition
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open WindowChargeInverse
open LiteralModel EndpointCells GlobalPresetObstruction PhysicalWindowDecoder OriginalNarrowCost OriginalAcquiredTrace OriginalExecutionBridge
open FirstWindowBoundaryAttainment FirstWindowBoundaryCodes FirstWindowBoundaryCompatibility
open FirstWindowBoundaryFourLabels FirstWindowBoundaryPrice DonorCorrection

def SafePlan (m : ℕ) (H : ZMod 2 → Finset ℕ) (c : ℕ) : Prop :=
  ∃ (bs : List (Fin m → Bool)) (codes : Phase m → List (Option (ZMod 2))),
    bs.length = c ∧
    (∀ v j s, s < 2 * m - 2 →
      endpointDifferences (some v) ((scriptArchive bs (some ⟨v, -j, s⟩)).map Prod.snd) = codes j) ∧
    (∀ p q, codes p = codes q → membership m H p = membership m H q) ∧
    (∀ j, none ∉ codes j)

private theorem safe_plan {Y : Type u} (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (H : ZMod 2 → Finset ℕ) (inside : ∀ v h, h ∈ H v → 1 ≤ h ∧ h ≤ m)
    (A B : ZMod 2 → Y) (distinct : ∀ v, A v ≠ B v)
    (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
      f (some ⟨v, -j, s⟩) = if j.val ∈ H v then B v else A v) :
    SafePlan m H (presetCost m H) := by
  classical
  have price := original_first_window_preset_price m hm alphabet H inside A B distinct f target
  have outside (j : Phase m) (out : ¬ (1 ≤ j.val ∧ j.val ≤ m)) : membership m H j = 0 := by
    have absent (v : ZMod 2) : j.val ∉ H v := fun mem => out (inside v _ mem)
    simp [membership, supportRow, absent]
  let pairLabel (v : ZMod 2) (z : Pair) : Y :=
    if v = 0 then (if z.1 = 0 then A v else B v) else (if z.2 = 0 then A v else B v)
  have labels (v : ZMod 2) (j : Phase m) (s : ℕ) (hs : s < 2 * m - 2) :
      f (some ⟨v, -j, s⟩) = pairLabel v (membership m H j) := by
    rw [target v j s hs]
    have values : v = 0 ∨ v = 1 := (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) v
    rcases values with rfl | rfl <;> simp [pairLabel, membership, supportRow]
  have cap (cost : presetCost m H = 3) : SafePlan m H (presetCost m H) := by
    have supplied := original_first_window_three_block_stream m hm alphabet f
      (membership m H) outside pairLabel labels
    refine ⟨words m (membership m H), code m (membership m H), by rw [cost]; rfl,
      fun v j s hs => (supplied.2.2 v j s hs).1,
      code_separates m (membership m H) outside, ?_⟩
    intro j
    simp [code]
  by_cases one : (fullImage m H).card = 1
  · have empty := price.2.2.1.mp one
    refine ⟨[], fun _ => [], ?_, ?_, ?_, by simp⟩
    · simp [presetCost, one]
    · intro v j s hs; rfl
    · intro p q eq; simp [membership, supportRow, empty]
  by_cases two : (fullImage m H).card = 2
  · obtain ⟨z, nz, image, normalized, supports, _⟩ := price.2.2.2.1 two
    let U := H 0 ∪ H 1
    have Uinside : ∀ h ∈ U, 1 ≤ h ∧ h ≤ m := by
      intro h hh; rcases Finset.mem_union.mp hh with hh | hh <;> exact inside _ h hh
    let synthetic : Option (LiveRecord (2 * m - 2)) → ZMod 2 := fun q =>
      q.elim 0 (fun q => supportRow U (-q.phase).val)
    have supplied := original_first_window_binary_stream m hm alphabet U Uinside synthetic
      (fun _ b => b) (by intro v j s hs; simp [synthetic])
    refine ⟨binaryWords m U, binaryCode m U, ?_,
      fun v j s hs => (supplied.2.2.1 v j s hs).1, ?_, ?_⟩
    · simpa [presetCost, one, two, U] using supplied.2.1
    · intro p q same
      have rows := binary_separates m hm U Uinside p q same
      have member : p.val ∈ U ↔ q.val ∈ U := by
        by_cases a : p.val ∈ U <;> by_cases b : q.val ∈ U <;> simp_all [supportRow]
      rw [normalized p, normalized q]
      change (if p.val ∈ U then z else 0) = (if q.val ∈ U then z else 0)
      by_cases h : p.val ∈ U
      · rw [if_pos h, if_pos (member.mp h)]
      · rw [if_neg h, if_neg (fun hq => h (member.mpr hq))]
    · intro j; unfold binaryCode; split_ifs <;> simp
  by_cases three : (fullImage m H).card = 3
  · by_cases admitted : piThree m H
    · have bound := admitted.1
      have positive : 0 < (internalImage m H).card := by
        have val : ((2 : ℕ) : Phase m).val = 2 := ZMod.val_natCast_of_lt (by omega)
        apply Finset.card_pos.mpr
        exact ⟨_, Finset.mem_image.mpr ⟨(2 : ℕ), Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, by rw [val]; omega⟩, rfl⟩⟩
      have cost : presetCost m H = 2 := by simp [presetCost, one, two, three, admitted]
      by_cases internalOne : (internalImage m H).card = 1
      · have supplied := (original_first_window_boundary_rows m hm alphabet H inside A B distinct f target).2.2 internalOne
        have homogeneous (p q : Phase m) (plo : 2 ≤ p.val) (phi : p.val < m)
            (qlo : 2 ≤ q.val) (qhi : q.val < m) : membership m H p = membership m H q := by
          obtain ⟨z, image⟩ := Finset.card_eq_one.mp internalOne
          have mem (j : Phase m) (lo : 2 ≤ j.val) (hi : j.val < m) :
              membership m H j ∈ internalImage m H :=
            Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, lo, hi⟩, rfl⟩
          have a := mem p plo phi; have b := mem q qlo qhi
          rw [image, Finset.mem_singleton] at a b
          exact a.trans b.symm
        refine ⟨homogeneousWords m, homogeneousCode m, by rw [cost]; rfl,
          fun v j s hs => (supplied.2 v j s hs).1,
          homogeneous_separates m hm (membership m H) outside homogeneous, ?_⟩
        intro j; unfold homogeneousCode; split_ifs <;> simp
      · have internalTwo : (internalImage m H).card = 2 := by omega
        by_cases base : (0 : Pair) ∈ internalImage m H
        · obtain ⟨X, S, a, _, _, _, _, _, _, _, count, refines, _, readings⟩ :=
            (original_first_window_three_label_compatibility m hm alphabet H inside A B distinct f target three).2 internalTwo base
          refine ⟨baseWords m S a, fun j => [some (baseCode m S a j).1, some (baseCode m S a j).2],
            count.trans cost.symm, fun v j s hs => (readings v j s hs).1, ?_, by simp⟩
          intro p q same
          simp only [List.cons.injEq, Option.some.injEq] at same
          exact refines p q (Prod.ext same.1 same.2.1)
        · obtain ⟨S, flip, left, right, _, _, _, count, refines, _, readings⟩ :=
            (original_first_window_nonbase_internal_stream m hm alphabet H inside A B distinct f target three internalTwo base).2 admitted.2
          refine ⟨nonbaseWords m S flip left right,
            fun j => [some (nonbaseCode m S flip left right j).1, some (nonbaseCode m S flip left right j).2],
            count.trans cost.symm, fun v j s hs => (readings v j s hs).1, ?_, by simp⟩
          intro p q same
          simp only [List.cons.injEq, Option.some.injEq] at same
          exact refines p q (Prod.ext same.1 same.2.1)
    · apply cap; simp [presetCost, one, two, three, admitted]
  · have four : (fullImage m H).card = 4 := by
      have pos : 0 < (fullImage m H).card := Finset.card_pos.mpr
        ⟨_, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩
      have bound : (fullImage m H).card ≤ 4 := by
        simpa [ZMod.card] using Finset.card_le_univ (fullImage m H)
      omega
    have compat := original_first_window_four_label_compatibility m hm alphabet H inside A B distinct f target four
    have cost : presetCost m H = if piFour m H then 2 else 3 := by
      have ext := original_first_window_table_extremes m hm alphabet H inside A B distinct f target four
      unfold presetCost
      simp only [one, two, three, if_false]
      by_cases oneK : (internalImage m H).card = 1
      · simp [oneK, ext.2.1 oneK]
      · by_cases many : 3 ≤ (internalImage m H).card
        · simp [oneK, many, ext.2.2 many]
        · simp [oneK, many]
    by_cases admitted : piFour m H
    · obtain ⟨g, S, a, bijective, _, _, _, _, _, _, _, _, _, codes, count, _, readings⟩ := compat.2.2 admitted
      refine ⟨baseWords m S a, fun j => [some (g (membership m H j)).1, some (g (membership m H j)).2],
        count.trans (by simpa [admitted] using cost.symm), fun v j s hs => (readings v j s hs).1,
        ?_, by simp⟩
      intro p q same
      simp only [List.cons.injEq, Option.some.injEq] at same
      exact bijective.1 (Prod.ext same.1 same.2.1)
    · apply cap; simpa [admitted] using cost

/-- A common optimal script succeeds on every live original history, stops
at bottom without issuing a block, and realizes its worst bit fee on one joint source. -/
theorem original_first_window_safe_preset_price {Y : Type u} (m : ℕ) (hm : 5 ≤ m)
    (alphabet : Bool) (H : ZMod 2 → Finset ℕ)
    (inside : ∀ v h, h ∈ H v → 1 ≤ h ∧ h ≤ m)
    (A B : ZMod 2 → Y) (distinct : ∀ v, A v ≠ B v)
    (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
      f (some ⟨v, -j, s⟩) = if j.val ∈ H v then B v else A v) :
    ∃ (stream : ℕ → Fin m → Bool)
      (stop : Option (ZMod 2) → NarrowWindowCost.Archive m → Option Y),
      FullPositiveWindowPrice.SelectorLegal (2 * m - 2) alphabet (presetSelector stream stop) ∧
      stop none [] = some (f none) ∧
      (∀ history : List (AllowedBlock (2 * m - 2) m alphabet),
        let w := history.flatMap (fun a => List.ofFn a.val)
        let q := OriginalRecord (2 * m - 2) (by omega) w
        ∃ issued, PaidTrace (presetSelector stream stop) (NarrowWindowCost.output (2 * m - 2) (by omega) w)
          q [] issued (f q) ∧ issued.length = NearCriticalGrid.fee (presetCost m H) q ∧
          (archiveWords issued).length = m * NearCriticalGrid.fee (presetCost m H) q ∧
          none ∉ issued.map Prod.snd) ∧
      ∃ (history : List (AllowedBlock (2 * m - 2) m alphabet)) (issued : NarrowWindowCost.Archive m),
        OriginalRecord (2 * m - 2) (by omega) (history.flatMap (fun a => List.ofFn a.val)) =
          some ⟨0, 0, 0⟩ ∧
        PaidTrace (k := 2 * m - 2) (presetSelector stream stop) (some 0) (some ⟨0, 0, 0⟩) [] issued
          (f (some ⟨0, 0, 0⟩)) ∧ issued.length = presetCost m H ∧
          (archiveWords issued).length = m * presetCost m H := by
  classical
  obtain ⟨bs, codes, count, readings, refines, live⟩ := safe_plan m hm alphabet H inside A B distinct f target
  let label (v : ZMod 2) (z : Pair) : Y :=
    if v = 0 then (if z.1 = 0 then A v else B v) else (if z.2 = 0 then A v else B v)
  let decode (v : ZMod 2) (ar : NarrowWindowCost.Archive m) : Y :=
    if h : ∃ j, codes j = endpointDifferences (some v) (ar.map Prod.snd)
    then label v (membership m H (Classical.choose h)) else f none
  have decoded (v : ZMod 2) (phase : Phase m) (s : ℕ) (hs : s < 2 * m - 2) :
      decode v (scriptArchive bs (some ⟨v, phase, s⟩)) = f (some ⟨v, phase, s⟩) := by
    have rd := readings v (-phase) s hs
    simp only [neg_neg] at rd
    have exist : ∃ j, codes j = endpointDifferences (some v)
        ((scriptArchive bs (some ⟨v, phase, s⟩)).map Prod.snd) := ⟨-phase, rd.symm⟩
    unfold decode
    rw [dif_pos exist, refines _ _ ((Classical.choose_spec exist).trans rd)]
    have labels := target v (-phase) s hs
    simp only [neg_neg] at labels
    rw [labels]
    have values : v = 0 ∨ v = 1 := (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) v
    rcases values with rfl | rfl <;> simp [label, membership, supportRow]
  have safe (v : ZMod 2) (phase : Phase m) (s : ℕ) (hs : s < 2 * m - 2) :
      none ∉ (scriptArchive bs (some ⟨v, phase, s⟩)).map Prod.snd := by
    apply FirstWindowBoundaryAdaptive.differences_live v
    rw [show (⟨v, phase, s⟩ : LiveRecord (2 * m - 2)) = ⟨v, -(-phase), s⟩ by simp,
      readings v (-phase) s hs]
    exact live _
  let stream : ℕ → Fin m → Bool := fun t => bs[t]?.getD (fun _ => false)
  let stop := NearCriticalGrid.scriptStop (fun _ => bs) decode (f none)
  have same : FourLabelPaidFeedback.selectedSelector (NearCriticalGrid.scriptStreams (fun _ => bs))
      (NearCriticalGrid.scriptStop (fun _ => bs) decode (f none)) =
      presetSelector stream stop := rfl
  have traces (history : List (AllowedBlock (2 * m - 2) m alphabet)) :=
    NearCriticalGrid.script_history_trace (2 * m - 2) m (by omega) f (presetCost m H)
      (fun _ => bs) decode (fun _ => count) decoded safe alphabet history
  simp only [same] at traces
  refine ⟨stream, stop, ?_, rfl, traces, ?_⟩
  · intro free ar word selected localAlphabet
    exact short_legal _ m (by omega) (by omega) word
  · obtain ⟨history, state⟩ :=
      ((whole_first_zero_acquisition (2 * m - 2) m (by omega) (by omega) alphabet (fun _ => ())).1
        (some ⟨0, 0, 0⟩)).mp ⟨by change 0 < 2 * m - 2; omega, by simp⟩
    have record : OriginalRecord (2 * m - 2) (by omega)
        (history.flatMap (fun a => List.ofFn a.val)) = some ⟨0, 0, 0⟩ :=
      (record_history (2 * m - 2) m (by omega) alphabet history).trans state
    obtain ⟨issued, traced, blocks, bits, _⟩ := traces history
    have output : NarrowWindowCost.output (2 * m - 2) (by omega)
        (history.flatMap (fun a => List.ofFn a.val)) = some 0 := by
      have bridge : NarrowWindowCost.output (2 * m - 2) (by omega)
          (history.flatMap (fun a => List.ofFn a.val)) =
          endpointReading (OriginalRecord (2 * m - 2) (by omega)
            (history.flatMap (fun a => List.ofFn a.val))) :=
        output_record (2 * m - 2) (by omega) _
      rw [record] at bridge
      exact bridge
    refine ⟨history, issued, record, ?_, ?_, ?_⟩
    · simpa only [record, output] using traced
    · simpa [record, NearCriticalGrid.fee] using blocks
    · simpa [record, NearCriticalGrid.fee] using bits

#print axioms original_first_window_safe_preset_price
end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundarySafePrice
