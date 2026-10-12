/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundaryAdaptive
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundaryAdaptive
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Each original value selects its own safe binary script and pays only its issued prefix. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment
import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NearCriticalGrid

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAdaptive
open D5.S0.Tower.DBonacci.Names
open D5.S3.ObserverMemory.Algorithms.KBonacciIrreversibleAcquisition
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open LiteralModel EndpointCells WindowChargeInverse PhysicalWindowDecoder
open OriginalNarrowCost OriginalAcquiredTrace OriginalExecutionBridge DonorCorrection
open FirstWindowBoundaryAttainment GlobalPresetObstruction

def worstCost (H : ZMod 2 → Finset ℕ) : ℕ := max (binaryCost (H 0)) (binaryCost (H 1))

def sourceCost {k : ℕ} (H : ZMod 2 → Finset ℕ) : Option (LiveRecord k) → ℕ
  | none => 0
  | some q => binaryCost (H q.value)

def binaryDecode {Y : Type u} (m : ℕ) (H : ZMod 2 → Finset ℕ)
    (A B : ZMod 2 → Y) (bottom : Y) (v : ZMod 2) (ar : NarrowWindowCost.Archive m) : Y :=
  if h : ∃ j, binaryCode m (H v) j = endpointDifferences (some v) (ar.map Prod.snd)
  then if (Classical.choose h).val ∈ H v then B v else A v
  else bottom

def adaptiveSelector {Y : Type u} (m : ℕ) (H : ZMod 2 → Finset ℕ)
    (A B : ZMod 2 → Y) (bottom : Y) : NarrowWindowCost.Selector m Y :=
  FourLabelPaidFeedback.selectedSelector
    (NearCriticalGrid.scriptStreams (fun v => binaryWords m (H v)))
    (NearCriticalGrid.scriptStop (fun v => binaryWords m (H v))
      (binaryDecode m H A B bottom) bottom)

private theorem binary_decode_correct {Y : Type u} (m : ℕ) (hm : 5 ≤ m)
    (H : ZMod 2 → Finset ℕ) (inside : ∀ v h, h ∈ H v → 1 ≤ h ∧ h ≤ m)
    (A B : ZMod 2 → Y) (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
      f (some ⟨v, -j, s⟩) = if j.val ∈ H v then B v else A v)
    (v : ZMod 2) (j : Phase m) (s : ℕ) (hs : s < 2 * m - 2) :
    binaryDecode m H A B (f none) v
      (scriptArchive (binaryWords m (H v)) (some ⟨v, -j, s⟩)) = f (some ⟨v, -j, s⟩) := by
  classical
  let synthetic : Option (LiveRecord (2 * m - 2)) → ZMod 2 := fun q =>
    q.elim 0 (fun q => supportRow (H v) (-q.phase).val)
  have supplied := (original_first_window_binary_stream m hm false (H v) (inside v)
    synthetic (fun _ b => b) (by intro w p t ht; simp [synthetic])).2.2.1 v j s hs
  have existsPhase : ∃ p, binaryCode m (H v) p = endpointDifferences (some v)
      ((scriptArchive (binaryWords m (H v)) (some ⟨v, -j, s⟩)).map Prod.snd) :=
    ⟨j, supplied.1.symm⟩
  unfold binaryDecode
  rw [dif_pos existsPhase]
  have same := binary_separates m hm (H v) (inside v) _ j
    ((Classical.choose_spec existsPhase).trans supplied.1)
  rw [target v j s hs]
  have membership : (Classical.choose existsPhase).val ∈ H v ↔ j.val ∈ H v := by
    by_cases a : (Classical.choose existsPhase).val ∈ H v <;>
      by_cases b : j.val ∈ H v <;> simp_all [supportRow]
  simp only [membership]

theorem differences_live (v : ZMod 2) (replies : List (Option (ZMod 2)))
    (live : none ∉ endpointDifferences (some v) replies) : none ∉ replies := by
  induction replies generalizing v with
  | nil => simp
  | cons head rest ih =>
    cases head with
    | none => simp [endpointDifferences] at live
    | some z =>
      simp [endpointDifferences] at live
      simpa using ih z live

private theorem branch_history_trace {Y : Type u} (m : ℕ) (hm : 5 ≤ m)
    (H : ZMod 2 → Finset ℕ) (inside : ∀ v h, h ∈ H v → 1 ≤ h ∧ h ≤ m)
    (A B : ZMod 2 → Y) (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
      f (some ⟨v, -j, s⟩) = if j.val ∈ H v then B v else A v)
    (alphabet : Bool) (history : List (AllowedBlock (2 * m - 2) m alphabet)) :
    let w := history.flatMap (fun a => List.ofFn a.val)
    let q := OriginalRecord (2 * m - 2) (by omega) w
    let free := NarrowWindowCost.output (2 * m - 2) (by omega) w
    ∃ issued, PaidTrace (adaptiveSelector m H A B (f none)) free q [] issued (f q) ∧
      issued.map Prod.fst = q.elim [] (fun q => binaryWords m (H q.value)) ∧
      issued.length = sourceCost H q ∧ (archiveWords issued).length = m * sourceCost H q ∧
      none ∉ issued.map Prod.snd := by
  intro w q free
  have output : free = endpointReading q := output_record _ (by omega) w
  cases initial : q with
  | none =>
    refine ⟨[], ?_, rfl, rfl, by simp [archiveWords, sourceCost], by simp⟩
    rw [output, initial]
    rfl
  | some source =>
    have freeEq : free = some source.value := by rw [output, initial]; rfl
    have hs : source.tail < 2 * m - 2 := by
      change OriginalRecord (2 * m - 2) (by omega) w = some source at initial
      unfold OriginalRecord at initial
      cases scan : (NarrowWindowCost.scanner (2 * m - 2) (by omega)).eval w with
      | none => simp [scan] at initial
      | some tail =>
        simp only [scan, Option.map_some, Option.some.injEq] at initial
        simpa only [← congrArg LiveRecord.tail initial] using tail.isLt
    have same (ar : NarrowWindowCost.Archive m) :
        adaptiveSelector m H A B (f none) (some source.value) ar =
        finalSelector 0 (binaryWords m (H source.value))
          (binaryDecode m H A B (f none) source.value) (some source.value) ar := by
      simp only [adaptiveSelector, FourLabelPaidFeedback.selectedSelector, Option.getD_some,
        presetSelector, NearCriticalGrid.scriptStop]
      cases selected : (binaryWords m (H source.value))[ar.length]? <;>
        simp [selected, NearCriticalGrid.scriptStreams, finalSelector]
    have script := original_final_script (2 * m - 2) m (by omega)
      (binaryWords m (H source.value)) (binaryDecode m H A B (f none) source.value)
      w (some source.value) []
    dsimp only at script
    change OriginalRecord (2 * m - 2) (by omega) w = some source at initial
    rw [initial] at script
    have decoded := binary_decode_correct m hm H inside A B f target
      source.value (-source.phase) source.tail hs
    simp only [neg_neg] at decoded
    have record : (⟨source.value, source.phase, source.tail⟩ : LiveRecord (2 * m - 2)) =
        source := by cases source; rfl
    rw [record] at decoded
    have traced := (FullPositiveWindowPrice.trace_congr _ _ (some source.value)
      same _ _ [] _).mpr script.1
    rw [decoded] at traced
    have count : (binaryWords m (H source.value)).length = binaryCost (H source.value) := by
      unfold binaryWords binaryCost
      split_ifs <;> rfl
    refine ⟨scriptArchive (binaryWords m (H source.value)) (some source), ?_, script.2.1,
      script.2.2.1.trans count, ?_, ?_⟩
    · rw [freeEq]; exact traced
    · rw [archive_length, script.2.2.1, count]; simp [sourceCost, Nat.mul_comm]
    · apply differences_live source.value
      let synthetic : Option (LiveRecord (2 * m - 2)) → ZMod 2 := fun q =>
        q.elim 0 (fun q => supportRow (H source.value) (-q.phase).val)
      have readings := (original_first_window_binary_stream m hm alphabet (H source.value)
        (inside source.value) synthetic (fun _ b => b)
        (by intro v j s hs; simp [synthetic])).2.2.1 source.value (-source.phase) source.tail hs
      simp only [neg_neg, record] at readings
      rw [readings.1]
      unfold binaryCode
      split_ifs <;> simp

private theorem fiber_lower {Y : Type u} (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (H : ZMod 2 → Finset ℕ) (inside : ∀ v h, h ∈ H v → 1 ≤ h ∧ h ≤ m)
    (A B : ZMod 2 → Y) (distinct : ∀ v, A v ≠ B v)
    (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
      f (some ⟨v, -j, s⟩) = if j.val ∈ H v then B v else A v)
    (v : ZMod 2) (d : ℕ) (π : NarrowWindowCost.Selector m Y)
    (correct : FiberCorrect m hm alphabet f v d π) : binaryCost (H v) ≤ d := by
  classical
  let synthetic : Option (LiveRecord (2 * m - 2)) → Y := fun q =>
    q.elim (f none) (fun q => if (-q.phase).val ∈ H v then B q.value else A q.value)
  let label (w b : ZMod 2) : Y := if b = 0 then A w else B w
  have supplied := original_first_window_binary_stream m hm alphabet (H v) (inside v)
    synthetic label (by intro w j s hs; simp [synthetic, label, supportRow])
  have translated : FiberCorrect m hm alphabet synthetic v d π := by
    intro history
    dsimp only
    intro observed
    let w := history.flatMap (fun a => List.ofFn a.val)
    obtain ⟨c, bound, success⟩ := correct history observed
    have eq : synthetic (OriginalRecord (2 * m - 2) (by omega) w) =
        f (OriginalRecord (2 * m - 2) (by omega) w) := by
      have output : NarrowWindowCost.output (2 * m - 2) (by omega) w =
          endpointReading (OriginalRecord (2 * m - 2) (by omega) w) :=
        OriginalExecutionBridge.output_record (2 * m - 2) (by omega) w
      cases initial : OriginalRecord (2 * m - 2) (by omega) w with
      | none => simp [initial, synthetic]
      | some q =>
        have value : q.value = v := by
          rw [initial] at output
          change NarrowWindowCost.output _ _ w = some q.value at output
          exact Option.some.inj (output.symm.trans observed)
        have tail : q.tail < 2 * m - 2 := by
          unfold OriginalRecord at initial
          cases scan : (NarrowWindowCost.scanner (2 * m - 2) (by omega)).eval w with
          | none => simp [scan] at initial
          | some s =>
            simp only [scan, Option.map_some, Option.some.injEq] at initial
            simpa only [← congrArg LiveRecord.tail initial] using s.isLt
        have labels := target q.value (-q.phase) q.tail tail
        simp only [neg_neg] at labels
        have record : (⟨q.value, q.phase, q.tail⟩ : LiveRecord (2 * m - 2)) = q := by cases q; rfl
        rw [record] at labels
        change (if (-q.phase).val ∈ H v then B q.value else A q.value) = f (some q)
        rw [labels, value]
    refine ⟨c, bound, ?_⟩
    change NarrowWindowCost.execute _ _ π d w (some v) [] =
      some (synthetic (OriginalRecord (2 * m - 2) (by omega) w), c)
    rw [eq]
    exact success
  have labels : label v 0 ≠ label v 1 := by simpa [label] using distinct v
  by_cases empty : H v = ∅
  · simp [binaryCost, empty]
  by_cases zero : d = 0
  · subst d
    exact (empty (supplied.2.2.2.1 v labels π translated)).elim
  by_cases one : d = 1
  · subst d
    obtain ⟨W, _, _, _, even⟩ :=
      supplied.2.2.2.2 (Finset.nonempty_iff_ne_empty.mpr empty) v labels π translated
    simp [binaryCost, empty, even]
  · unfold binaryCost
    split_ifs <;> omega

def AdaptiveBitFeasible {Y : Type u} (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (f : Option (LiveRecord (2 * m - 2)) → Y) (b : ℕ) : Prop :=
  ∃ π : NarrowWindowCost.Selector m Y,
    FullPositiveWindowPrice.SelectorLegal (2 * m - 2) alphabet π ∧ π none [] = .inl (f none) ∧
    ∀ history : List (AllowedBlock (2 * m - 2) m alphabet),
      let w := history.flatMap (fun a => List.ofFn a.val)
      ∃ issued, PaidTrace π (NarrowWindowCost.output (2 * m - 2) (by omega) w)
        (OriginalRecord (2 * m - 2) (by omega) w) [] issued (f (OriginalRecord (2 * m - 2) (by omega) w)) ∧
        (archiveWords issued).length ≤ b

/-- The remembered free value selects a safe binary stream. Each original
history pays exactly its own branch length, including empty branches. -/
theorem original_first_window_adaptive_price {Y : Type u}
    (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (H : ZMod 2 → Finset ℕ) (inside : ∀ v h, h ∈ H v → 1 ≤ h ∧ h ≤ m)
    (A B : ZMod 2 → Y) (distinct : ∀ v, A v ≠ B v)
    (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
      f (some ⟨v, -j, s⟩) = if j.val ∈ H v then B v else A v) :
    GlobalAdaptivePrice (2 * m - 2) m (by omega) alphabet f = (worstCost H : ℕ∞) ∧
    (∀ d, OriginalAdaptiveFeasible (2 * m - 2) m (by omega) alphabet f d ↔ worstCost H ≤ d) ∧
    FullPositiveWindowPrice.SelectorLegal (2 * m - 2) alphabet
      (adaptiveSelector m H A B (f none)) ∧
    adaptiveSelector m H A B (f none) none [] = .inl (f none) ∧
    (∀ history : List (AllowedBlock (2 * m - 2) m alphabet),
      let w := history.flatMap (fun a => List.ofFn a.val)
      let q := OriginalRecord (2 * m - 2) (by omega) w
      let free := NarrowWindowCost.output (2 * m - 2) (by omega) w
      ∃ issued, PaidTrace (adaptiveSelector m H A B (f none)) free q [] issued (f q) ∧
        issued.map Prod.fst = q.elim [] (fun q => binaryWords m (H q.value)) ∧
        issued.length = sourceCost H q ∧ (archiveWords issued).length = m * sourceCost H q ∧
      none ∉ issued.map Prod.snd) ∧
    (∃ (v : ZMod 2) (history : List (AllowedBlock (2 * m - 2) m alphabet))
      (issued : NarrowWindowCost.Archive m),
      OriginalRecord (2 * m - 2) (by omega) (history.flatMap (fun a => List.ofFn a.val)) =
        some ⟨v, 0, 0⟩ ∧
      PaidTrace (k := 2 * m - 2) (adaptiveSelector m H A B (f none)) (some v) (some ⟨v, 0, 0⟩) [] issued
        (f (some ⟨v, 0, 0⟩)) ∧
      issued.length = worstCost H ∧ (archiveWords issued).length = m * worstCost H) ∧
    (∀ b, AdaptiveBitFeasible m hm alphabet f b ↔ m * worstCost H ≤ b) := by
  classical
  have legal : FullPositiveWindowPrice.SelectorLegal (2 * m - 2) alphabet
      (adaptiveSelector m H A B (f none)) := by
    intro free ar word selected localAlphabet
    exact short_legal _ m (by omega) (by omega) word
  have bottom : adaptiveSelector m H A B (f none) none [] = .inl (f none) := rfl
  have traces := branch_history_trace m hm H inside A B f target alphabet
  have bounded (q : Option (LiveRecord (2 * m - 2))) : sourceCost H q ≤ worstCost H := by
    cases q with
    | none => simp [sourceCost]
    | some q =>
      have values : q.value = 0 ∨ q.value = 1 := (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) q.value
      rcases values with e | e <;> simp [sourceCost, worstCost, e]
  have iff (d : ℕ) : OriginalAdaptiveFeasible (2 * m - 2) m (by omega) alphabet f d ↔
      worstCost H ≤ d := by
    constructor
    · rintro ⟨π, _, _, correct⟩
      apply max_le
      all_goals
        apply fiber_lower m hm alphabet H inside A B distinct f target _ d π
        intro history
        dsimp only
        intro observed
        obtain ⟨c, bound, success⟩ := correct history
        rw [observed] at success
        exact ⟨c, bound, success⟩
    · intro bound
      refine ⟨adaptiveSelector m H A B (f none), legal, bottom, ?_⟩
      intro history w
      obtain ⟨issued, traced, _, count, _⟩ := traces history
      refine ⟨sourceCost H (OriginalRecord (2 * m - 2) (by omega) w), (bounded _).trans bound, ?_⟩
      rw [execute_paid_trace _ m (by omega)]
      exact ⟨issued, traced, count, (bounded _).trans bound⟩
  refine ⟨FullPositiveWindowPrice.price_exact _ _ ((iff _).mpr le_rfl)
    (fun d feasible => (iff d).mp feasible), iff, legal, bottom, traces, ?_, ?_⟩
  ·
    let v : ZMod 2 := if binaryCost (H 0) ≤ binaryCost (H 1) then 1 else 0
    have maximizing : binaryCost (H v) = worstCost H := by
      unfold v worstCost
      split_ifs with order
      · exact (max_eq_right order).symm
      · exact (max_eq_left (by omega)).symm
    obtain ⟨history, state⟩ :=
      ((whole_first_zero_acquisition (2 * m - 2) m (by omega) (by omega) alphabet (fun _ => ())).1
        (some ⟨v, 0, 0⟩)).mp ⟨by change 0 < 2 * m - 2; omega, by simp⟩
    have record : OriginalRecord (2 * m - 2) (by omega)
        (history.flatMap (fun a => List.ofFn a.val)) = some ⟨v, 0, 0⟩ :=
      (OriginalExecutionBridge.record_history (2 * m - 2) m (by omega) alphabet history).trans state
    obtain ⟨issued, traced, _, count, bits, _⟩ := traces history
    have output : NarrowWindowCost.output (2 * m - 2) (by omega)
        (history.flatMap (fun a => List.ofFn a.val)) = some v := by
      have bridge : NarrowWindowCost.output (2 * m - 2) (by omega)
          (history.flatMap (fun a => List.ofFn a.val)) =
          endpointReading (OriginalRecord (2 * m - 2) (by omega)
            (history.flatMap (fun a => List.ofFn a.val))) :=
        OriginalExecutionBridge.output_record (2 * m - 2) (by omega) _
      rw [record] at bridge
      exact bridge
    refine ⟨v, history, issued, record, ?_, ?_, ?_⟩
    · simpa only [record, output] using traced
    · simpa only [record, sourceCost, maximizing] using count
    · simpa only [record, sourceCost, maximizing] using bits
  · intro b
    constructor
    · rintro ⟨π, lawful, root, paid⟩
      have feasible : OriginalAdaptiveFeasible (2 * m - 2) m (by omega) alphabet f (b / m) := by
        refine ⟨π, lawful, root, ?_⟩
        intro history w
        obtain ⟨issued, traced, bits⟩ := paid history
        rw [archive_length, Nat.mul_comm] at bits
        have bound : issued.length ≤ b / m := (Nat.le_div_iff_mul_le (by omega)).mpr
          (by simpa [Nat.mul_comm] using bits)
        refine ⟨issued.length, bound, ?_⟩
        rw [execute_paid_trace _ m (by omega)]
        exact ⟨issued, traced, rfl, bound⟩
      have bound := (iff _).mp feasible
      have bits := (Nat.le_div_iff_mul_le (by omega)).mp bound
      simpa [Nat.mul_comm] using bits
    · intro bound
      refine ⟨adaptiveSelector m H A B (f none), legal, bottom, ?_⟩
      intro history w
      obtain ⟨issued, traced, _, count, bits, _⟩ := traces history
      exact ⟨issued, traced, by rw [bits]; exact (Nat.mul_le_mul_left m (bounded _)).trans bound⟩

#print axioms original_first_window_adaptive_price
end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAdaptive
