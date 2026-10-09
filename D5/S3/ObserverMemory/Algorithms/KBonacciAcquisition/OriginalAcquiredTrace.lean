/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: One actual acquired archive preserves INITIAL records and exact chronological paid traces. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowChargeInverse

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe z

namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open LiteralModel EndpointCells OriginalNarrowCost OriginalExecutionBridge WindowChargeInverse
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open D5.S0.Tower.DBonacci.Names
open scoped BigOperators

private theorem record_append (k : ℕ) (hk : 2 ≤ k) (w b : List Bool) :
    OriginalRecord k (by omega) (w ++ b) =
      runWord (bitUpdate k) b (OriginalRecord k (by omega) w) :=
  OriginalExecutionBridge.record_append k hk w b

private theorem output_record (k : ℕ) (hk : 0 < k) (w : List Bool) :
    NarrowWindowCost.output k hk w = endpointReading (OriginalRecord k hk w) :=
  OriginalExecutionBridge.output_record k hk w

private theorem execute_same {Y : Type z} (k m : ℕ) (hk : 2 ≤ k)
    (π : NarrowWindowCost.Selector m Y) (d : ℕ) (w : List Bool)
    (y₀ : Option (ZMod 2)) (archive : NarrowWindowCost.Archive m) :
    NarrowWindowCost.execute k (by omega) π d w y₀ archive =
      NativeExecute π d (OriginalRecord k (by omega) w) y₀ archive :=
  OriginalExecutionBridge.execute_same k m hk π d w y₀ archive

/-- The absolute issued-block vertex; its index counts every complete paid word. -/
def vertex (k m a i : ℕ) : ZMod (k + 1) := ((a * m + i : ℕ) : ZMod (k + 1))

/-- The complete ordered physical window, including both endpoint vertices. -/
def physicalWindow (k m a : ℕ) : Set (ZMod (k + 1)) :=
  {j | ∃ i, i ≤ m ∧ j = vertex k m a i}

/-- Every position of every chronological issued block, including zeros and waits. -/
def archiveWords {m : ℕ} (archive : NarrowWindowCost.Archive m) : List Bool :=
  archive.flatMap (fun entry => List.ofFn entry.1)

/-- The complete chronological archive is read from the same original literal word.
Only the endpoint after each complete appended block is tested. -/
def ActualArchive {m : ℕ} (k : ℕ) (hk : 0 < k) :
    List Bool → NarrowWindowCost.Archive m → Prop
  | _, [] => True
  | w, (B, reply) :: rest =>
      NarrowWindowCost.output k hk (w ++ List.ofFn B) = reply ∧
        ActualArchive k hk (w ++ List.ofFn B) rest

/-- Splitting an archive retains the actual word produced by its entire first part. -/
theorem actual_archive_append {m : ℕ} (k : ℕ) (hk : 0 < k)
    (w : List Bool) (first rest : NarrowWindowCost.Archive m) :
    ActualArchive k hk w (first ++ rest) ↔
      ActualArchive k hk w first ∧
        ActualArchive k hk (w ++ archiveWords first) rest := by
  induction first generalizing w with
  | nil => simp [ActualArchive, archiveWords]
  | cons entry first ih =>
      rcases entry with ⟨B, reply⟩
      simp only [List.cons_append, ActualArchive, ih, archiveWords,
        List.flatMap_cons, List.append_assoc, and_assoc]

/-- The entire actual source fiber, filtered by its acquired archive, retains
the INITIAL record together with the current record of that same history. -/
def AcquiredPairs (k m : ℕ) (hk : 0 < k) (localAlphabet : Bool)
    (y₀ : Option (ZMod 2)) (archive : NarrowWindowCost.Archive m) :
    Set (Option (LiveRecord k) × Option (LiveRecord k)) :=
  {pair | ∃ history : List (AllowedBlock k m localAlphabet),
    let w := history.flatMap (fun action => List.ofFn action.val)
    NarrowWindowCost.output k hk w = y₀ ∧ ActualArchive k hk w archive ∧
      pair.1 = OriginalRecord k hk w ∧
      pair.2 = OriginalRecord k hk (w ++ archiveWords archive)}

/-- One actual endpoint fiber equals appending that block and reply to the
whole acquired archive, with the original source coordinate unchanged. -/
theorem actual_archive_reply (k m : ℕ) (hk : 2 ≤ k) (localAlphabet : Bool)
    (sourceHistory : List (AllowedBlock k m localAlphabet))
    (archive : NarrowWindowCost.Archive m)
    (sourceArchive : ActualArchive k (by omega)
      (sourceHistory.flatMap (fun action => List.ofFn action.val)) archive)
    (B : Fin m → Bool) (reply : Option (ZMod 2)) :
    let w := sourceHistory.flatMap (fun action => List.ofFn action.val)
    let y₀ := NarrowWindowCost.output k (by omega) w
    let cell : CandidateState k (Option (LiveRecord k)) :=
      ⟨AcquiredPairs k m (by omega) localAlphabet y₀ archive,
        ⟨(OriginalRecord k (by omega) w,
          OriginalRecord k (by omega) (w ++ archiveWords archive)),
          sourceHistory, rfl, sourceArchive, rfl, rfl⟩⟩
    replyFiber k m cell B reply =
      AcquiredPairs k m (by omega) localAlphabet y₀ (archive ++ [(B, reply)]) := by
  intro sourceWord y₀ cell
  have attained : cell.val = AcquiredPairs k m (by omega) localAlphabet y₀ archive := rfl
  ext pair
  constructor
  · rintro ⟨current, member, updated, observed⟩
    rw [attained] at member
    obtain ⟨history, initialOutput, matched, initial, currentEq⟩ := member
    let w := history.flatMap (fun action => List.ofFn action.val)
    have nextRecord : OriginalRecord k (by omega)
        (w ++ archiveWords (archive ++ [(B, reply)])) = runBits k B current := by
      simp only [archiveWords, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, ← List.append_assoc]
      rw [record_append k hk]
      change runBits k B (OriginalRecord k (by omega) (w ++ archiveWords archive)) =
        runBits k B current
      have same : current = OriginalRecord k (by omega) (w ++ archiveWords archive) := currentEq
      rw [same]
    refine ⟨history, initialOutput, ?_, initial, updated.symm.trans nextRecord.symm⟩
    apply (actual_archive_append k (by omega) w archive [(B, reply)]).mpr
    refine ⟨matched, ?_⟩
    change NarrowWindowCost.output k (by omega)
      ((w ++ archiveWords archive) ++ List.ofFn B) = reply ∧ True
    refine ⟨?_, trivial⟩
    rw [output_record, record_append k hk, ← currentEq]
    change endpointReading (runBits k B current) = reply
    rw [updated]
    exact observed
  · rintro ⟨history, initialOutput, matched, initial, currentEq⟩
    let w := history.flatMap (fun action => List.ofFn action.val)
    let current := OriginalRecord k (by omega) (w ++ archiveWords archive)
    obtain ⟨before, last⟩ :=
      (actual_archive_append k (by omega) w archive [(B, reply)]).mp matched
    have nextRecord : OriginalRecord k (by omega)
        (w ++ archiveWords (archive ++ [(B, reply)])) = runBits k B current := by
      simp only [archiveWords, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, ← List.append_assoc]
      rw [record_append k hk]
      rfl
    refine ⟨current, ?_, nextRecord.symm.trans currentEq.symm, ?_⟩
    · rw [attained]
      exact ⟨history, initialOutput, before, initial, rfl⟩
    · change NarrowWindowCost.output k (by omega)
        ((w ++ archiveWords archive) ++ List.ofFn B) = reply ∧ True at last
      rw [output_record, record_append k hk] at last
      change endpointReading pair.2 = reply
      rw [currentEq]
      change endpointReading
        (OriginalRecord k (by omega) (w ++ archiveWords (archive ++ [(B, reply)]))) = reply
      rw [nextRecord]
      exact last.1

/-- A stopped execution emits precisely these paid complete blocks. A leaf
has no further actions; each subsequent choice sees only its own prior archive. -/
def PaidTrace {Y : Type z} {k m : ℕ} (π : NarrowWindowCost.Selector m Y)
    (y₀ : Option (ZMod 2)) : Option (LiveRecord k) →
      NarrowWindowCost.Archive m → NarrowWindowCost.Archive m → Y → Prop
  | _, archive, [], y => π y₀ archive = .inl y
  | q, archive, (B, reply) :: rest, y =>
      π y₀ archive = .inr B ∧ reply = endpointReading (runBits k B q) ∧
        PaidTrace π y₀ (runBits k B q) (archive ++ [(B, reply)]) rest y

/-- The returned fee is exactly the length of the actually stopped trace,
not the supplied horizon. The equivalence also includes zero-budget leaves. -/
theorem native_execute_paid_trace {Y : Type z} (k m : ℕ)
    (π : NarrowWindowCost.Selector m Y) (d : ℕ)
    (q : Option (LiveRecord k)) (y₀ : Option (ZMod 2))
    (archive : NarrowWindowCost.Archive m) (y : Y) (c : ℕ) :
    NativeExecute π d q y₀ archive = some (y, c) ↔
      ∃ issued, PaidTrace π y₀ q archive issued y ∧ issued.length = c ∧ c ≤ d := by
  induction d generalizing q archive y c with
  | zero =>
      constructor
      · intro success
        cases chosen : π y₀ archive with
        | inl label =>
            simp only [NativeExecute, Nat.rec_zero, chosen, Option.some.injEq,
              Prod.mk.injEq] at success
            rcases success with ⟨rfl, rfl⟩
            exact ⟨[], chosen, rfl, le_rfl⟩
        | inr B => simp [NativeExecute, Nat.rec_zero, chosen] at success
      · rintro ⟨issued, traced, counted, bounded⟩
        have empty : issued = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst issued
        have zero : c = 0 := by simpa using counted.symm
        subst c
        change π y₀ archive = .inl y at traced
        simp only [NativeExecute, Nat.rec_zero, traced, List.length_nil]
  | succ d ih =>
      constructor
      · intro success
        cases chosen : π y₀ archive with
        | inl label =>
            simp only [NativeExecute, Nat.rec_add_one, chosen, Option.some.injEq,
              Prod.mk.injEq] at success
            rcases success with ⟨rfl, rfl⟩
            exact ⟨[], chosen, rfl, Nat.zero_le _⟩
        | inr B =>
            simp only [NativeExecute, Nat.rec_add_one, chosen] at success
            obtain ⟨⟨label, fee⟩, next, equal⟩ := Option.map_eq_some_iff.mp success
            rcases Prod.mk.inj equal with ⟨rfl, rfl⟩
            obtain ⟨issued, traced, counted, bounded⟩ :=
              (ih (runBits k B q)
                (archive ++ [(B, endpointReading (runBits k B q))]) label fee).mp next
            exact ⟨(B, endpointReading (runBits k B q)) :: issued,
              ⟨chosen, rfl, traced⟩, by simp only [List.length_cons, counted],
              Nat.succ_le_succ bounded⟩
      · rintro ⟨issued, traced, counted, bounded⟩
        cases issued with
        | nil =>
            have zero : c = 0 := by simpa using counted.symm
            subst c
            change π y₀ archive = .inl y at traced
            simp only [NativeExecute, Nat.rec_add_one, traced, List.length_nil]
        | cons entry rest =>
            rcases entry with ⟨B, reply⟩
            obtain ⟨chosen, observed, nextTrace⟩ := traced
            subst reply
            have next := (ih (runBits k B q)
              (archive ++ [(B, endpointReading (runBits k B q))]) y rest.length).mpr
                ⟨rest, nextTrace, rfl, by simp only [List.length_cons] at counted; omega⟩
            change (match π y₀ archive with
              | .inl label => some (label, 0)
              | .inr word =>
                  (NativeExecute π d (runBits k word q) y₀
                    (archive ++ [(word, endpointReading (runBits k word q))])).map
                    (fun result => (result.1, result.2 + 1))) = some (y, c)
            simp only [chosen, next, Option.map_some]
            exact congrArg (fun fee => some (y, fee))
              (by simpa only [List.length_cons] using counted)

/-- Every endpoint of a stopped native trace is the original integer-weight
readout of that same history after all its preceding complete issued blocks. -/
private theorem paid_trace_actual_archive {Y : Type z} (k m : ℕ) (hk : 2 ≤ k)
    (π : NarrowWindowCost.Selector m Y) (y₀ : Option (ZMod 2))
    (w : List Bool) (archive issued : NarrowWindowCost.Archive m) (y : Y)
    (traced : PaidTrace π y₀ (OriginalRecord k (by omega) w) archive issued y) :
    ActualArchive k (by omega) w issued := by
  induction issued generalizing w archive with
  | nil => trivial
  | cons entry issued ih =>
      rcases entry with ⟨B, reply⟩
      obtain ⟨chosen, observed, nextTrace⟩ := traced
      refine ⟨?_, ih (w ++ List.ofFn B) (archive ++ [(B, reply)]) ?_⟩
      · rw [output_record, record_append k hk]
        exact observed.symm
      · simpa only [record_append k hk, runBits] using nextTrace

/-- Original literal execution and the stopped paid trace agree on the exact
label and paid fee, including rejection, clearing, and terminal early stops. -/
theorem execute_paid_trace {Y : Type z} (k m : ℕ) (hk : 2 ≤ k)
    (π : NarrowWindowCost.Selector m Y) (d : ℕ) (w : List Bool)
    (y₀ : Option (ZMod 2)) (archive : NarrowWindowCost.Archive m) (y : Y) (c : ℕ) :
    NarrowWindowCost.execute k (by omega) π d w y₀ archive = some (y, c) ↔
      ∃ issued, PaidTrace π y₀ (OriginalRecord k (by omega) w) archive issued y ∧
        issued.length = c ∧ c ≤ d := by
  rw [execute_same k m hk]
  exact native_execute_paid_trace k m π d _ y₀ archive y c

/-- The endpoint already present at the end of the entire chronological archive. -/
def archiveEndpoint {m : ℕ} (free : Option (ZMod 2)) : NarrowWindowCost.Archive m → Option (ZMod 2)
  | [] => free
  | (_, reply) :: rest => archiveEndpoint reply rest

private theorem archive_length {m : ℕ} (archive : NarrowWindowCost.Archive m) :
    (archiveWords archive).length = archive.length * m := by
  induction archive with
  | nil => simp [archiveWords]
  | cons entry rest ih =>
      simp only [archiveWords, List.flatMap_cons, List.length_append, List.length_ofFn,
        List.length_cons]
      change m + (archiveWords rest).length = (rest.length + 1) * m
      rw [ih, Nat.add_mul, Nat.one_mul]
      omega

private theorem archive_endpoint_actual (k m : ℕ) (hk : 0 < k)
    (w : List Bool) (archive : NarrowWindowCost.Archive m)
    (matched : ActualArchive k hk w archive) :
    NarrowWindowCost.output k hk (w ++ archiveWords archive) =
      archiveEndpoint (NarrowWindowCost.output k hk w) archive := by
  induction archive generalizing w with
  | nil => simp [archiveWords, archiveEndpoint]
  | cons entry rest ih =>
      rcases entry with ⟨B, reply⟩
      obtain ⟨last, next⟩ := matched
      simpa only [archiveWords, List.flatMap_cons, List.append_assoc,
        archiveEndpoint, last] using ih (w ++ List.ofFn B) next

private theorem original_live_coordinates (k : ℕ) (hk : 0 < k)
    (w : List Bool) (q : LiveRecord k) (live : OriginalRecord k hk w = some q) :
    q.phase = (w.length : ZMod (k + 1)) ∧ q.tail < k := by
  unfold OriginalRecord at live
  obtain ⟨tail, accepted, equal⟩ := Option.map_eq_some_iff.mp live
  cases equal
  exact ⟨rfl, tail.isLt⟩

/-- INITIAL phases retained by this entire actual acquired archive. -/
def initialSupport (k m : ℕ) (hk : 0 < k) (localAlphabet : Bool)
    (v : ZMod 2) (archive : NarrowWindowCost.Archive m) : Set (ZMod (k + 1)) :=
  {j | ∃ initial : LiveRecord k, ∃ current,
    (some initial, current) ∈ AcquiredPairs k m hk localAlphabet (some v) archive ∧
      j = -initial.phase}

/-- A successful positive endpoint forces the physical parent charge on every
retained INITIAL history; its current phase includes every paid archived block. -/
theorem actual_positive_coordinates (k m : ℕ) (hk : 3 ≤ k) (short : m < k)
    (localAlphabet : Bool) (v previous : ZMod 2) (archive : NarrowWindowCost.Archive m)
    (parent : Fin m → Bool)
    (prior : archiveEndpoint (some v) archive = some previous) :
    let acquired := archive ++ [(parent, some (previous + 1))]
    let A := initialSupport k m (by omega) localAlphabet v acquired
    A ⊆ physicalWindow k m archive.length ∧
    (∀ j ∈ A, wordIncrement k (-j + ((archive.length * m : ℕ) : ZMod (k + 1))) parent = 1) ∧
    ∀ pair ∈ AcquiredPairs k m (by omega) localAlphabet (some v) acquired,
      ∃ initial current : LiveRecord k,
        pair.1 = some initial ∧ pair.2 = some current ∧
        current.value = previous + 1 ∧ current.tail < k ∧
        current.phase = initial.phase + (((archive.length + 1) * m : ℕ) : ZMod (k + 1)) := by
  intro acquired A
  have coordinates (pair) (member : pair ∈ AcquiredPairs k m (by omega)
      localAlphabet (some v) acquired) :
      ∃ initial current : LiveRecord k,
        pair.1 = some initial ∧ pair.2 = some current ∧ current.value = previous + 1 ∧
        current.tail < k ∧
        current.phase = initial.phase + (((archive.length + 1) * m : ℕ) : ZMod (k + 1)) ∧
        wordIncrement k (initial.phase + ((archive.length * m : ℕ) : ZMod (k + 1))) parent = 1 := by
    obtain ⟨history, free, matched, source, endpoint⟩ := member
    let w := history.flatMap (fun action => List.ofFn action.val)
    obtain ⟨before, last⟩ := (actual_archive_append k (by omega) w archive
      [(parent, some (previous + 1))]).mp matched
    have beforeOutput : NarrowWindowCost.output k (by omega) (w ++ archiveWords archive) =
        some previous := by
      rw [archive_endpoint_actual k m (by omega) w archive before, free, prior]
    have nextOutput : NarrowWindowCost.output k (by omega)
        ((w ++ archiveWords archive) ++ List.ofFn parent) = some (previous + 1) := last.1
    rw [output_record] at free beforeOutput nextOutput
    change endpointReading (OriginalRecord k (by omega) w) = some v at free
    cases initialEq : OriginalRecord k (by omega) w with
    | none => simp only [initialEq, endpointReading] at free; cases free
    | some initial =>
      cases beforeEq : OriginalRecord k (by omega) (w ++ archiveWords archive) with
      | none => simp only [beforeEq, endpointReading] at beforeOutput; cases beforeOutput
      | some old =>
        cases currentEq : OriginalRecord k (by omega)
            ((w ++ archiveWords archive) ++ List.ofFn parent) with
        | none => simp only [currentEq, endpointReading] at nextOutput; cases nextOutput
        | some current =>
          have initialCoordinates := original_live_coordinates k (by omega) w initial initialEq
          have oldCoordinates := original_live_coordinates k (by omega)
            (w ++ archiveWords archive) old beforeEq
          have currentCoordinates := original_live_coordinates k (by omega)
            ((w ++ archiveWords archive) ++ List.ofFn parent) current currentEq
          have oldValue : old.value = previous := by
            simpa only [beforeEq, endpointReading, Option.some.injEq] using beforeOutput
          have currentValue : current.value = previous + 1 := by
            simpa only [currentEq, endpointReading, Option.some.injEq] using nextOutput
          have oldPhase : old.phase = initial.phase + ((archive.length * m : ℕ) : ZMod (k + 1)) := by
            rw [oldCoordinates.1, initialCoordinates.1, List.length_append, archive_length, Nat.cast_add]
          have updated : runBits k parent (some old) = some current := by
            rw [← beforeEq]
            change Prediction.ControlledBehaviorUniversality.runWord (bitUpdate k)
              (List.ofFn parent) (OriginalRecord k (by omega) (w ++ archiveWords archive)) = _
            rw [← record_append k (by omega)]
            exact currentEq
          have model := (literal_block_execution k (by omega) m parent old.value old.phase old.tail oldCoordinates.2).1
          have safe : runAdmissible (k - 1) (k - 1 - old.tail) m parent = true := by
            cases scan : runAdmissible (k - 1) (k - 1 - old.tail) m parent with
            | true => rfl
            | false => simp only [scan, Bool.false_eq_true, ↓reduceIte] at model; rw [updated] at model; cases model
          simp only [safe, ↓reduceIte, updated] at model
          have values := congrArg (fun q : LiveRecord k => q.value) (Option.some.inj model)
          have increment : wordIncrement k old.phase parent = 1 := by
            rw [oldValue, currentValue] at values
            linear_combination -values
          have currentPhase : current.phase = initial.phase +
              (((archive.length + 1) * m : ℕ) : ZMod (k + 1)) := by
            rw [currentCoordinates.1, initialCoordinates.1, List.length_append,
              List.length_append, List.length_ofFn, archive_length]
            push_cast
            ring
          have finalEq : pair.2 = some current := by
            rw [endpoint]
            change OriginalRecord k (by omega) (w ++ archiveWords acquired) = some current
            simpa only [acquired, archiveWords, List.flatMap_append, List.flatMap_cons,
              List.flatMap_nil, List.append_nil, List.append_assoc] using currentEq
          exact ⟨initial, current, source.trans initialEq, finalEq, currentValue,
            currentCoordinates.2, currentPhase, by simpa only [oldPhase] using increment⟩
  have charged (j : ZMod (k + 1)) (member : j ∈ A) :
      wordIncrement k (-j + ((archive.length * m : ℕ) : ZMod (k + 1))) parent = 1 := by
    obtain ⟨initial, current, member, index⟩ := member
    obtain ⟨initial', current', same, next, value, tail, phase, charge⟩ :=
      coordinates (some initial, current) member
    have equal : initial' = initial := Option.some.inj same.symm
    subst initial'
    simpa only [index, neg_neg] using charge
  refine ⟨?_, charged, ?_⟩
  · intro j member
    by_contra outside
    let r : ZMod (k + 1) := j - ((archive.length * m : ℕ) : ZMod (k + 1))
    have beyond : m < r.val := by
      by_contra h
      have bounded : r.val ≤ m := by omega
      apply outside
      refine ⟨r.val, bounded, ?_⟩
      have cast := ZMod.natCast_zmod_val r
      dsimp [r] at cast
      simp only [vertex, Nat.cast_add]
      linear_combination -cast
    have zero : wordIncrement k (-j + ((archive.length * m : ℕ) : ZMod (k + 1))) parent = 0 := by
      have derivative := increment_derivative k (by omega) m short parent r
      have phase : -r = -j + ((archive.length * m : ℕ) : ZMod (k + 1)) := by dsimp [r]; ring
      rw [phase] at derivative
      simpa [extendedBit, show ¬ r.val < m by omega,
        show ¬ r.val - 1 < m by omega, show r.val ≠ 0 by omega] using derivative
    rw [charged j member] at zero
    norm_num at zero
  · intro pair member
    obtain ⟨initial, current, source, endpoint, value, tail, phase, charge⟩ := coordinates pair member
    exact ⟨initial, current, source, endpoint, value, tail, phase⟩



private theorem paid_trace_acquired_pair {Y : Type z} (k m : ℕ) (hk : 2 ≤ k)
    (localAlphabet : Bool) (π : NarrowWindowCost.Selector m Y)
    (history : List (AllowedBlock k m localAlphabet)) (y₀ : Option (ZMod 2))
    (archive issued : NarrowWindowCost.Archive m) (initial : Option (LiveRecord k)) (y : Y)
    (free : NarrowWindowCost.output k (by omega)
      (history.flatMap (fun action => List.ofFn action.val)) = y₀)
    (matched : ActualArchive k (by omega)
      (history.flatMap (fun action => List.ofFn action.val)) archive)
    (member : (initial, OriginalRecord k (by omega)
      (history.flatMap (fun action => List.ofFn action.val) ++ archiveWords archive)) ∈
        AcquiredPairs k m (by omega) localAlphabet y₀ archive)
    (traced : PaidTrace π y₀ (OriginalRecord k (by omega)
      (history.flatMap (fun action => List.ofFn action.val) ++ archiveWords archive)) archive issued y) :
    (initial, OriginalRecord k (by omega)
      (history.flatMap (fun action => List.ofFn action.val) ++ archiveWords (archive ++ issued))) ∈
        AcquiredPairs k m (by omega) localAlphabet y₀ (archive ++ issued) := by
  induction issued generalizing archive with
  | nil => simpa only [List.append_nil] using member
  | cons entry issued ih =>
    rcases entry with ⟨B, reply⟩
    obtain ⟨chosen, observed, nextTrace⟩ := traced
    let w := history.flatMap (fun action => List.ofFn action.val)
    let current := OriginalRecord k (by omega) (w ++ archiveWords archive)
    have nextRecord : OriginalRecord k (by omega)
        (w ++ archiveWords (archive ++ [(B, reply)])) = runBits k B current := by
      simp only [archiveWords, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, ← List.append_assoc]
      exact record_append k hk _ _
    have fiber := actual_archive_reply k m hk localAlphabet history archive matched B reply
    dsimp only at fiber
    simp only [free] at fiber
    have nextMember : (initial, OriginalRecord k (by omega)
        (w ++ archiveWords (archive ++ [(B, reply)]))) ∈
        AcquiredPairs k m (by omega) localAlphabet y₀ (archive ++ [(B, reply)]) := by
      rw [nextRecord, ← fiber]
      exact ⟨current, member, rfl, observed.symm⟩
    have nextMatched : ActualArchive k (by omega) w (archive ++ [(B, reply)]) :=
      (actual_archive_append k (by omega) w archive [(B, reply)]).mpr
        ⟨matched, by
          refine ⟨?_, trivial⟩
          rw [output_record, record_append k hk]
          exact observed.symm⟩
    have hfinal := ih (archive ++ [(B, reply)]) nextMatched nextMember
      (by
        change PaidTrace π y₀ (OriginalRecord k (by omega)
          (w ++ archiveWords (archive ++ [(B, reply)]))) _ issued y
        rw [nextRecord]
        exact nextTrace)
    simpa only [List.append_assoc, List.singleton_append] using hfinal

/-- The exact paid trace stays in the same original acquired fiber and retains
its immutable INITIAL target, even when a later endpoint rejects. -/
theorem acquired_execution_trace {Y : Type z} (k m : ℕ) (hk : 2 ≤ k)
    (localAlphabet : Bool) (f : Option (LiveRecord k) → Y)
    (history : List (AllowedBlock k m localAlphabet))
    (y₀ : Option (ZMod 2)) (archive : NarrowWindowCost.Archive m)
    (free : NarrowWindowCost.output k (by omega)
      (history.flatMap (fun action => List.ofFn action.val)) = y₀)
    (matched : ActualArchive k (by omega)
      (history.flatMap (fun action => List.ofFn action.val)) archive)
    (π : NarrowWindowCost.Selector m Y) (d c : ℕ) :
    let w := history.flatMap (fun action => List.ofFn action.val)
    let initial := OriginalRecord k (by omega) w
    let current := OriginalRecord k (by omega) (w ++ archiveWords archive)
    NarrowWindowCost.execute k (by omega) π d (w ++ archiveWords archive) y₀ archive =
        some (f initial, c) ↔
      ∃ issued, PaidTrace π y₀ current archive issued (f initial) ∧
        issued.length = c ∧ c ≤ d ∧ ActualArchive k (by omega) w (archive ++ issued) ∧
        (initial, OriginalRecord k (by omega) (w ++ archiveWords (archive ++ issued))) ∈
          AcquiredPairs k m (by omega) localAlphabet y₀ (archive ++ issued) := by
  intro w initial current
  rw [execute_paid_trace k m hk]
  constructor
  · rintro ⟨issued, traced, counted, bounded⟩
    have source : (initial, current) ∈ AcquiredPairs k m (by omega) localAlphabet y₀ archive :=
      ⟨history, free, matched, rfl, rfl⟩
    exact ⟨issued, traced, counted, bounded,
      (actual_archive_append k (by omega) w archive issued).mpr
        ⟨matched, paid_trace_actual_archive k m hk π y₀ _ archive issued _ traced⟩,
      paid_trace_acquired_pair k m hk localAlphabet π history y₀ archive issued initial _
        free matched source traced⟩
  · rintro ⟨issued, traced, counted, bounded, _, _⟩
    exact ⟨issued, traced, counted, bounded⟩

private def alternatingWord (m : ℕ) : Fin m → Bool :=
  fun i => decide (i.val % 2 = 0)

private theorem alternating_tail (m : ℕ) (s : ℕ) :
    tailAfter s (alternatingWord m) =
      if m = 0 then s else if m = 1 then s + 1 else if m % 2 = 0 then 0 else 1 := by
  induction m using Nat.strong_induction_on generalizing s with
  | h m ih =>
    cases m with
    | zero => rfl
    | succ n =>
      cases n with
      | zero => simp [tailAfter, alternatingWord]
      | succ r =>
        have shift : Fin.tail (Fin.tail (alternatingWord (r + 2))) = alternatingWord r := by
          funext i
          have shiftIndex : (i.val + 1 + 1) % 2 = i.val % 2 := by omega
          simp only [alternatingWord, Fin.tail, Fin.val_succ, shiftIndex]
        have first : alternatingWord (r + 2) 0 = true := by simp [alternatingWord]
        have second : Fin.tail (alternatingWord (r + 2)) 0 = false := by
          simp [alternatingWord, Fin.tail]
        rw [show r + 1 + 1 = r + 2 by omega]
        simp only [tailAfter, first, second, Bool.false_eq_true, ↓reduceIte]
        rw [shift, ih r (by omega) 0]
        by_cases zero : r = 0
        · subst r; simp
        by_cases one : r = 1
        · subst r; simp
        have same : (r + 2) % 2 = r % 2 := by omega
        simp [zero, one, same, show r + 2 ≠ 0 by omega, show r + 2 ≠ 1 by omega]

private theorem acquired_tail (k m : ℕ) (hk : 3 ≤ k) (localAlphabet : Bool)
    (y₀ : Option (ZMod 2)) (archive : NarrowWindowCost.Archive m)
    (parent : Fin m → Bool) (reply : Option (ZMod 2)) (sigma : ℕ)
    (terminal : ∀ s, tailAfter s parent = sigma) :
    ∀ initial current : LiveRecord k,
      (some initial, some current) ∈ AcquiredPairs k m (by omega) localAlphabet y₀
        (archive ++ [(parent, reply)]) → current.tail = sigma := by
  intro initial current member
  obtain ⟨history, free, matched, initialEq, currentEq⟩ := member
  let w := history.flatMap (fun action => List.ofFn action.val)
  let before := OriginalRecord k (by omega) (w ++ archiveWords archive)
  have updated : runBits k parent before = some current := by
    change some current = OriginalRecord k (by omega)
      (w ++ archiveWords (archive ++ [(parent, reply)])) at currentEq
    rw [currentEq]
    simp only [archiveWords, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, ← List.append_assoc]
    exact (record_append k (by omega) (w ++ archiveWords archive) (List.ofFn parent)).symm
  cases oldEq : before with
  | none =>
    rw [oldEq] at updated
    obtain ⟨_, _, absorbed, _⟩ := CoprimeSingletonLower.singleton_tree_obstruction k 2 1
      (by omega) (by omega) (by omega) (by omega) (by omega) false true (by decide) 0 false
    have gone : runBits k parent none = none := absorbed (List.ofFn parent)
    rw [gone] at updated
    cases updated
  | some old =>
    have oldTail : old.tail < k :=
      (original_live_coordinates k (by omega) _ old oldEq).2
    rw [oldEq] at updated
    have model := (literal_block_execution k (by omega) m parent old.value old.phase old.tail oldTail).1
    change runBits k parent (some old) = _ at model
    rw [updated] at model
    cases safe : runAdmissible (k - 1) (k - 1 - old.tail) m parent with
    | false => simp only [safe, Bool.false_eq_true, ↓reduceIte] at model; cases model
    | true =>
      simp only [safe, ↓reduceIte] at model
      have tails := congrArg LiveRecord.tail (Option.some.inj model)
      exact tails.trans (terminal old.tail)

/-- Full positive support, rather than positive output alone, fixes the actual
alternating parent and tail one; the unique inverse is the native prefix word. -/
theorem full_positive_parent (k m : ℕ) (hm : 3 ≤ m) (odd : Odd m) (short : m < k)
    (localAlphabet : Bool) (v previous : ZMod 2) (archive : NarrowWindowCost.Archive m)
    (parent : Fin m → Bool) (prior : archiveEndpoint (some v) archive = some previous)
    (full : initialSupport k m (by omega) localAlphabet v
      (archive ++ [(parent, some (previous + 1))]) = physicalWindow k m archive.length) :
    (∀ i : Fin m, parent i = decide (i.val % 2 = 0)) ∧
      ∀ initial current : LiveRecord k,
        (some initial, some current) ∈ AcquiredPairs k m (by omega) localAlphabet (some v)
          (archive ++ [(parent, some (previous + 1))]) → current.tail = 1 := by
  have facts := actual_positive_coordinates k m (by omega) short localAlphabet
    v previous archive parent prior
  have even : (∑ h ∈ Finset.range (m + 1), (1 : ZMod 2)) = 0 := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_one]
    apply (ZMod.natCast_eq_zero_iff (m + 1) 2).mpr
    obtain ⟨r, hr⟩ := odd
    exact ⟨r + 1, by omega⟩
  have inverse := short_window_charge_inverse k (by omega) m (by omega) short
    (fun _ => (1 : ZMod 2)) even
  have parentCharge : ∀ j : ZMod (k + 1), wordIncrement k (-j) parent =
      windowCharge k m (fun _ => (1 : ZMod 2)) j := by
    intro j
    let absolute : ZMod (k + 1) := j + ((archive.length * m : ℕ) : ZMod (k + 1))
    have rotated : -absolute + ((archive.length * m : ℕ) : ZMod (k + 1)) = -j := by
      dsimp [absolute]; ring
    by_cases inside : j.val ≤ m
    · have member : absolute ∈ initialSupport k m (by omega) localAlphabet v
          (archive ++ [(parent, some (previous + 1))]) := by
        rw [full]
        refine ⟨j.val, inside, ?_⟩
        simp only [absolute, vertex, Nat.cast_add, ZMod.natCast_zmod_val]
        ring
      have charged := facts.2.1 absolute member
      simpa only [rotated, windowCharge, if_pos inside] using charged
    · have derivative := increment_derivative k (by omega) m short parent j
      simpa [windowCharge, inside, extendedBit, show ¬ j.val < m by omega,
        show ¬ j.val - 1 < m by omega, show j.val ≠ 0 by omega] using derivative
  have forced : parent = alternatingWord m := by
    rw [inverse.2.2.2 parent parentCharge]
    funext i
    simp only [prefixWord, alternatingWord, Finset.sum_const, Finset.card_range, nsmul_one]
    congr 1
    apply propext
    constructor
    · intro nz
      by_contra ne
      have evenIndex : 2 ∣ i.val + 1 := Nat.dvd_of_mod_eq_zero (by omega)
      exact nz ((ZMod.natCast_eq_zero_iff (i.val + 1) 2).mpr evenIndex)
    · intro evenIndex zero
      have divided := (ZMod.natCast_eq_zero_iff (i.val + 1) 2).mp zero
      obtain ⟨r, hr⟩ := divided
      omega
  have parity : m % 2 = 1 := by obtain ⟨r, hr⟩ := odd; omega
  refine ⟨fun i => congrFun forced i, ?_⟩
  exact acquired_tail k m (by omega) localAlphabet (some v) archive parent
    (some (previous + 1)) 1 (fun s => by
      rw [forced, alternating_tail]
      simp [show m ≠ 0 by omega, show m ≠ 1 by omega, show m % 2 ≠ 0 by omega])

/-- Every actual full-positive source retains its INITIAL label, exact current
phase and tail, and original chronological execution with its exact paid fee. -/
theorem full_positive_history_trace {Y : Type z} (k m : ℕ) (hm : 3 ≤ m)
    (odd : Odd m) (critical : k = m + 1) (localAlphabet : Bool)
    (v previous : ZMod 2) (archive : NarrowWindowCost.Archive m) (parent : Fin m → Bool)
    (prior : archiveEndpoint (some v) archive = some previous)
    (full : initialSupport k m (by omega) localAlphabet v
      (archive ++ [(parent, some (previous + 1))]) = physicalWindow k m archive.length)
    (f : Option (LiveRecord k) → Y) (labels : ZMod (k + 1) → Y)
    (wellDefined : ∀ initial current : LiveRecord k,
      (some initial, some current) ∈ AcquiredPairs k m (by omega) localAlphabet (some v)
        (archive ++ [(parent, some (previous + 1))]) → f (some initial) = labels (-initial.phase)) :
    let acquired := archive ++ [(parent, some (previous + 1))]
    (∀ i : Fin m, parent i = decide (i.val % 2 = 0)) ∧
    ∀ pair ∈ AcquiredPairs k m (by omega) localAlphabet (some v) acquired,
      ∃ initial current : LiveRecord k,
        pair.1 = some initial ∧ pair.2 = some current ∧
        f pair.1 = labels (-initial.phase) ∧ -initial.phase ∈ physicalWindow k m archive.length ∧
        current.value = previous + 1 ∧ current.tail = 1 ∧
        current.phase = initial.phase + (((archive.length + 1) * m : ℕ) : ZMod (k + 1)) ∧
        ∃ history : List (AllowedBlock k m localAlphabet),
          let w := history.flatMap (fun action => List.ofFn action.val)
          OriginalRecord k (by omega) w = some initial ∧
          OriginalRecord k (by omega) (w ++ archiveWords acquired) = some current ∧
          NarrowWindowCost.output k (by omega) w = some v ∧ ActualArchive k (by omega) w acquired ∧
          ∀ (π : NarrowWindowCost.Selector m Y) (d c : ℕ),
            NarrowWindowCost.execute k (by omega) π d (w ++ archiveWords acquired) (some v) acquired =
                some (f (some initial), c) ↔
              ∃ issued, PaidTrace π (some v) (some current) acquired issued (f (some initial)) ∧
                issued.length = c ∧ c ≤ d ∧ ActualArchive k (by omega) w (acquired ++ issued) ∧
                (some initial, OriginalRecord k (by omega) (w ++ archiveWords (acquired ++ issued))) ∈
                  AcquiredPairs k m (by omega) localAlphabet (some v) (acquired ++ issued) := by
  intro acquired
  have short : m < k := by omega
  have parentFacts := full_positive_parent k m hm odd short localAlphabet v previous archive parent prior full
  have facts := actual_positive_coordinates k m (by omega) short localAlphabet v previous archive parent prior
  refine ⟨parentFacts.1, ?_⟩
  intro pair member
  obtain ⟨initial, current, initialEq, currentEq, value, tail, phase⟩ := facts.2.2 pair member
  have liveMember : (some initial, some current) ∈
      AcquiredPairs k m (by omega) localAlphabet (some v) acquired := by
    simpa only [← initialEq, ← currentEq] using member
  have support : -initial.phase ∈ physicalWindow k m archive.length := by
    rw [← full]
    exact ⟨initial, some current, liveMember, rfl⟩
  obtain ⟨history, free, matched, source, endpoint⟩ := member
  refine ⟨initial, current, initialEq, currentEq, ?_, support, value,
    parentFacts.2 initial current liveMember, phase, history, source.symm.trans initialEq,
    endpoint.symm.trans currentEq, free, matched, ?_⟩
  · rw [initialEq]
    exact wellDefined initial current liveMember
  · intro π d c
    have bridge := acquired_execution_trace k m (by omega) localAlphabet f history (some v)
      acquired free matched π d c
    dsimp only at bridge
    rw [source.symm.trans initialEq, endpoint.symm.trans currentEq] at bridge
    exact bridge

#print axioms full_positive_history_trace
#print axioms acquired_execution_trace

end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace
