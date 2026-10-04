/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/EndpointCells
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/EndpointCells
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Retained initial targets, actual endpoint cells, and deterministic complete-block controllers. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.LiteralModel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.EndpointCells

open D5.S0.Tower.DBonacci.Names
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open scoped BigOperators
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.LiteralModel

/- This model uses the original KBonacci recurrence, its fixed mod-two scalar,
legal-run language and endpoint alphabet. Its all-order results do not provide
a theorem for an arbitrary recurrence, scalar readout or controlled machine. -/

/-- A candidate retains both its initial source and its changing current record.
Actual reply fibers are nonempty cells of this type. -/
def CandidateState (k : ℕ) (X : Type*) :=
  {records : Set (X × Option (LiveRecord k)) // records.Nonempty}

/-- Local legality restricts the block itself, never the old source tail. -/
def AllowedBlock (k m : ℕ) (localAlphabet : Bool) :=
  {word : Fin m → Bool // localAlphabet = true → DBonacciAdmissible k m word}

/-- The sources and updated records remaining after one actual endpoint reply. -/
def replyFiber (k m : ℕ) {X : Type*} (cell : CandidateState k X) (word : Fin m → Bool)
    (reply : Option (ZMod 2)) : Set (X × Option (LiveRecord k)) :=
  {pair | ∃ current, (pair.1, current) ∈ cell.val ∧
    runBits k word current = pair.2 ∧ endpointReading pair.2 = reply}

/-- The native finite-horizon control system branches only on nonempty actual
endpoint fibers and keeps the initial target coordinate through every action. -/
def acquisitionSystem (k m : ℕ) (localAlphabet : Bool) (X : Type*) :
    D5.S3.ConceptDynamics.Control.FiniteHorizonReachability.ControlSystem
      (CandidateState k X) where
  Action _ := AllowedBlock k m localAlphabet
  successor := fun {cell} action =>
    {next | ∃ reply, next.val = replyFiber k m cell action.val reply}
  successor_nonempty := by
    intro cell action
    obtain ⟨⟨initial, current⟩, member⟩ := cell.property
    let nextCurrent := runBits k action.val current
    let reply := endpointReading nextCurrent
    have nonempty : (replyFiber k m cell action.val reply).Nonempty :=
      ⟨(initial, nextCurrent), current, member, rfl, rfl⟩
    exact ⟨⟨replyFiber k m cell action.val reply, nonempty⟩, reply, rfl⟩

/-- A stopping cell permits one label precisely when all retained initial
sources have the same target; current record constancy is not the goal. -/
def targetGoal {k : ℕ} {X Y : Type*} (f : X → Y) :
    Set (CandidateState k X) :=
  {cell | ∀ a ∈ cell.val, ∀ b ∈ cell.val, f a.1 = f b.1}

/-- Any bounded actual acquisition preserves equality of initial target labels
for candidates whose current records have already merged. This includes a
merge into rejection, without identifying its label with the initial bottom. -/
theorem acquisition_merge_obstruction (k m : ℕ) (localAlphabet : Bool)
    {X Y : Type*} (f : X → Y) (n : ℕ)
    (cell : CandidateState k X)
    (strategy : D5.S3.ConceptDynamics.Control.FiniteHorizonReachability.BoundedReachStrategy
      (acquisitionSystem k m localAlphabet X) (targetGoal f) n cell) :
    ∀ initial₁ initial₂ current,
      (initial₁, current) ∈ cell.val → (initial₂, current) ∈ cell.val →
      f initial₁ = f initial₂ := by
  induction strategy with
  | now atGoal =>
      intro initial₁ initial₂ current first second
      exact atGoal (initial₁, current) first (initial₂, current) second
  | @step n cell action continuation ih =>
      intro initial₁ initial₂ current first second
      let updated := runBits k action.val current
      let reply := endpointReading updated
      have firstNext : (initial₁, updated) ∈ replyFiber k m cell action.val reply :=
        ⟨current, first, rfl, rfl⟩
      have secondNext : (initial₂, updated) ∈ replyFiber k m cell action.val reply :=
        ⟨current, second, rfl, rfl⟩
      let next : CandidateState k X :=
        ⟨replyFiber k m cell action.val reply, ⟨(initial₁, updated), firstNext⟩⟩
      have attained : next ∈ (acquisitionSystem k m localAlphabet X).successor action :=
        ⟨reply, rfl⟩
      exact ih next attained initial₁ initial₂ updated firstNext secondNext

#print axioms acquisition_merge_obstruction

/-- The literal all-one block. -/
def allOneBlock (m : ℕ) : Fin m → Bool := fun _ => true

/-- The increment of the next all-one block after `t` previous blocks. -/
def allOneIncrement (k m t : ℕ) (phase : ZMod (k + 1)) : ZMod 2 :=
  wordIncrement k (phase + ((t * m : ℕ) : ZMod (k + 1))) (allOneBlock m)

/-- One actually executed all-one block orbit; intermediate bits are unread. -/
def allOneOrbit (k m t : ℕ) (q : Option (LiveRecord k)) : Option (LiveRecord k) :=
  (runBits k (allOneBlock m))^[t] q

/-- An archive of successful complete-block endpoint values. The supplied
`b i` is the acquired difference between endpoints `i` and `i+1`. -/
def OnesArchive (k m t : ℕ) (v : ZMod 2) (phase : ZMod (k + 1)) (s : ℕ)
    (b : ℕ → ZMod 2) : Prop :=
  ∀ r, r ≤ t →
    endpointReading (allOneOrbit k m r (some ⟨v, phase, s⟩)) =
      some (v + ∑ i ∈ Finset.range r, b i)

/-- The complete actual endpoint archive filters precisely the initial phases
and tails in the source's all-one prefix invariant. No current tail is used as
an initial target coordinate, and no unread bit supplies an observation. -/
theorem all_one_archive_exact (k m : ℕ) (hk : 2 ≤ k) (hm : 1 ≤ m)
    (t : ℕ) (v : ZMod 2) (phase : ZMod (k + 1)) (s : ℕ) (hs : s < k)
    (b : ℕ → ZMod 2) :
    (OnesArchive k m t v phase s b ↔
      s + t * m < k ∧ ∀ i, i < t → allOneIncrement k m i phase = b i) ∧
    (OnesArchive k m t v phase s b →
      allOneOrbit k m t (some ⟨v, phase, s⟩) =
        some ⟨v + ∑ i ∈ Finset.range t, b i,
          phase + ((t * m : ℕ) : ZMod (k + 1)), s + t * m⟩) ∧
    (allOneOrbit k m t (some ⟨v, phase, s⟩) =
      if s + t * m < k then
        some ⟨v + ∑ i ∈ Finset.range t, allOneIncrement k m i phase,
          phase + ((t * m : ℕ) : ZMod (k + 1)), s + t * m⟩
      else none) := by
  have scan : ∀ (maxTrue fuel n : ℕ),
      runAdmissible maxTrue fuel n (fun _ => true) = decide (n ≤ fuel) := by
    intro maxTrue fuel n
    induction n generalizing fuel with
    | zero => simp [runAdmissible]
    | succ n ih =>
        cases fuel with
        | zero => simp [runAdmissible]
        | succ fuel =>
            change runAdmissible maxTrue fuel n (fun _ => true) = decide (n + 1 ≤ fuel + 1)
            simpa only [Nat.add_le_add_iff_right] using ih fuel
  have tail : ∀ (n s : ℕ), tailAfter s (fun _ : Fin n => true) = s + n := by
    intro n
    induction n with
    | zero => intro s; rfl
    | succ n ih =>
        intro s
        change tailAfter (s + 1) (fun _ : Fin n => true) = s + (n + 1)
        rw [ih]
        omega
  have oneBlock : ∀ (value : ZMod 2) (phi : ZMod (k + 1)) (tail₀ : ℕ), tail₀ < k →
      runBits k (allOneBlock m) (some ⟨value, phi, tail₀⟩) =
        if tail₀ + m < k then
          some ⟨value + wordIncrement k phi (allOneBlock m), phi + (m : ℕ), tail₀ + m⟩
        else none := by
    intro value phi tail₀ htail
    have model := (literal_block_execution k hk m (allOneBlock m) value phi tail₀ htail).1
    have scanned : runAdmissible (k - 1) (k - 1 - tail₀) m (allOneBlock m) =
        decide (m ≤ k - 1 - tail₀) := scan (k - 1) (k - 1 - tail₀) m
    have tailed : tailAfter tail₀ (allOneBlock m) = tail₀ + m := tail m tail₀
    have safe : m ≤ k - 1 - tail₀ ↔ tail₀ + m < k := by omega
    simpa only [scanned, tailed, decide_eq_true_eq, safe] using model
  have rejected : ∀ bits : List Bool, runWord (bitUpdate k) bits none = none := by
    intro bits
    induction bits with
    | nil => rfl
    | cons bit bits ih => simpa [runWord, bitUpdate] using ih
  have execute : ∀ r,
      allOneOrbit k m r (some ⟨v, phase, s⟩) =
        if s + r * m < k then
          some ⟨v + ∑ i ∈ Finset.range r, allOneIncrement k m i phase,
            phase + ((r * m : ℕ) : ZMod (k + 1)), s + r * m⟩
        else none := by
    intro r
    induction r with
    | zero => simp [allOneOrbit, hs]
    | succ r ih =>
        rw [allOneOrbit, Function.iterate_succ_apply']
        change runBits k (allOneBlock m) (allOneOrbit k m r (some ⟨v, phase, s⟩)) = _
        rw [ih]
        by_cases previous : s + r * m < k
        · rw [if_pos previous, oneBlock _ _ _ previous]
          have arithmetic : s + r * m + m = s + (r + 1) * m := by ring
          have phaseArithmetic :
              phase + ((r * m : ℕ) : ZMod (k + 1)) + (m : ℕ) =
              phase + (((r + 1) * m : ℕ) : ZMod (k + 1)) := by push_cast; ring
          rw [arithmetic, phaseArithmetic, Finset.sum_range_succ]
          simp only [allOneIncrement, add_assoc]
        · have next : ¬ s + (r + 1) * m < k := by nlinarith
          simp [previous, next, runBits, rejected]
  have total : ∀ r,
      (∀ i, i < r → allOneIncrement k m i phase = b i) →
      (∑ i ∈ Finset.range r, allOneIncrement k m i phase) =
        ∑ i ∈ Finset.range r, b i := by
    intro r matching
    apply Finset.sum_congr rfl
    intro i hi
    exact matching i (Finset.mem_range.mp hi)
  constructor
  · constructor
    · intro archive
      have last := archive t le_rfl
      rw [execute] at last
      have safe : s + t * m < k := by
        by_contra notSafe
        simp [notSafe, endpointReading] at last
      refine ⟨safe, ?_⟩
      intro i hi
      have safeBefore : s + i * m < k := by nlinarith
      have safeAfter : s + (i + 1) * m < k := by nlinarith
      have before := archive i (by omega)
      have after := archive (i + 1) (by omega)
      rw [execute, if_pos safeBefore] at before
      rw [execute, if_pos safeAfter] at after
      simp only [endpointReading, Option.some.injEq] at before after
      rw [Finset.sum_range_succ, Finset.sum_range_succ] at after
      linear_combination after - before
    · rintro ⟨safe, matching⟩ r hr
      have safeR : s + r * m < k := by nlinarith
      rw [execute, if_pos safeR]
      simp only [endpointReading, Option.some.injEq]
      rw [total r (fun i hi => matching i (by omega))]
  · constructor
    · intro archive
      have last := archive t le_rfl
      have safe : s + t * m < k := by
        rw [execute] at last
        by_contra notSafe
        simp [notSafe, endpointReading] at last
      rw [execute, if_pos safe]
      have matching : ∀ i, i < t → allOneIncrement k m i phase = b i := by
        intro i hi
        have before := archive i (by omega)
        have after := archive (i + 1) (by omega)
        rw [execute, if_pos (by nlinarith : s + i * m < k)] at before
        rw [execute, if_pos (by nlinarith : s + (i + 1) * m < k)] at after
        simp only [endpointReading, Option.some.injEq] at before after
        rw [Finset.sum_range_succ, Finset.sum_range_succ] at after
        linear_combination after - before
      rw [total t matching]
    · exact execute t

#print axioms all_one_archive_exact

/-- For a locally legal block, the first zero has exactly the claimed
destructive effect: an old tail rejects precisely when its leading ones reach
`k`, and every survivor ends at the same record as the zero-tail source with
the same value and phase. No bit inside this execution is observed. -/
theorem first_zero_block_exact (k : ℕ) (hk : 2 ≤ k) (n a : ℕ)
    (word : Fin n → Bool) (rest : List Bool)
    (cut : List.ofFn word = List.replicate a true ++ false :: rest)
    (legal : DBonacciAdmissible k n word)
    (v : ZMod 2) (phase : ZMod (k + 1)) (s : ℕ) (hs : s < k) :
    runBits k word (some ⟨v, phase, s⟩) =
      if s + a < k then
        some ⟨v + wordIncrement k phase word, phase + (n : ℕ), tailAfter 0 word⟩
      else none := by
  have appendRun : ∀ (left right : List Bool) (q : Option (LiveRecord k)),
      runWord (bitUpdate k) (left ++ right) q =
        runWord (bitUpdate k) right (runWord (bitUpdate k) left q) := by
    intro left
    induction left with
    | nil => intro right q; rfl
    | cons bit left ih =>
        intro right q
        simpa only [List.cons_append, runWord] using ih right (bitUpdate k bit q)
  have repeats : ∀ r (q : Option (LiveRecord k)),
      runWord (bitUpdate k) (List.replicate r true) q = allOneOrbit k 1 r q := by
    intro r
    induction r with
    | zero => intro q; rfl
    | succ r ih =>
        intro q
        rw [List.replicate_succ, runWord, ih]
        simp +unfoldPartialApp only [allOneOrbit, Function.iterate_succ_apply,
          runBits, allOneBlock, List.ofFn_const, List.replicate_one, runWord, bitUpdate]
  have leadingExecution : ∀ tail₀, tail₀ < k →
      runWord (bitUpdate k) (List.replicate a true) (some ⟨v, phase, tail₀⟩) =
        if tail₀ + a < k then
          some ⟨v + ∑ i ∈ Finset.range a, allOneIncrement k 1 i phase,
            phase + (a : ℕ), tail₀ + a⟩
        else none := by
    intro tail₀ htail
    rw [repeats]
    simpa only [Nat.mul_one] using
      (all_one_archive_exact k 1 hk le_rfl a v phase tail₀ htail (fun _ => 0)).2.2
  have scanner : runAdmissible (k - 1) (k - 1) n word = true := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    simpa [hd, DBonacciAdmissible] using legal
  have baseline : runBits k word (some ⟨v, phase, 0⟩) =
      some ⟨v + wordIncrement k phase word, phase + (n : ℕ), tailAfter 0 word⟩ := by
    have model := (literal_block_execution k hk n word v phase 0 (by omega)).1
    simpa only [Nat.sub_zero, scanner, ↓reduceIte] using model
  have rejected : ∀ bits : List Bool, runWord (bitUpdate k) bits none = none := by
    intro bits
    induction bits with
    | nil => rfl
    | cons bit bits ih => simpa [runWord, bitUpdate] using ih
  by_cases safe : s + a < k
  · rw [if_pos safe]
    have leadingSafe : a < k := by omega
    have same : runBits k word (some ⟨v, phase, s⟩) =
        runBits k word (some ⟨v, phase, 0⟩) := by
      simp only [runBits, cut, appendRun, runWord]
      rw [leadingExecution s hs, if_pos safe, leadingExecution 0 (by omega),
        if_pos (by simpa only [zero_add] using leadingSafe)]
      rfl
    exact same.trans baseline
  · rw [if_neg safe]
    simp only [runBits, cut, appendRun, runWord]
    rw [leadingExecution s hs, if_neg safe]
    exact rejected rest

#print axioms first_zero_block_exact

/-- A deterministic finite controller uses one actual endpoint reply to select
its continuation. A leaf returns an initial target label in an arbitrary type. -/
inductive AcquisitionTree (k m : ℕ) (localAlphabet : Bool) (Y : Type*) : ℕ → Type _
  | stop {n : ℕ} (label : Y) : AcquisitionTree k m localAlphabet Y n
  | step {n : ℕ} (action : AllowedBlock k m localAlphabet)
      (next : Option (ZMod 2) → AcquisitionTree k m localAlphabet Y n) :
      AcquisitionTree k m localAlphabet Y (n + 1)

/-- Execution follows only the reply to the block actually issued. -/
def AcquisitionTree.result {k m : ℕ} {localAlphabet : Bool} {Y : Type*} :
    {n : ℕ} → AcquisitionTree k m localAlphabet Y n → Option (LiveRecord k) → Y
  | _, .stop label, _ => label
  | _, .step action next, current =>
      let updated := runBits k action.val current
      (next (endpointReading updated)).result updated

/-- The acquired archive contains complete blocks and their endpoint readings. -/
def AcquisitionTree.archive {k m : ℕ} {localAlphabet : Bool} {Y : Type*} :
    {n : ℕ} → AcquisitionTree k m localAlphabet Y n → Option (LiveRecord k) →
      List (AllowedBlock k m localAlphabet × Option (ZMod 2))
  | _, .stop _, _ => []
  | _, .step action next, current =>
      let updated := runBits k action.val current
      let reply := endpointReading updated
      (action, reply) :: (next reply).archive updated

/-- Native nonempty-cell strategies and deterministic single-orbit controllers
have the same retained-initial-label semantics and the same finite horizon.
Impossible reply branches can use a label from the current source cell; neither
decidable target equality nor observation of the target is required. -/
theorem native_controller_exact (k m : ℕ) (localAlphabet : Bool)
    {X Y : Type*} (f : X → Y) (n : ℕ) (cell : CandidateState k X) :
    (∃ tree : AcquisitionTree k m localAlphabet Y n,
      (∀ pair ∈ cell.val, tree.result pair.2 = f pair.1) ∧
      ∀ current, (tree.archive current).length ≤ n) ↔
    D5.S3.ConceptDynamics.Control.FiniteHorizonReachability.BoundedReachStrategy
      (acquisitionSystem k m localAlphabet X) (targetGoal f) n cell := by
  classical
  have horizon : ∀ {r} (tree : AcquisitionTree k m localAlphabet Y r) current,
      (tree.archive current).length ≤ r := by
    intro r tree
    induction tree with
    | stop label => intro current; simp [AcquisitionTree.archive]
    | @step r action next ih =>
        intro current
        simpa only [AcquisitionTree.archive, List.length_cons, Nat.add_le_add_iff_right]
          using ih (endpointReading (runBits k action.val current))
            (runBits k action.val current)
  have forward : ∀ {r} (tree : AcquisitionTree k m localAlphabet Y r)
      (state : CandidateState k X),
      (∀ pair ∈ state.val, tree.result pair.2 = f pair.1) →
      D5.S3.ConceptDynamics.Control.FiniteHorizonReachability.BoundedReachStrategy
        (acquisitionSystem k m localAlphabet X) (targetGoal f) r state := by
    intro r tree
    induction tree with
    | stop label =>
        intro state correct
        exact .now (fun a ha b hb => (correct a ha).symm.trans (correct b hb))
    | @step r action next ih =>
        intro state correct
        refine .step action ?_
        intro successor attained
        obtain ⟨reply, equal⟩ := attained
        apply ih reply successor
        intro pair member
        rw [equal] at member
        obtain ⟨current, origin, updated, observed⟩ := member
        have same := correct (pair.1, current) origin
        simpa only [AcquisitionTree.result, updated, observed] using same
  have backward : ∀ r (state : CandidateState k X),
      D5.S3.ConceptDynamics.Control.FiniteHorizonReachability.BoundedReachStrategy
        (acquisitionSystem k m localAlphabet X) (targetGoal f) r state →
      ∃ tree : AcquisitionTree k m localAlphabet Y r,
        ∀ pair ∈ state.val, tree.result pair.2 = f pair.1 := by
    intro r
    induction r with
    | zero =>
        intro state strategy
        cases strategy with
        | now atGoal =>
            obtain ⟨source, member⟩ := state.property
            exact ⟨.stop (f source.1), fun pair hp => atGoal source member pair hp⟩
    | succ r ih =>
        intro state strategy
        cases strategy with
        | now atGoal =>
            obtain ⟨source, member⟩ := state.property
            exact ⟨.stop (f source.1), fun pair hp => atGoal source member pair hp⟩
        | step action continuation =>
            obtain ⟨source, member⟩ := state.property
            have branches : ∀ reply, ∃ tree : AcquisitionTree k m localAlphabet Y r,
                ∀ pair ∈ replyFiber k m state action.val reply,
                  tree.result pair.2 = f pair.1 := by
              intro reply
              by_cases attained : (replyFiber k m state action.val reply).Nonempty
              · exact ih ⟨replyFiber k m state action.val reply, attained⟩
                  (continuation _ ⟨reply, rfl⟩)
              · exact ⟨.stop (f source.1), fun pair hp =>
                  False.elim (attained ⟨pair, hp⟩)⟩
            choose next correct using branches
            refine ⟨.step action next, ?_⟩
            intro pair hp
            exact correct (endpointReading (runBits k action.val pair.2))
              (pair.1, runBits k action.val pair.2) ⟨pair.2, hp, rfl, rfl⟩
  constructor
  · rintro ⟨tree, correct, _⟩
    exact forward tree cell correct
  · intro strategy
    obtain ⟨tree, correct⟩ := backward n cell strategy
    exact ⟨tree, correct, horizon tree⟩

#print axioms native_controller_exact

/-- The endpoint archive of a predetermined sequence of allowed complete
blocks. It contains no internal bit reading. -/
def fixedBlockArchive {k m : ℕ} {localAlphabet : Bool} :
    List (AllowedBlock k m localAlphabet) → Option (LiveRecord k) → List (Option (ZMod 2))
  | [], _ => []
  | action :: rest, current =>
      let updated := runBits k action.val current
      endpointReading updated :: fixedBlockArchive rest updated

/-- A fixed actual protocol whose acquired archive separates the original
target classes yields a deterministic bounded controller with arbitrary labels.
The construction chooses labels only in nonempty attained cells; impossible
reply branches use a label from the parent cell. -/
theorem archive_controller_synthesis (k m : ℕ) (localAlphabet : Bool)
    {X Y : Type*} (f : X → Y) (actions : List (AllowedBlock k m localAlphabet))
    (cell : CandidateState k X)
    (separates : ∀ first ∈ cell.val, ∀ second ∈ cell.val,
      fixedBlockArchive actions first.2 = fixedBlockArchive actions second.2 →
        f first.1 = f second.1) :
    ∃ tree : AcquisitionTree k m localAlphabet Y actions.length,
      (∀ pair ∈ cell.val, tree.result pair.2 = f pair.1) ∧
      ∀ current, (tree.archive current).length ≤ actions.length := by
  classical
  apply (native_controller_exact k m localAlphabet f actions.length cell).mpr
  induction actions generalizing cell with
  | nil =>
      exact .now (fun first hf second hs => separates first hf second hs rfl)
  | cons action actions ih =>
      refine .step action ?_
      intro successor attained
      obtain ⟨reply, equal⟩ := attained
      apply ih successor
      intro first hf second hs sameArchive
      rw [equal] at hf hs
      obtain ⟨oldFirst, originFirst, updatedFirst, observedFirst⟩ := hf
      obtain ⟨oldSecond, originSecond, updatedSecond, observedSecond⟩ := hs
      apply separates (first.1, oldFirst) originFirst (second.1, oldSecond) originSecond
      simp only [fixedBlockArchive, updatedFirst, updatedSecond, observedFirst,
        observedSecond, List.cons.injEq]
      exact ⟨trivial, sameArchive⟩

#print axioms archive_controller_synthesis



end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.EndpointCells
