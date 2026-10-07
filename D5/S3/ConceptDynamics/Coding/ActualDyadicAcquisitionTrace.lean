/- GID: D5/S3/ConceptDynamics/Coding/ActualDyadicAcquisitionTrace
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ActualDyadicAcquisitionTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual dyadic continuations force midpoint traces and pair-local final queries. -/

import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.ActualDyadicCausalPrefixRepairCapacity

/-- The complete available event and read record. -/
structure Record where
  events : Nat
  reads : List (Nat × Fin 2)
  deriving DecidableEq

/-- The only physical actions: one forward event, one nondisturbing read,
or a successful stop with an output. -/
inductive Action (P : Nat) where
  | advance
  | read
  | stop (output : Fin P)

/-- Literal standard-representative sensor after the counted forward events. -/
def rawSensor {P : Nat} (positive : 0 < P) (b : Fin 2) (r : Fin P)
    (events : Nat) : Fin 2 :=
  ⟨((b.val * P + r.val + events) % (2 * P)) / P,
    (Nat.div_lt_iff_lt_mul positive).2
      (Nat.mod_lt _ (by omega))⟩

/-- Finite successful executions. The word contains only the new physical reads.
There is no constructor for a fuel cutoff. A stop with no reads is allowed. -/
inductive Execution {P : Nat} (positive : 0 < P) (b : Fin 2)
    (policy : Record → Action P) (r : Fin P) :
    Record → List (Fin 2) → (Record × Fin P) → Prop where
  | stopped {record : Record} {output : Fin P}
      (choice : policy record = .stop output) :
      Execution positive b policy r record [] (record, output)
  | advanced {record : Record} {word : List (Fin 2)} {terminal : Record × Fin P}
      (choice : policy record = .advance)
      (rest : Execution positive b policy r
        { record with events := record.events + 1 } word terminal) :
      Execution positive b policy r record word terminal
  | queried {record : Record} {word : List (Fin 2)} {terminal : Record × Fin P}
      (choice : policy record = .read)
      (rest : Execution positive b policy r
        { record with reads := record.reads ++
          [(record.events, rawSensor positive b r record.events)] } word terminal) :
      Execution positive b policy r record
        (rawSensor positive b r record.events :: word) terminal

/-- Zero padding is a mathematical word encoding, never a physical read. -/
def rawCode : List (Fin 2) → Nat → Fin 2
  | [], _ => 0
  | bit :: _, 0 => bit
  | _ :: tail, index + 1 => rawCode tail index

/-- From one common complete record, every source in a finite candidate set has
an actual successful continuation identifying that source with at most `remaining`
new reads. That set has at most `2^remaining` sources. Silent advances and early
stopping are included in the two-run replay used to establish the injection. -/
theorem actual_continuation_capacity_and_saturation
    {P : Nat} (positive : 0 < P) (b : Fin 2) (policy : Record → Action P)
    (record : Record) (remaining : Nat) (candidates : Finset (Fin P))
    (success : ∀ r ∈ candidates, ∃ word terminal,
      Execution positive b policy r record word terminal ∧
      word.length ≤ remaining ∧ terminal.2 = r) :
    candidates.card ≤ 2 ^ remaining ∧
    (candidates.card = 2 ^ remaining →
      ∀ r ∈ candidates, ∀ word terminal,
        Execution positive b policy r record word terminal →
        word.length ≤ remaining → word.length = remaining) := by
  classical
  have replay : ∀ (r : Fin P) (start : Record) (word : List (Fin 2))
      (terminal : Record × Fin P),
      Execution positive b policy r start word terminal →
      ∀ (r' : Fin P) (word' : List (Fin 2)) (terminal' : Record × Fin P)
        , Execution positive b policy r' start word' terminal' →
        (∀ k < word.length, rawCode word k = rawCode word' k) →
        word = word' ∧ terminal = terminal' := by
    intro r start word terminal execution
    induction execution with
    | @stopped start output choice =>
        intro r' word' terminal' other equalCode
        cases other with
        | stopped otherChoice =>
            have outputs := choice.symm.trans otherChoice
            cases outputs
            exact ⟨rfl, rfl⟩
        | advanced otherChoice rest =>
            have impossible := choice.symm.trans otherChoice
            cases impossible
        | queried otherChoice rest =>
            have impossible := choice.symm.trans otherChoice
            cases impossible
    | @advanced start word terminal choice rest ih =>
        intro r' word' terminal' other equalCode
        cases other with
        | stopped otherChoice =>
            have impossible := choice.symm.trans otherChoice
            cases impossible
        | advanced otherChoice otherRest =>
            exact ih r' word' terminal' otherRest equalCode
        | queried otherChoice otherRest =>
            have impossible := choice.symm.trans otherChoice
            cases impossible
    | @queried start word terminal choice rest ih =>
        intro r' word' terminal' other equalCode
        cases other with
        | stopped otherChoice =>
            have impossible := choice.symm.trans otherChoice
            cases impossible
        | advanced otherChoice otherRest =>
            have impossible := choice.symm.trans otherChoice
            cases impossible
        | queried otherChoice otherRest =>
            have sameBit : rawSensor positive b r start.events =
                rawSensor positive b r' start.events := by
              simpa [rawCode] using equalCode 0 (by simp)
            have sameRecord :
                ({ start with reads := start.reads ++
                  [(start.events, rawSensor positive b r start.events)] } : Record) =
                { start with reads := start.reads ++
                  [(start.events, rawSensor positive b r' start.events)] } := by
              rw [sameBit]
            rw [← sameRecord] at otherRest
            have equalTail := ih r' _ terminal' otherRest (by
              intro k hk
              simpa [rawCode] using equalCode (k + 1) (by simp; omega))
            exact ⟨by rw [equalTail.1, sameBit], equalTail.2⟩
  let witness (r : candidates) := success r.val r.property
  let word (r : candidates) : List (Fin 2) := (witness r).choose
  let terminal (r : candidates) : Record × Fin P := (witness r).choose_spec.choose
  have runs (r : candidates) :
      Execution positive b policy r.val record (word r) (terminal r) ∧
      (word r).length ≤ remaining ∧ (terminal r).2 = r.val :=
    (witness r).choose_spec.choose_spec
  let encode : candidates → (Fin remaining → Fin 2) :=
    fun r k => rawCode (word r) k.val
  have injective : Function.Injective encode := by
    intro r r' sameCode
    have sameTerminal := replay r.val record (word r) (terminal r) (runs r).1
      r'.val (word r') (terminal r') (runs r').1
      (fun k hk => congrFun sameCode ⟨k, hk.trans_le (runs r).2.1⟩)
    apply Subtype.ext
    calc
      r.val = (terminal r).2 := (runs r).2.2.symm
      _ = (terminal r').2 := congrArg Prod.snd sameTerminal.2
      _ = r'.val := (runs r').2.2
  have count := Fintype.card_le_of_injective encode injective
  refine ⟨by simpa using count, ?_⟩
  intro saturated r member actualWord actualTerminal execution bounded
  have sameCard : Fintype.card candidates = Fintype.card (Fin remaining → Fin 2) := by
    simpa using saturated
  have onto : Function.Surjective encode :=
    ((Fintype.bijective_iff_injective_and_card encode).2 ⟨injective, sameCard⟩).2
  have padding : ∀ w : List (Fin 2), rawCode w w.length = 0 := by
    intro w
    induction w with
    | nil => rfl
    | cons bit tail ih => simpa [rawCode] using ih
  apply Nat.le_antisymm bounded
  by_contra notFull
  have short : actualWord.length < remaining := by omega
  let changed : Fin remaining → Fin 2 := fun k =>
    if k.val < actualWord.length then rawCode actualWord k.val else 1
  obtain ⟨r', encoded⟩ := onto changed
  have equalPrefix : ∀ k < actualWord.length,
      rawCode actualWord k = rawCode (word r') k := by
    intro k hk
    have atIndex := congrFun encoded ⟨k, hk.trans short⟩
    simpa [encode, changed, hk] using atIndex.symm
  have sameRun := replay r record actualWord actualTerminal execution
    r'.val (word r') (terminal r') (runs r').1 equalPrefix
  have atEnd := congrFun encoded ⟨actualWord.length, short⟩
  change rawCode (word r') actualWord.length = changed ⟨actualWord.length, short⟩ at atEnd
  rw [← sameRun.1, padding] at atEnd
  simp [changed] at atEnd


/-- A nonempty actual successful run reaches one common next-read event after
finite silent forward evolution. Every other nonempty actual successful run
from that complete record reaches the same event before acquiring its first bit. -/
theorem actual_next_read_decomposition
    {P : Nat} (positive : 0 < P) (b : Fin 2) (policy : Record → Action P)
    (record : Record) (r : Fin P) (word : List (Fin 2)) (terminal : Record × Fin P)
    (execution : Execution positive b policy r record word terminal)
    (nonempty : word ≠ []) :
    ∃ N, record.events ≤ N ∧ policy ⟨N, record.reads⟩ = .read ∧
      (∀ k, record.events ≤ k → k < N → policy ⟨k, record.reads⟩ = .advance) ∧
      ∀ (r' : Fin P) (word' : List (Fin 2)) (terminal' : Record × Fin P),
        Execution positive b policy r' record word' terminal' → word' ≠ [] →
        ∃ tail, word' = rawSensor positive b r' N :: tail ∧
          Execution positive b policy r'
            ⟨N, record.reads ++ [(N, rawSensor positive b r' N)]⟩ tail terminal' := by
  have first : ∀ (source : Fin P) (start : Record) (bits : List (Fin 2))
      (finish : Record × Fin P),
      Execution positive b policy source start bits finish → bits ≠ [] →
      ∃ N, start.events ≤ N ∧ policy ⟨N, start.reads⟩ = .read ∧
        (∀ k, start.events ≤ k → k < N → policy ⟨k, start.reads⟩ = .advance) ∧
        ∃ tail, bits = rawSensor positive b source N :: tail ∧
          Execution positive b policy source
            ⟨N, start.reads ++ [(N, rawSensor positive b source N)]⟩ tail finish := by
    intro source start bits finish run
    induction run with
    | @stopped start output choice =>
        intro nonempty
        exact False.elim (nonempty rfl)
    | @advanced start bits finish choice rest ih =>
        intro nonempty
        obtain ⟨N, lower, readChoice, advances, tail, wordEq, tailRun⟩ := ih nonempty
        refine ⟨N, by simp at lower; omega, readChoice, ?_, tail, wordEq, tailRun⟩
        intro k lowerK upperK
        by_cases atStart : k = start.events
        · subst k
          exact choice
        · exact advances k (by simp; omega) upperK
    | @queried start tail finish choice rest ih =>
        intro _
        refine ⟨start.events, Nat.le_refl _, choice, ?_, tail, rfl, rest⟩
        intro k lower upper
        omega
  obtain ⟨N, lower, readChoice, advances, tail, wordEq, tailRun⟩ :=
    first r record word terminal execution nonempty
  refine ⟨N, lower, readChoice, advances, ?_⟩
  intro r' word' terminal' other otherNonempty
  obtain ⟨N', lower', readChoice', advances', tail', wordEq', tailRun'⟩ :=
    first r' record word' terminal' other otherNonempty
  have notEarlier : ¬N < N' := by
    intro earlier
    have impossible := readChoice.symm.trans (advances' N lower earlier)
    cases impossible
  have notLater : ¬N' < N := by
    intro later
    have impossible := readChoice'.symm.trans (advances N' lower' later)
    cases impossible
  have sameEvent : N' = N := by omega
  subst N'
  exact ⟨tail', wordEq', tailRun'⟩


/-- A conclusion about the chronological actual read trace. At each read the
phase must be the midpoint of the current source interval. The raw bit retains
the known initial bit and the complete actual event quotient. -/
def ForcedReadTrace {P : Nat} (b : Fin 2) (r : Fin P) :
    Nat → Nat → List (Nat × Fin 2) → Prop
  | _, 0, trace => trace = []
  | lo, d + 1, trace =>
      ∃ N bit tail, trace = (N, bit) :: tail ∧
        N % P = P - (lo + 2 ^ d) ∧
        bit.val = (b.val + N / P +
          if r.val < lo + 2 ^ d then 0 else 1) % 2 ∧
        ForcedReadTrace b r
          (lo + (if r.val < lo + 2 ^ d then 0 else 1) * 2 ^ d) d tail

/-- Saturated actual continuations from a dyadic source interval force its
entire chronological midpoint trace. The interval and successful continuations
are the local induction input; neither read times nor raw bits are policy fields.
The terminal record may include silent reporting advances, but the trace contains
only literal query event counts, so its last event is the actual final query. -/
theorem actual_dyadic_interval_trace
    {P : Nat} (positive : 0 < P) (b : Fin 2) (policy : Record → Action P)
    (record : Record) (lo d : Nat) (within : lo + 2 ^ d ≤ P)
    (success : ∀ r : Fin P, lo ≤ r.val → r.val < lo + 2 ^ d →
      ∃ word terminal, Execution positive b policy r record word terminal ∧
        word.length ≤ d ∧ terminal.2 = r)
    (r : Fin P) (lower : lo ≤ r.val) (upper : r.val < lo + 2 ^ d)
    (word : List (Fin 2)) (terminal : Record × Fin P)
    (execution : Execution positive b policy r record word terminal)
    (bounded : word.length ≤ d) :
    ∃ trace, terminal.1.reads = record.reads ++ trace ∧
      ForcedReadTrace b r lo d trace := by
  classical
  let interval (a h : Nat) : Finset (Fin P) :=
    Finset.univ.filter (fun s => a ≤ s.val ∧ s.val < h)
  have cardInterval (a h : Nat) (hP : h ≤ P) :
      (interval a h).card = h - a := by
    have image : (interval a h).image Fin.val = Finset.Ico a h := by
      ext n
      simp only [interval, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and, Finset.mem_Ico]
      constructor
      · rintro ⟨s, hs, rfl⟩
        exact hs
      · intro hn
        exact ⟨⟨n, hn.2.trans_le hP⟩, hn, rfl⟩
    rw [← Finset.card_image_of_injective (interval a h) Fin.val_injective,
      image, Nat.card_Ico]
  have sensor (s : Fin P) (N : Nat) :
      (rawSensor positive b s N).val =
        (b.val + N / P + if s.val < P - N % P then 0 else 1) % 2 := by
    change ((b.val * P + s.val + N) % (2 * P)) / P = _
    rw [Nat.mod_mul_left_div_self]
    have hN := Nat.mod_add_div N P
    have hm := Nat.mod_lt N positive
    have hs := s.isLt
    have rearrange : b.val * P + s.val + N =
        (s.val + N % P) + P * (b.val + N / P) := by nlinarith
    rw [rearrange, Nat.add_mul_div_left _ _ positive]
    by_cases h : s.val < P - N % P
    · rw [if_pos h, Nat.div_eq_of_lt (by omega)]
      congr 1
      omega
    · have q : (s.val + N % P) / P = 1 :=
        Nat.div_eq_of_lt_le (by omega) (by omega)
      rw [if_neg h, q]
      congr 1
      omega
  have noReads : ∀ (s : Fin P) (start : Record) (finish : Record × Fin P),
      Execution positive b policy s start [] finish →
      finish.1.reads = start.reads := by
    intro s start finish run
    generalize hword : ([] : List (Fin 2)) = bits at run
    induction run with
    | stopped choice => rfl
    | advanced choice rest ih => exact ih hword
    | queried choice rest ih => cases hword
  induction d generalizing record lo r word terminal with
  | zero =>
      have empty : word = [] := List.eq_nil_of_length_eq_zero (by simpa using bounded)
      subst word
      exact ⟨[], by simpa using noReads r record terminal execution, rfl⟩
  | succ d ih =>
      have hpow : 0 < 2 ^ d := by positivity
      have cardParent : (interval lo (lo + 2 ^ (d + 1))).card = 2 ^ (d + 1) := by
        rw [cardInterval _ _ within, Nat.add_sub_cancel_left]
      have successParent : ∀ s ∈ interval lo (lo + 2 ^ (d + 1)),
          ∃ bits finish, Execution positive b policy s record bits finish ∧
            bits.length ≤ d + 1 ∧ finish.2 = s := by
        intro s hs
        simp only [interval, Finset.mem_filter, Finset.mem_univ, true_and] at hs
        exact success s hs.1 hs.2
      have capacity := actual_continuation_capacity_and_saturation positive b policy
        record (d + 1) (interval lo (lo + 2 ^ (d + 1))) successParent
      have full := capacity.2 cardParent r
        (by simp [interval, lower, upper]) word terminal execution bounded
      have nonempty : word ≠ [] := by intro h; simp [h] at full
      obtain ⟨N, after, readChoice, advances, decompose⟩ :=
        actual_next_read_decomposition positive b policy record r word terminal execution nonempty
      let theta := P - N % P
      let leftBit : Fin 2 := ⟨(b.val + N / P) % 2, Nat.mod_lt _ (by decide)⟩
      let rightBit : Fin 2 := ⟨(b.val + N / P + 1) % 2, Nat.mod_lt _ (by decide)⟩
      let leftRecord : Record := ⟨N, record.reads ++ [(N, leftBit)]⟩
      let rightRecord : Record := ⟨N, record.reads ++ [(N, rightBit)]⟩
      have childSuccess (a h : Nat) (bit : Fin 2)
          (childSubset : ∀ s ∈ interval a h,
            lo ≤ s.val ∧ s.val < lo + 2 ^ (d + 1))
          (childBit : ∀ s ∈ interval a h, rawSensor positive b s N = bit) :
          ∀ s ∈ interval a h, ∃ bits finish,
            Execution positive b policy s ⟨N, record.reads ++ [(N, bit)]⟩ bits finish ∧
              bits.length ≤ d ∧ finish.2 = s := by
        intro s hs
        obtain ⟨bits, finish, run, bound, output⟩ :=
          success s (childSubset s hs).1 (childSubset s hs).2
        have length := capacity.2 cardParent s
          (by simp [interval, (childSubset s hs).1, (childSubset s hs).2])
          bits finish run bound
        have nonempty' : bits ≠ [] := by intro h; simp [h] at length
        obtain ⟨tail, eqBits, rest⟩ := decompose s bits finish run nonempty'
        rw [childBit s hs] at rest
        refine ⟨tail, finish, rest, ?_, output⟩
        rw [eqBits] at bound
        simpa using bound
      have successLeft := childSuccess lo (min theta (lo + 2 ^ (d + 1))) leftBit
        (by intro s hs; simp only [interval, Finset.mem_filter, Finset.mem_univ,
            true_and, lt_min_iff] at hs; exact ⟨hs.1, hs.2.2⟩)
        (by intro s hs; apply Fin.ext
            simp only [interval, Finset.mem_filter, Finset.mem_univ,
              true_and, lt_min_iff] at hs
            simp [sensor, theta, leftBit, hs.2.1])
      have successRight := childSuccess (max lo theta) (lo + 2 ^ (d + 1)) rightBit
        (by intro s hs; simp only [interval, Finset.mem_filter, Finset.mem_univ,
            true_and, max_le_iff] at hs; exact ⟨hs.1.1, hs.2⟩)
        (by intro s hs; apply Fin.ext
            simp only [interval, Finset.mem_filter, Finset.mem_univ,
              true_and, max_le_iff] at hs
            have notBelow : ¬s.val < theta := by omega
            simp [sensor, theta, rightBit, notBelow])
      have leftBound := (actual_continuation_capacity_and_saturation positive b policy
        leftRecord d (interval lo (min theta (lo + 2 ^ (d + 1)))) successLeft).1
      have rightBound := (actual_continuation_capacity_and_saturation positive b policy
        rightRecord d (interval (max lo theta) (lo + 2 ^ (d + 1))) successRight).1
      rw [cardInterval _ _ (by omega)] at leftBound
      rw [cardInterval _ _ within] at rightBound
      have powStep : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by simp [pow_succ]; omega
      have midpoint : theta = lo + 2 ^ d := by
        rw [powStep] at leftBound rightBound
        omega
      have phase : N % P = P - (lo + 2 ^ d) := by
        have hmod := Nat.mod_lt N positive
        dsimp [theta] at midpoint
        omega
      obtain ⟨tail, wordEq, tailRun⟩ := decompose r word terminal execution nonempty
      have tailBound : tail.length ≤ d := by rw [wordEq] at bounded; simpa using bounded
      by_cases low : r.val < lo + 2 ^ d
      · have sameBit : rawSensor positive b r N = leftBit := by
          apply Fin.ext
          rw [sensor, show P - N % P = lo + 2 ^ d from midpoint]
          simp [leftBit, low]
        have subSuccess : ∀ s : Fin P, lo ≤ s.val → s.val < lo + 2 ^ d →
            ∃ bits finish, Execution positive b policy s leftRecord bits finish ∧
              bits.length ≤ d ∧ finish.2 = s := by
          intro s hs hu
          apply successLeft s
          simp [interval, midpoint, powStep, hs, hu]
        rw [sameBit] at tailRun
        obtain ⟨trace, traceEq, forced⟩ := ih leftRecord lo (by omega)
          subSuccess r lower low tail terminal tailRun tailBound
        refine ⟨(N, leftBit) :: trace, ?_, N, leftBit, trace, rfl, phase, ?_, ?_⟩
        · simpa [leftRecord, List.append_assoc] using traceEq
        · simp [leftBit, low]
        · simpa [low] using forced
      · have high : lo + 2 ^ d ≤ r.val := by omega
        have sameBit : rawSensor positive b r N = rightBit := by
          apply Fin.ext
          rw [sensor, show P - N % P = lo + 2 ^ d from midpoint]
          simp [rightBit, low]
        have subSuccess : ∀ s : Fin P, lo + 2 ^ d ≤ s.val →
            s.val < (lo + 2 ^ d) + 2 ^ d →
            ∃ bits finish, Execution positive b policy s rightRecord bits finish ∧
              bits.length ≤ d ∧ finish.2 = s := by
          intro s hs hu
          apply successRight s
          simp only [interval, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [midpoint, powStep]
          omega
        rw [sameBit] at tailRun
        obtain ⟨trace, traceEq, forced⟩ := ih rightRecord (lo + 2 ^ d) (by omega)
          subSuccess r high (by omega) tail terminal tailRun tailBound
        refine ⟨(N, rightBit) :: trace, ?_, N, rightBit, trace, rfl, phase, ?_, ?_⟩
        · simpa [rightRecord, List.append_assoc] using traceEq
        · simp [rightBit, low]
        · simpa [low] using forced


/-- Actual executions of a source pair have one common pre-final raw-read
history and one common literal last-query event. Forced midpoint traces are
supplied by `actual_dyadic_interval_trace`, rather than assumed by a policy. -/
theorem actual_pair_common_final_query
    {P : Nat} (positive : 0 < P) (b : Fin 2) (policy : Record → Action P)
    (record : Record) (lo d : Nat) (evenLo : Even lo)
    (within : lo + 2 ^ (d + 1) ≤ P)
    (r s : Fin P) (samePair : r.val / 2 = s.val / 2)
    (lower : lo ≤ r.val) (upper : r.val < lo + 2 ^ (d + 1))
    (lower' : lo ≤ s.val) (upper' : s.val < lo + 2 ^ (d + 1))
    (word word' : List (Fin 2)) (terminal terminal' : Record × Fin P)
    (execution : Execution positive b policy r record word terminal)
    (execution' : Execution positive b policy s record word' terminal')
    (length : word.length = d + 1) (length' : word'.length = d + 1)
    (trace trace' : List (Nat × Fin 2))
    (reads : terminal.1.reads = record.reads ++ trace)
    (reads' : terminal'.1.reads = record.reads ++ trace')
    (forced : ForcedReadTrace b r lo (d + 1) trace)
    (forced' : ForcedReadTrace b s lo (d + 1) trace') :
    ∃ past N bit bit', trace = past ++ [(N, bit)] ∧
      trace' = past ++ [(N, bit')] ∧
      N % P = P - 1 - 2 * (r.val / 2) ∧
      bit.val = (b.val + N / P + r.val % 2) % 2 ∧
      bit'.val = (b.val + N / P + s.val % 2) % 2 ∧
      policy ⟨N, record.reads ++ past⟩ = .read ∧
      Execution positive b policy r ⟨N, (record.reads ++ past) ++ [(N, bit)]⟩ [] terminal ∧
      Execution positive b policy s ⟨N, (record.reads ++ past) ++ [(N, bit')]⟩ [] terminal' := by
  have readExtension : ∀ (source : Fin P) (start : Record) (bits : List (Fin 2))
      (finish : Record × Fin P),
      Execution positive b policy source start bits finish →
      ∃ extra, finish.1.reads = start.reads ++ extra := by
    intro source start bits finish run
    induction run with
    | stopped choice => exact ⟨[], by simp⟩
    | advanced choice rest ih => exact ih
    | @queried start bits finish choice rest ih =>
        obtain ⟨extra, eqReads⟩ := ih
        exact ⟨(start.events, rawSensor positive b source start.events) :: extra,
          by simpa [List.append_assoc] using eqReads⟩
  have unpack (source : Fin P) (a k N : Nat) (bit : Fin 2)
      (tail : List (Nat × Fin 2))
      (h : ForcedReadTrace b source a (k + 1) ((N, bit) :: tail)) :
      N % P = P - (a + 2 ^ k) ∧
      bit.val = (b.val + N / P + if source.val < a + 2 ^ k then 0 else 1) % 2 ∧
      ForcedReadTrace b source
        (a + (if source.val < a + 2 ^ k then 0 else 1) * 2 ^ k) k tail := by
    rcases h with ⟨M, bit', tail', shape, phase, value, rest⟩
    simp only [List.cons.injEq, Prod.mk.injEq] at shape
    rcases shape with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨phase, value, rest⟩
  induction d generalizing record lo word word' terminal terminal' trace trace' with
  | zero =>
      have nonempty : word ≠ [] := by intro h; simp [h] at length
      have nonempty' : word' ≠ [] := by intro h; simp [h] at length'
      obtain ⟨N, after, choice, advances, decompose⟩ :=
        actual_next_read_decomposition positive b policy record r word terminal execution nonempty
      obtain ⟨tail, shape, rest⟩ := decompose r word terminal execution nonempty
      obtain ⟨tail', shape', rest'⟩ := decompose s word' terminal' execution' nonempty'
      obtain ⟨extra, eqReads⟩ := readExtension r _ tail terminal rest
      obtain ⟨extra', eqReads'⟩ := readExtension s _ tail' terminal' rest'
      have eqTrace : trace = (N, rawSensor positive b r N) :: extra := by
        apply (List.append_right_inj record.reads).mp
        simpa [List.append_assoc] using reads.symm.trans eqReads
      have eqTrace' : trace' = (N, rawSensor positive b s N) :: extra' := by
        apply (List.append_right_inj record.reads).mp
        simpa [List.append_assoc] using reads'.symm.trans eqReads'
      rw [eqTrace] at forced
      rw [eqTrace'] at forced'
      have info := unpack r lo 0 N _ extra forced
      have info' := unpack s lo 0 N _ extra' forced'
      have empty := info.2.2
      have empty' := info'.2.2
      change extra = [] at empty
      change extra' = [] at empty'
      refine ⟨[], N, rawSensor positive b r N, rawSensor positive b s N,
        by simpa [empty] using eqTrace, by simpa [empty'] using eqTrace', ?_, ?_, ?_,
        by simpa using choice, ?_, ?_⟩
      · obtain ⟨a, ha⟩ := evenLo
        have hr := r.isLt
        simp only [pow_zero] at info
        change r.val < lo + 2 at upper
        change lo + 2 ≤ P at within
        omega
      · have bitEq : (if r.val < lo + 1 then 0 else 1) = r.val % 2 := by
          obtain ⟨a, ha⟩ := evenLo
          change r.val < lo + 2 at upper
          split <;> omega
        simpa only [pow_zero, bitEq] using info.2.1
      · have bitEq : (if s.val < lo + 1 then 0 else 1) = s.val % 2 := by
          obtain ⟨a, ha⟩ := evenLo
          change s.val < lo + 2 at upper'
          split <;> omega
        simpa only [pow_zero, bitEq] using info'.2.1
      · have tailNil : tail = [] := by
          apply List.eq_nil_of_length_eq_zero
          rw [shape] at length
          simpa using length
        simpa [tailNil] using rest
      · have tailNil : tail' = [] := by
          apply List.eq_nil_of_length_eq_zero
          rw [shape'] at length'
          simpa using length'
        simpa [tailNil] using rest'
  | succ d ih =>
      have nonempty : word ≠ [] := by intro h; simp [h] at length
      have nonempty' : word' ≠ [] := by intro h; simp [h] at length'
      obtain ⟨N, after, choice, advances, decompose⟩ :=
        actual_next_read_decomposition positive b policy record r word terminal execution nonempty
      obtain ⟨tail, shape, rest⟩ := decompose r word terminal execution nonempty
      obtain ⟨tail', shape', rest'⟩ := decompose s word' terminal' execution' nonempty'
      obtain ⟨extra, eqReads⟩ := readExtension r _ tail terminal rest
      obtain ⟨extra', eqReads'⟩ := readExtension s _ tail' terminal' rest'
      have eqTrace : trace = (N, rawSensor positive b r N) :: extra := by
        apply (List.append_right_inj record.reads).mp
        simpa [List.append_assoc] using reads.symm.trans eqReads
      have eqTrace' : trace' = (N, rawSensor positive b s N) :: extra' := by
        apply (List.append_right_inj record.reads).mp
        simpa [List.append_assoc] using reads'.symm.trans eqReads'
      rw [eqTrace] at forced
      rw [eqTrace'] at forced'
      have info := unpack r lo (d + 1) N _ extra forced
      have info' := unpack s lo (d + 1) N _ extra' forced'
      obtain ⟨a, ha⟩ := evenLo
      have midpointEven : ∃ a, lo + 2 ^ (d + 1) = 2 * a := by
        refine ⟨a + 2 ^ d, ?_⟩
        rw [ha, pow_succ]
        ring
      have sameSide : (r.val < lo + 2 ^ (d + 1)) ↔
          (s.val < lo + 2 ^ (d + 1)) := by
        obtain ⟨a, ha⟩ := midpointEven
        rw [ha]
        omega
      have sameBit : rawSensor positive b r N = rawSensor positive b s N := by
        apply Fin.ext
        rw [info.2.1, info'.2.1]
        simp only [sameSide]
      have childEven : Even
          (lo + (if r.val < lo + 2 ^ (d + 1) then 0 else 1) * 2 ^ (d + 1)) := by
        by_cases h : r.val < lo + 2 ^ (d + 1)
        · simpa [h] using (show Even lo from ⟨a, ha⟩)
        · simpa [h] using (show Even (lo + 2 ^ (d + 1)) from
            by obtain ⟨a, ha⟩ := midpointEven; exact ⟨a, by omega⟩)
      rw [← sameBit] at rest' eqReads'
      simp only [← sameSide] at info'
      have powStep : 2 ^ (d + 1 + 1) = 2 ^ (d + 1) + 2 ^ (d + 1) := by
        simp [pow_succ]; omega
      have childBounds :
          lo + (if r.val < lo + 2 ^ (d + 1) then 0 else 1) * 2 ^ (d + 1) ≤ r.val ∧
          r.val < lo + (if r.val < lo + 2 ^ (d + 1) then 0 else 1) * 2 ^ (d + 1) + 2 ^ (d + 1) ∧
          lo + (if r.val < lo + 2 ^ (d + 1) then 0 else 1) * 2 ^ (d + 1) ≤ s.val ∧
          s.val < lo + (if r.val < lo + 2 ^ (d + 1) then 0 else 1) * 2 ^ (d + 1) + 2 ^ (d + 1) ∧
          lo + (if r.val < lo + 2 ^ (d + 1) then 0 else 1) * 2 ^ (d + 1) + 2 ^ (d + 1) ≤ P := by
        rw [powStep] at upper upper' within
        by_cases h : r.val < lo + 2 ^ (d + 1)
        · have hs := sameSide.mp h
          simp only [if_pos h, zero_mul, add_zero]
          omega
        · have hs : ¬s.val < lo + 2 ^ (d + 1) := by simpa [← sameSide] using h
          simp only [if_neg h, one_mul]
          omega
      obtain ⟨past, M, bit, bit', sameTrace, sameTrace', phase, value, value', lastChoice, lastRun, lastRun'⟩ := ih
        ⟨N, record.reads ++ [(N, rawSensor positive b r N)]⟩
        (lo + (if r.val < lo + 2 ^ (d + 1) then 0 else 1) * 2 ^ (d + 1))
        childEven childBounds.2.2.2.2 childBounds.1 childBounds.2.1
        childBounds.2.2.1 childBounds.2.2.2.1 tail tail' terminal terminal' rest rest'
        (by rw [shape] at length; simpa using length)
        (by rw [shape'] at length'; simpa using length')
        extra extra' eqReads eqReads' info.2.2 info'.2.2
      refine ⟨(N, rawSensor positive b r N) :: past, M, bit, bit', ?_, ?_, phase, value, value', ?_, ?_, ?_⟩
      · rw [eqTrace, sameTrace]
        rfl
      · rw [eqTrace', ← sameBit, sameTrace']
        rfl
      · simpa [List.append_assoc] using lastChoice
      · simpa [List.append_assoc] using lastRun
      · simpa [List.append_assoc] using lastRun'

end D5.S3.ConceptDynamics.Coding.ActualDyadicCausalPrefixRepairCapacity
