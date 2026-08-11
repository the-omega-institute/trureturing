/- GID: D5/S1/Digit/Carry/Successor
   generality: I
   mirror-B: D5/B/S1/Digit/Carry/Successor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Zeckendorf successor carry chains terminate within the highest occupied index. -/

import D5.S1.Digit.Normalize

namespace D5.S1.Digit.Carry.Successor

open D5.S0.Conventions
open D5.S1.Digit

/-- A carry chain with its exact number of local rewrite steps exposed. -/
inductive CarrySteps : Nat -> RawDigits -> RawDigits -> Prop where
  | zero (r : RawDigits) : CarrySteps 0 r r
  | succ {k : Nat} {before middle after : RawDigits} :
      CarrySteps k before middle -> CarryStep middle after ->
        CarrySteps (k + 1) before after

/-- Exact carry chains preserve the represented natural number. -/
theorem rawValue_carrySteps {k : Nat} {before after : RawDigits}
    (chain : CarrySteps k before after) : rawValue before = rawValue after := by
  induction chain with
  | zero => rfl
  | succ chain step ih => exact ih.trans (rawValue_carryStep step)

/-- The arithmetic progression of original digits consumed by a successor carry. -/
def prefixIndex (offset j : Nat) : Nat := offset + 2 * j

def prefixSet (offset count : Nat) : Finset Nat :=
  (Finset.range count).image fun j => prefixIndex offset j

def InPrefix (offset count i : Nat) : Prop :=
  i ∈ prefixSet offset count

private instance decidableInPrefix (offset count i : Nat) :
    Decidable (InPrefix offset count i) := by
  unfold InPrefix
  infer_instance

private theorem inPrefix_iff (offset count i : Nat) :
    InPrefix offset count i <->
      Exists fun j => j < count ∧ i = prefixIndex offset j := by
  constructor
  · intro h
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp h
    exact ⟨j, Finset.mem_range.mp hj, hji.symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩

/-- Remove the first `count` digits of one parity from a raw string. -/
noncomputable def stripPrefix (r : RawDigits) (offset count : Nat) : RawDigits := by
  classical
  exact r.filter fun i => Not (InPrefix offset count i)

/-- After `count` carries, the moving digit sits immediately before the next prefix digit. -/
def carriedIndex (offset count : Nat) : Nat :=
  prefixIndex offset count - 1

/-- State of the successor chain after exactly `count` carries. -/
noncomputable def carryState (r : RawDigits) (offset count : Nat) : RawDigits :=
  stripPrefix r offset count + Finsupp.single (carriedIndex offset count) 1

private theorem prefix_gap_exists (r : RawDigits) (offset : Nat) :
    Exists fun k => r (prefixIndex offset k) = 0 := by
  classical
  let bound := r.support.sup id + 1
  refine Exists.intro bound ?_
  by_contra hne
  have hmem : prefixIndex offset bound ∈ r.support :=
    Finsupp.mem_support_iff.mpr hne
  have hle : prefixIndex offset bound <= r.support.sup id :=
    Finset.le_sup (f := id) hmem
  dsimp [bound, prefixIndex] at hle
  omega

/-- Number of consecutive low digits consumed along one parity. -/
noncomputable def gapCount (r : RawDigits) (offset : Nat) : Nat :=
  Nat.find (prefix_gap_exists r offset)

private theorem gapCount_spec (r : RawDigits) (offset : Nat) :
    r (prefixIndex offset (gapCount r offset)) = 0 :=
  Nat.find_spec (prefix_gap_exists r offset)

private theorem gapCount_prefix_ne_zero (r : RawDigits) (offset j : Nat)
    (hj : j < gapCount r offset) : r (prefixIndex offset j) ≠ 0 := by
  exact Nat.find_min (prefix_gap_exists r offset) hj

private theorem gapCount_prefix_eq_one {r : RawDigits}
    (canonical : CanonicalRaw r) (offset j : Nat)
    (hj : j < gapCount r offset) : r (prefixIndex offset j) = 1 := by
  have hne := gapCount_prefix_ne_zero r offset j hj
  have hle := canonical.1 (prefixIndex offset j)
  omega

private theorem gapCount_le_highestIndexBound (r : RawDigits) (offset : Nat) :
    gapCount r offset <= r.support.sup id + 1 := by
  apply Nat.find_min'
  let bound := r.support.sup id + 1
  change r (prefixIndex offset bound) = 0
  by_contra hne
  have hmem : prefixIndex offset bound ∈ r.support :=
    Finsupp.mem_support_iff.mpr hne
  have hle : prefixIndex offset bound <= r.support.sup id :=
    Finset.le_sup (f := id) hmem
  dsimp [bound, prefixIndex] at hle
  omega

@[simp] private theorem stripPrefix_apply (r : RawDigits)
    (offset count i : Nat) :
    stripPrefix r offset count i = if InPrefix offset count i then 0 else r i := by
  classical
  simp [stripPrefix, Finsupp.filter_apply]

private theorem inPrefix_succ_iff (offset count i : Nat) :
    InPrefix offset (count + 1) i <->
      InPrefix offset count i ∨ i = prefixIndex offset count := by
  rw [inPrefix_iff, inPrefix_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    by_cases h : j < count
    · exact Or.inl ⟨j, h, rfl⟩
    · right
      congr 1
      omega
  · rintro (h | rfl)
    · obtain ⟨j, hj, rfl⟩ := h
      exact ⟨j, by omega, rfl⟩
    · exact ⟨count, by omega, rfl⟩

private theorem stripPrefix_restore {r : RawDigits} {offset count : Nat}
    (hbit : r (prefixIndex offset count) = 1) :
    stripPrefix r offset (count + 1) +
        Finsupp.single (prefixIndex offset count) 1 =
      stripPrefix r offset count := by
  classical
  ext i
  rw [Finsupp.add_apply, stripPrefix_apply, stripPrefix_apply,
    Finsupp.single_apply]
  simp only [inPrefix_succ_iff]
  by_cases hold : InPrefix offset count i
  · have hne : i ≠ prefixIndex offset count := by
      rintro rfl
      obtain ⟨j, hj, heq⟩ := (inPrefix_iff offset count _).mp hold
      simp only [prefixIndex] at heq
      omega
    have hne' : prefixIndex offset count ≠ i := Ne.symm hne
    simp [hold, hne, hne']
  · by_cases hi : i = prefixIndex offset count
    · subst i
      simp [hold, hbit]
    · have hi' : prefixIndex offset count ≠ i := Ne.symm hi
      simp [hold, hi, hi']

private theorem canonical_stripPrefix {r : RawDigits}
    (canonical : CanonicalRaw r) (offset count : Nat) :
    CanonicalRaw (stripPrefix r offset count) := by
  constructor
  · intro i
    rw [stripPrefix_apply]
    by_cases h : InPrefix offset count i
    · simp [h]
    · simp [h, canonical.1 i]
  · intro i hi
    rw [stripPrefix_apply] at hi
    have hri : r i = 1 := by
      split at hi
      · contradiction
      · exact hi
    have hrnext := canonical.2 i hri
    rw [stripPrefix_apply, hrnext]
    split <;> rfl

private theorem canonical_add_single {r : RawDigits} {i : Nat}
    (canonical : CanonicalRaw r) (here : r i = 0)
    (previous : i = 0 ∨ r (i - 1) = 0) (next : r (i + 1) = 0) :
    CanonicalRaw (r + Finsupp.single i 1) := by
  constructor
  · intro j
    rw [Finsupp.add_apply, Finsupp.single_apply]
    by_cases hji : i = j
    · subst j
      simp [here]
    · simp [hji]
      exact canonical.1 j
  · intro j hj
    rw [Finsupp.add_apply, Finsupp.single_apply]
    by_cases hji : i = j
    · subst j
      simpa using next
    · have hrj : r j = 1 := by
        rw [Finsupp.add_apply, Finsupp.single_apply] at hj
        simpa [hji] using hj
      by_cases hadj : j + 1 = i
      · subst i
        have hzero : r j = 0 := by
          rcases previous with hzero | hzero
          · omega
          · simpa using hzero
        omega
      · have hne : i ≠ j + 1 := Ne.symm hadj
        simpa [hne] using canonical.2 j hrj

private theorem carryState_zero (r : RawDigits) :
    carryState r 0 0 = r + Finsupp.single 0 1 := by
  classical
  ext i
  simp [carryState, stripPrefix, InPrefix, prefixSet, carriedIndex, prefixIndex]

private theorem carryState_one (r : RawDigits) :
    carryState r 1 0 = r + Finsupp.single 0 1 := by
  classical
  ext i
  simp [carryState, stripPrefix, InPrefix, prefixSet, carriedIndex, prefixIndex]

private theorem carryState_step_zero {r : RawDigits}
    (canonical : CanonicalRaw r) {count : Nat}
    (hcount : count < gapCount r 0) :
    CarryStep (carryState r 0 count) (carryState r 0 (count + 1)) := by
  have hbit := gapCount_prefix_eq_one canonical 0 count hcount
  by_cases hzero : count = 0
  · subst count
    have step := CarryStep.double_zero (stripPrefix r 0 1)
    have restore := stripPrefix_restore (r := r) (offset := 0)
      (count := 0) hbit
    have strip_zero : stripPrefix r 0 0 = r := by
      ext i
      simp [stripPrefix_apply, InPrefix, prefixSet]
    have restore' : stripPrefix r 0 1 + Finsupp.single 0 1 = r := by
      simpa [prefixIndex, strip_zero] using restore
    have hbefore :
        r + Finsupp.single 0 1 =
          stripPrefix r 0 1 + Finsupp.single 0 2 := by
      calc
        r + Finsupp.single 0 1 =
            (stripPrefix r 0 1 + Finsupp.single 0 1) +
              Finsupp.single 0 1 :=
          congrArg (fun s : RawDigits => s + Finsupp.single 0 1) restore'.symm
        _ = stripPrefix r 0 1 + Finsupp.single 0 2 := by
          ext i
          by_cases hi : i = 0
          · subst i
            simp
          · simp [hi]
    rw [carryState_zero]
    rw [show carryState r 0 (0 + 1) =
        stripPrefix r 0 1 + Finsupp.single 1 1 by
      simp [carryState, carriedIndex, prefixIndex]]
    rw [hbefore]
    exact step
  · have restore := stripPrefix_restore (r := r) (offset := 0)
      (count := count) hbit
    have step := CarryStep.adjacent (stripPrefix r 0 (count + 1))
      (carriedIndex 0 count)
    have hcarried : carriedIndex 0 count + 1 = prefixIndex 0 count := by
      simp [carriedIndex, prefixIndex]
      omega
    have hnext : carriedIndex 0 count + 2 = carriedIndex 0 (count + 1) := by
      simp [carriedIndex, prefixIndex]
      omega
    have hbefore :
        stripPrefix r 0 count + Finsupp.single (carriedIndex 0 count) 1 =
          stripPrefix r 0 (count + 1) +
            Finsupp.single (carriedIndex 0 count) 1 +
            Finsupp.single (prefixIndex 0 count) 1 := by
      rw [← restore]
      ac_rfl
    rw [carryState, carryState, hbefore]
    simpa only [hcarried, hnext] using step

private theorem carryState_step_one {r : RawDigits}
    (canonical : CanonicalRaw r) {count : Nat}
    (hcount : count < gapCount r 1) :
    CarryStep (carryState r 1 count) (carryState r 1 (count + 1)) := by
  have hbit := gapCount_prefix_eq_one canonical 1 count hcount
  have restore := stripPrefix_restore (r := r) (offset := 1)
    (count := count) hbit
  have step := CarryStep.adjacent (stripPrefix r 1 (count + 1))
    (carriedIndex 1 count)
  have hcarried : carriedIndex 1 count + 1 = prefixIndex 1 count := by
    simp only [carriedIndex, prefixIndex]
    omega
  have hnext : carriedIndex 1 count + 2 = carriedIndex 1 (count + 1) := by
    simp only [carriedIndex, prefixIndex]
    omega
  have hbefore :
      stripPrefix r 1 count + Finsupp.single (carriedIndex 1 count) 1 =
        stripPrefix r 1 (count + 1) +
          Finsupp.single (carriedIndex 1 count) 1 +
          Finsupp.single (prefixIndex 1 count) 1 := by
    rw [← restore]
    ac_rfl
  rw [carryState, carryState, hbefore]
  simpa only [hcarried, hnext] using step

private theorem carrySteps_to_state_zero {r : RawDigits}
    (canonical : CanonicalRaw r) {count : Nat}
    (hcount : count <= gapCount r 0) :
    CarrySteps count (r + Finsupp.single 0 1) (carryState r 0 count) := by
  induction count with
  | zero =>
      rw [carryState_zero]
      exact CarrySteps.zero _
  | succ count ih =>
      apply CarrySteps.succ (ih (by omega))
      exact carryState_step_zero canonical (by omega)

private theorem carrySteps_to_state_one {r : RawDigits}
    (canonical : CanonicalRaw r) {count : Nat}
    (hcount : count <= gapCount r 1) :
    CarrySteps count (r + Finsupp.single 0 1) (carryState r 1 count) := by
  induction count with
  | zero =>
      rw [carryState_one]
      exact CarrySteps.zero _
  | succ count ih =>
      apply CarrySteps.succ (ih (by omega))
      exact carryState_step_one canonical (by omega)

private theorem carried_original_zero_zero {r : RawDigits}
    (canonical : CanonicalRaw r) (hzero : r 0 = 1) :
    r (carriedIndex 0 (gapCount r 0)) = 0 := by
  have hpos : 0 < gapCount r 0 := by
    by_contra hpos
    have hcount : gapCount r 0 = 0 := Nat.eq_zero_of_not_pos hpos
    have hgap := gapCount_spec r 0
    simp [hcount, prefixIndex] at hgap
    omega
  let j := gapCount r 0 - 1
  have hj : j < gapCount r 0 := by omega
  have hbit := gapCount_prefix_eq_one canonical 0 j hj
  have hnext := canonical.2 (prefixIndex 0 j) hbit
  have hindex : prefixIndex 0 j + 1 = carriedIndex 0 (gapCount r 0) := by
    dsimp [j, prefixIndex, carriedIndex]
    omega
  simpa [hindex] using hnext

private theorem carried_original_zero_one {r : RawDigits}
    (canonical : CanonicalRaw r) (hzero : r 0 = 0) :
    r (carriedIndex 1 (gapCount r 1)) = 0 := by
  by_cases hcount : gapCount r 1 = 0
  · simp [hcount, carriedIndex, prefixIndex, hzero]
  · let j := gapCount r 1 - 1
    have hj : j < gapCount r 1 := by omega
    have hbit := gapCount_prefix_eq_one canonical 1 j hj
    have hnext := canonical.2 (prefixIndex 1 j) hbit
    have hindex : prefixIndex 1 j + 1 = carriedIndex 1 (gapCount r 1) := by
      dsimp [j, prefixIndex, carriedIndex]
      omega
    simpa [hindex] using hnext

private theorem carryState_final_canonical {r : RawDigits}
    (canonical : CanonicalRaw r) (offset : Nat)
    (hoffset : offset = 0 ∨ offset = 1)
    (hpositive : offset = 0 -> 0 < gapCount r offset)
    (hcarried : r (carriedIndex offset (gapCount r offset)) = 0) :
    CanonicalRaw (carryState r offset (gapCount r offset)) := by
  let count := gapCount r offset
  let stripped := stripPrefix r offset count
  have hstripped := canonical_stripPrefix canonical offset count
  have hhere : stripped (carriedIndex offset count) = 0 := by
    rw [stripPrefix_apply]
    split
    · rfl
    · exact hcarried
  have hnext : stripped (carriedIndex offset count + 1) = 0 := by
    rw [stripPrefix_apply]
    have hindex : carriedIndex offset count + 1 = prefixIndex offset count := by
      rcases hoffset with rfl | rfl
      · have hcount : 0 < count := by
          simpa [count] using hpositive rfl
        simp only [carriedIndex, prefixIndex]
        omega
      · simp only [carriedIndex, prefixIndex]
        omega
    rw [hindex, gapCount_spec]
    split <;> rfl
  have hprevious : carriedIndex offset count = 0 ∨
      stripped (carriedIndex offset count - 1) = 0 := by
    by_cases hindex : carriedIndex offset count = 0
    · exact Or.inl hindex
    · right
      rw [stripPrefix_apply]
      have hcount : 0 < count := by
        rcases hoffset with rfl | rfl <;>
          simp [carriedIndex, prefixIndex] at hindex <;> omega
      have hp : InPrefix offset count (carriedIndex offset count - 1) :=
        (inPrefix_iff offset count _).2 ⟨count - 1, by omega, by
          rcases hoffset with rfl | rfl <;>
            simp [carriedIndex, prefixIndex] <;> omega⟩
      simp [hp]
  change CanonicalRaw (stripped +
    Finsupp.single (carriedIndex offset count) 1)
  exact canonical_add_single hstripped hhere hprevious hnext

private theorem rawValue_successorInput (n : Nat) :
    rawValue (rawOfZeckendorf (Nat.zeckendorf n) + Finsupp.single 0 1) =
      n + 1 := by
  rw [rawValue_add, rawValue_rawOfZeckendorf
      (Nat.isZeckendorfRep_zeckendorf n), Nat.sum_zeckendorf_fib,
    rawValue_single]
  norm_num [wValue]

/--
The Zeckendorf successor operation is realized by a finite local carry chain.
Its exact number of steps is bounded by one plus the largest occupied raw index,
which is the source convention's highest Fibonacci index. The endpoint is the
canonical Zeckendorf representation of `n + 1`.
-/
theorem zeckendorf_successor_carry_terminates (n : Nat) :
    let r := rawOfZeckendorf (Nat.zeckendorf n)
    Exists fun steps =>
      steps <= r.support.sup id + 1 ∧
      CarrySteps steps (r + Finsupp.single 0 1)
        (rawOfZeckendorf (Nat.zeckendorf (n + 1))) := by
  dsimp only
  let r := rawOfZeckendorf (Nat.zeckendorf n)
  have canonical : CanonicalRaw r :=
    canonicalRaw_rawOfZeckendorf (Nat.isZeckendorfRep_zeckendorf n)
  by_cases hzero : r 0 = 1
  · let steps := gapCount r 0
    let target := carryState r 0 steps
    have chain : CarrySteps steps (r + Finsupp.single 0 1) target :=
      carrySteps_to_state_zero canonical (by exact le_rfl)
    have targetCanonical : CanonicalRaw target :=
      carryState_final_canonical canonical 0 (Or.inl rfl)
        (by
          intro _
          by_contra hpos
          have hcount : gapCount r 0 = 0 := Nat.eq_zero_of_not_pos hpos
          have hgap := gapCount_spec r 0
          simp [hcount, prefixIndex] at hgap
          omega)
        (carried_original_zero_zero canonical hzero)
    have targetValue : rawValue target = n + 1 := by
      rw [← rawValue_carrySteps chain]
      exact rawValue_successorInput n
    have targetEq : target = rawOfZeckendorf (Nat.zeckendorf (n + 1)) := by
      apply canonicalRaw_unique targetCanonical
        (canonicalRaw_rawOfZeckendorf (Nat.isZeckendorfRep_zeckendorf (n + 1)))
      rw [targetValue, rawValue_rawOfZeckendorf
        (Nat.isZeckendorfRep_zeckendorf (n + 1)), Nat.sum_zeckendorf_fib]
    refine ⟨steps, gapCount_le_highestIndexBound r 0, ?_⟩
    simpa [targetEq] using chain
  · have hzero' : r 0 = 0 := by
      have hle := canonical.1 0
      omega
    let steps := gapCount r 1
    let target := carryState r 1 steps
    have chain : CarrySteps steps (r + Finsupp.single 0 1) target :=
      carrySteps_to_state_one canonical (by exact le_rfl)
    have targetCanonical : CanonicalRaw target :=
      carryState_final_canonical canonical 1 (Or.inr rfl)
        (by intro h; omega)
        (carried_original_zero_one canonical hzero')
    have targetValue : rawValue target = n + 1 := by
      rw [← rawValue_carrySteps chain]
      exact rawValue_successorInput n
    have targetEq : target = rawOfZeckendorf (Nat.zeckendorf (n + 1)) := by
      apply canonicalRaw_unique targetCanonical
        (canonicalRaw_rawOfZeckendorf (Nat.isZeckendorfRep_zeckendorf (n + 1)))
      rw [targetValue, rawValue_rawOfZeckendorf
        (Nat.isZeckendorfRep_zeckendorf (n + 1)), Nat.sum_zeckendorf_fib]
    refine ⟨steps, gapCount_le_highestIndexBound r 1, ?_⟩
    simpa [targetEq] using chain

end D5.S1.Digit.Carry.Successor
