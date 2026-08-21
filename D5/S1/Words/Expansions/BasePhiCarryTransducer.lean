/- GID: D5/S1/Words/Expansions/BasePhiCarryTransducer
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:algebraically-proved)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf]
   digest: A terminating carry/skip transducer specification from two-sided base-phi digits to Zeckendorf digits. -/

import D5.S1.Words.Expansions.BasePhiNegative
import D5.S1.Digit.Normalize
import D5.S1.Scale.Log
import D5.S1.Deficit.DoubleFaceLength

/-! Library reuse receipt:
`normalize_canonical`, `normalize_reachable`, `rawValue_normalize`,
`canonicalRaw_unique`, and `rawToZeckendorf_eq_zeckendorf` are the existing
normalization interfaces; `Nat.sum_zeckendorf_fib` and
`Nat.zeckendorf_sum_fib` are the existing Fibonacci/Zeckendorf interfaces.
No parallel carry theorem is introduced here. -/

namespace D5.S1.Words.Expansions.BasePhiCarryTransducer

noncomputable section

open D5.S0.Conventions
open D5.S0.Carrier
open D5.S1.Deficit
open D5.S1.Deficit.DoubleFaceLength
open D5.S1.Digit
open D5.S1.Scale
open D5.S1.Words.Expansions.BasePhiNegative

local instance (priority := low) (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Restrict a two-sided base-phi digit family to its nonnegative exponents. -/
noncomputable def nonnegativeDigits (expansion : BasePhiNegativeExpansion)
    (N : Nat) : RawDigits :=
  (Finsupp.comapDomain.addMonoidHom (f := fun k : Nat => (k : Int))
    Int.ofNat_injective) (expansion.digit N)

@[simp] theorem nonnegativeDigits_apply (expansion : BasePhiNegativeExpansion)
    (N k : Nat) : nonnegativeDigits expansion N k = expansion.digit N (k : Int) := by
  rfl

/-- A finite binary candidate whose base-phi value is zero has no occupied
position; positivity of the real embedding handles all integer exponents. -/
theorem digits_eq_zero_of_basePhiValue_eq_zero (digits : Int →₀ Nat)
    (value : basePhiValue digits = 0) : digits = 0 := by
  have unitEmbedding : ∀ i : Int,
      embedding (((phiUnit ^ i : GoldenIntˣ) : GoldenInt)) =
        Real.goldenRatio ^ i := by
    intro i
    simpa [phiUnitZPowMul] using
      (embedding_phiUnitZPowMul i (1 : GoldenInt))
  apply Finsupp.ext
  intro i
  by_contra nonzero
  have support : i ∈ digits.support := Finsupp.mem_support_iff.mpr nonzero
  have positive : 0 < embedding (basePhiValue digits) := by
    rw [basePhiValue, map_sum]
    apply Finset.sum_pos'
    · intro j _
      rw [map_mul, unitEmbedding]
      have coefficient : (0 : ℝ) ≤ embedding (digits j : GoldenInt) := by
        rw [map_natCast]
        exact_mod_cast Nat.zero_le (digits j)
      exact mul_nonneg coefficient
        (le_of_lt (zpow_pos Real.goldenRatio_pos j))
    · refine ⟨i, support, ?_⟩
      rw [map_mul, unitEmbedding]
      have coefficient : 0 < embedding (digits i : GoldenInt) := by
        rw [map_natCast]
        exact_mod_cast Nat.pos_of_ne_zero nonzero
      exact mul_pos coefficient (zpow_pos Real.goldenRatio_pos i)
  rw [value, map_zero] at positive
  exact (lt_self_iff_false 0).mp positive

/-- The actual nonnegative output has value zero before the first input. -/
theorem nonnegative_raw_value_initial
    (expansion : BasePhiNegativeExpansion) :
    rawValue (nonnegativeDigits expansion 0) = 0 := by
  have value : basePhiValue (expansion.digit 0) = 0 := by
    simpa using expansion.value_equation 0
  have digits_zero : expansion.digit 0 = 0 :=
    digits_eq_zero_of_basePhiValue_eq_zero _ value
  simp [nonnegativeDigits, digits_zero, rawValue]

/-- The nonnegative restriction retains binary digits and non-adjacency. -/
theorem nonnegativeDigits_canonical (expansion : BasePhiNegativeExpansion) (N : Nat) :
    CanonicalRaw (nonnegativeDigits expansion N) := by
  constructor
  · intro k
    rw [nonnegativeDigits_apply]
    exact expansion.binary N (k : Int)
  · intro k hk
    rw [nonnegativeDigits_apply] at hk ⊢
    simpa using expansion.canonical N (k : Int) hk

/-- The indicator of the `d_-1 = 1` event at input `N`. -/
def negativeOneEvent (expansion : BasePhiNegativeExpansion) (N : Nat) : Nat :=
  if negativeDigit expansion N 0 = true then 1 else 0

/-- Number of earlier `d_-1 = 1` events among inputs `0, ..., N - 1`. -/
def negativeOneCount (expansion : BasePhiNegativeExpansion) (N : Nat) : Nat :=
  ((Finset.range N).filter
    (fun j => negativeDigit expansion j 0 = true)).card

@[simp] theorem negativeOneCount_zero (expansion : BasePhiNegativeExpansion) :
    negativeOneCount expansion 0 = 0 := by
  simp [negativeOneCount]

/-- Advancing one input records exactly the current `d_-1` event. -/
theorem negativeOneCount_succ (expansion : BasePhiNegativeExpansion) (N : Nat) :
    negativeOneCount expansion (N + 1) =
      negativeOneCount expansion N + negativeOneEvent expansion N := by
  rw [negativeOneCount, negativeOneCount, Finset.range_add_one,
    Finset.filter_insert]
  by_cases event : negativeDigit expansion N 0 = true
  · simp [event, negativeOneEvent]
  · simp [event, negativeOneEvent]

/-- One transducer step adds one W-token, plus one more exactly on a `d_-1` event,
then runs the repository's well-founded local-carry normalizer. -/
noncomputable def carrySkipStep (expansion : BasePhiNegativeExpansion)
    (N : Nat) (positive : RawDigits) : RawDigits :=
  normalize (positive + Finsupp.single 0 (1 + negativeOneEvent expansion N))

/-- The carry/skip step terminates at canonical raw digits. -/
theorem carrySkipStep_canonical (expansion : BasePhiNegativeExpansion)
    (N : Nat) (positive : RawDigits) :
    CanonicalRaw (carrySkipStep expansion N positive) := by
  exact normalize_canonical _

/-- The step is a finite chain of the explicit adjacency/repetition carry rules. -/
theorem carrySkipStep_reachable (expansion : BasePhiNegativeExpansion)
    (N : Nat) (positive : RawDigits) :
    Relation.ReflTransGen CarryStep
      (positive + Finsupp.single 0 (1 + negativeOneEvent expansion N))
      (carrySkipStep expansion N positive) := by
  exact normalize_reachable _

/-- The step adds one represented integer, or two when the current input has `d_-1 = 1`. -/
theorem rawValue_carrySkipStep (expansion : BasePhiNegativeExpansion)
    (N : Nat) (positive : RawDigits) :
    rawValue (carrySkipStep expansion N positive) =
      rawValue positive + 1 + negativeOneEvent expansion N := by
  rw [carrySkipStep, rawValue_normalize, rawValue_add, rawValue_single]
  simp [wValue, Nat.add_assoc]

/-- Complete state exposed by the deterministic transducer. -/
structure CarrySkipState where
  input : Nat
  skips : Nat
  positive : RawDigits

/-- The initial state, before input zero. -/
def initialState : CarrySkipState :=
  { input := 0, skips := 0, positive := 0 }

/-- The deterministic state transition. -/
noncomputable def nextState (expansion : BasePhiNegativeExpansion)
    (state : CarrySkipState) : CarrySkipState :=
  { input := state.input + 1
    skips := state.skips + negativeOneEvent expansion state.input
    positive := carrySkipStep expansion state.input state.positive }

/-- A transition is exactly one application of `nextState`; no hidden transition is allowed. -/
def CarrySkipTransition (expansion : BasePhiNegativeExpansion)
    (before after : CarrySkipState) : Prop :=
  after = nextState expansion before

/-- Every state has one transition witness. -/
theorem carrySkipTransition_exists (expansion : BasePhiNegativeExpansion)
    (state : CarrySkipState) :
    ∃ after, CarrySkipTransition expansion state after :=
  ⟨nextState expansion state, rfl⟩

/-- The transition relation has no nondeterministic successors. -/
theorem carrySkipTransition_unique (expansion : BasePhiNegativeExpansion)
    {state after₁ after₂ : CarrySkipState}
    (h₁ : CarrySkipTransition expansion state after₁)
    (h₂ : CarrySkipTransition expansion state after₂) :
    after₁ = after₂ := by
  rw [CarrySkipTransition] at h₁ h₂
  exact h₁.trans h₂.symm

/-- State invariant: the counter is the exact earlier-event count, the output is canonical,
and its Fibonacci value is `input + skips`. -/
def CarrySkipInvariant (expansion : BasePhiNegativeExpansion)
    (state : CarrySkipState) : Prop :=
  state.skips = negativeOneCount expansion state.input ∧
    CanonicalRaw state.positive ∧
    rawValue state.positive = state.input + state.skips

/-- The initial state satisfies the complete invariant. -/
theorem initialState_invariant (expansion : BasePhiNegativeExpansion) :
    CarrySkipInvariant expansion initialState := by
  simp [CarrySkipInvariant, initialState, CanonicalRaw, rawValue]

/-- Every deterministic carry/skip transition preserves the complete invariant. -/
theorem nextState_invariant (expansion : BasePhiNegativeExpansion)
    {state : CarrySkipState} (invariant : CarrySkipInvariant expansion state) :
    CarrySkipInvariant expansion (nextState expansion state) := by
  rcases invariant with ⟨hcount, hcanonical, hvalue⟩
  refine ⟨?_, ?_, ?_⟩
  · change state.skips + negativeOneEvent expansion state.input =
      negativeOneCount expansion (state.input + 1)
    rw [negativeOneCount_succ, hcount]
  · change CanonicalRaw (carrySkipStep expansion state.input state.positive)
    exact carrySkipStep_canonical _ _ _
  · change rawValue (carrySkipStep expansion state.input state.positive) =
      state.input + 1 + (state.skips + negativeOneEvent expansion state.input)
    rw [rawValue_carrySkipStep, hvalue]
    omega

/-- The terminal state after exactly `N` deterministic transitions. -/
noncomputable def carrySkipRun (expansion : BasePhiNegativeExpansion) :
    Nat → CarrySkipState
  | 0 => initialState
  | N + 1 => nextState expansion (carrySkipRun expansion N)

@[simp] theorem carrySkipRun_zero (expansion : BasePhiNegativeExpansion) :
    carrySkipRun expansion 0 = initialState := rfl

@[simp] theorem carrySkipRun_succ (expansion : BasePhiNegativeExpansion) (N : Nat) :
    carrySkipRun expansion (N + 1) =
      nextState expansion (carrySkipRun expansion N) := rfl

/-- Every finite run terminates in a state satisfying the invariant. -/
theorem carrySkipRun_invariant (expansion : BasePhiNegativeExpansion) :
    ∀ N : Nat, CarrySkipInvariant expansion (carrySkipRun expansion N)
  | 0 => initialState_invariant expansion
  | N + 1 => nextState_invariant expansion (carrySkipRun_invariant expansion N)

/-- The terminal state's input coordinate is the number of transitions. -/
@[simp] theorem carrySkipRun_input (expansion : BasePhiNegativeExpansion) :
    ∀ N : Nat, (carrySkipRun expansion N).input = N
  | 0 => rfl
  | N + 1 => by
      rw [carrySkipRun_succ, nextState, carrySkipRun_input expansion N]

/-- The terminal state's skip coordinate counts exactly the earlier `d_-1 = 1` events. -/
theorem carrySkipRun_skips (expansion : BasePhiNegativeExpansion) (N : Nat) :
    (carrySkipRun expansion N).skips = negativeOneCount expansion N := by
  exact (carrySkipRun_invariant expansion N).1.trans
    (congrArg (negativeOneCount expansion) (carrySkipRun_input expansion N))

/-- The terminal raw output is exactly mathlib's Zeckendorf representation at value
`N + #{j < N | d_-1(j) = 1}`. -/
theorem carrySkipRun_zeckendorf (expansion : BasePhiNegativeExpansion) (N : Nat) :
    rawToZeckendorf (carrySkipRun expansion N).positive =
      Nat.zeckendorf (N + negativeOneCount expansion N) := by
  have invariant := carrySkipRun_invariant expansion N
  rw [rawToZeckendorf_eq_zeckendorf invariant.2.1, invariant.2.2,
    carrySkipRun_input, carrySkipRun_skips]

/-- Membership in the shifted raw list is exactly occupancy of raw index `k`.
This is the explicit `k + 2` alignment with mathlib Fibonacci indices. -/
theorem mem_rawToZeckendorf_iff {positive : RawDigits}
    (canonical : CanonicalRaw positive) (k : Nat) :
    k + 2 ∈ rawToZeckendorf positive ↔ positive k = 1 := by
  rw [rawToZeckendorf]
  constructor
  · intro hmem
    obtain ⟨i, hi, hik⟩ := List.mem_map.mp hmem
    have hi_mem : i ∈ positive.toMultiset := by simpa using hi
    have hi_ne : positive i ≠ 0 := by simpa using hi_mem
    have hi_one : positive i = 1 := by
      have := canonical.1 i
      omega
    have : i = k := by omega
    simpa [this] using hi_one
  · intro hk
    apply List.mem_map.mpr
    refine ⟨k, ?_, rfl⟩
    have hk_ne : positive k ≠ 0 := by omega
    have hk_mem : k ∈ positive.toMultiset := by simpa using hk_ne
    simpa using hk_mem

/-- The only remaining semantic realization obligation: the transducer's raw output must be
the actual nonnegative restriction of the canonical two-sided expansion. -/
def CarrySkipRealizes (expansion : BasePhiNegativeExpansion) (N : Nat) : Prop :=
  (carrySkipRun expansion N).positive = nonnegativeDigits expansion N

/-- Realization is equivalent to the one missing scalar invariant for the actual
nonnegative digits; canonical uniqueness supplies the digitwise equality. -/
theorem carrySkipRealizes_iff_rawValue_eq
    (expansion : BasePhiNegativeExpansion) (N : Nat) :
    CarrySkipRealizes expansion N ↔
      rawValue (nonnegativeDigits expansion N) =
        N + negativeOneCount expansion N := by
  have runInvariant := carrySkipRun_invariant expansion N
  constructor
  · intro realizes
    rw [← realizes, runInvariant.2.2, carrySkipRun_input,
      carrySkipRun_skips]
  · intro value
    apply canonicalRaw_unique runInvariant.2.1
      (nonnegativeDigits_canonical expansion N)
    rw [runInvariant.2.2, carrySkipRun_input, carrySkipRun_skips, value]

/-- The complete semantic realization reduces to an initial value and the exact
successor increment forced by the current `d_-1` event. -/
theorem carry_skip_realization_iff_value_recurrence
    (expansion : BasePhiNegativeExpansion) :
    (∀ N : Nat, CarrySkipRealizes expansion N) ↔
      ∀ N : Nat,
        rawValue (nonnegativeDigits expansion (N + 1)) =
          rawValue (nonnegativeDigits expansion N) + 1 +
            negativeOneEvent expansion N := by
  constructor
  · intro realizes
    intro N
    have current := (carrySkipRealizes_iff_rawValue_eq expansion N).1
      (realizes N)
    have next := (carrySkipRealizes_iff_rawValue_eq expansion (N + 1)).1
      (realizes (N + 1))
    rw [negativeOneCount_succ] at next
    omega
  · intro step
    intro N
    apply (carrySkipRealizes_iff_rawValue_eq expansion N).2
    induction N with
    | zero => simpa using nonnegative_raw_value_initial expansion
    | succ N inductionHypothesis =>
        rw [step, inductionHypothesis, negativeOneCount_succ]
        omega

/-- Once realization is supplied, every nonnegative base-phi digit is identified with the
corresponding occupied mathlib Fibonacci index. -/
theorem nonnegative_digit_iff_mem_zeckendorf_of_realizes
    (expansion : BasePhiNegativeExpansion)
    (realizes : ∀ N : Nat, CarrySkipRealizes expansion N) :
    ∀ N k : Nat,
      expansion.digit N (k : Int) = 1 ↔
        k + 2 ∈ Nat.zeckendorf (N + negativeOneCount expansion N) := by
  intro N k
  have canonical := nonnegativeDigits_canonical expansion N
  rw [← nonnegativeDigits_apply, ← mem_rawToZeckendorf_iff canonical,
    ← realizes N, carrySkipRun_zeckendorf]

/-- A proved first-negative-digit characterization rewrites the transducer counter to the
finite count of generalized-Beatty witnesses below `N`. -/
theorem negativeOneCount_eq_generalizedBeatty_count
    (expansion : BasePhiNegativeExpansion)
    (beatty : ∀ N : Nat,
      negativeDigit expansion N 0 = true ↔
        ∃ n : Nat,
          (N : Int) =
            3 * ⌊(((n + 1 : Nat) : Real) * Real.goldenRatio)⌋ +
              ((n + 1 : Nat) : Int) + 1)
    (N : Nat) :
    negativeOneCount expansion N =
      ((Finset.range N).filter (fun j : Nat =>
        ∃ n : Nat,
          (j : Int) =
            3 * ⌊(((n + 1 : Nat) : Real) * Real.goldenRatio)⌋ +
              ((n + 1 : Nat) : Int) + 1)).card := by
  classical
  apply congrArg Finset.card
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  exact and_congr_right fun _ => beatty j

/-!
## Executable residual signatures

The following are the complete open obligations after the proved structural
transducer above. Every symbol is defined in an imported or present module;
the quantifiers and invariants are explicit.

### Target 1: canonical two-sided construction and uniqueness

The construction lane must prove the high even-shift identity and expose the
shifted finite-support embedding. The uniqueness lane must eliminate the least
index of the symmetric difference; no prose-level "common support" shortcut
is accepted.

```lean
theorem betaGolden_even_shift :
    ∀ N : Nat,
      betaGolden (N * Nat.fib (2 * (N + 2))) =
        (N : D5.S0.Carrier.GoldenInt) *
          D5.S0.Carrier.phi ^ (2 * (N + 2))

theorem shifted_normalized_digits_spec :
    ∀ N : Nat, ∃ digits : Int →₀ Nat,
      (∀ i : Int, digits i ≤ 1) ∧
      (∀ i : Int, digits i = 1 → digits (i + 1) = 0) ∧
      basePhiValue digits = (N : D5.S0.Carrier.GoldenInt) ∧
      (∀ i ∈ digits.support, -((2 * (N + 2) : Nat) : Int) ≤ i)

theorem canonical_two_sided_digits_unique :
    ∀ digits₁ digits₂ : Int →₀ Nat,
      (∀ i : Int, digits₁ i ≤ 1) →
      (∀ i : Int, digits₁ i = 1 → digits₁ (i + 1) = 0) →
      (∀ i : Int, digits₂ i ≤ 1) →
      (∀ i : Int, digits₂ i = 1 → digits₂ (i + 1) = 0) →
      basePhiValue digits₁ = basePhiValue digits₂ →
      digits₁ = digits₂
```

These three signatures imply the frontier's exact `∃!` target.

### Target 2: realization of the proved carry/skip machine

```lean
theorem nonnegative_raw_value_succ
    (expansion : BasePhiNegativeExpansion) :
    ∀ N : Nat,
      rawValue (nonnegativeDigits expansion (N + 1)) =
        rawValue (nonnegativeDigits expansion N) + 1 +
          negativeOneEvent expansion N
```

`nonnegative_raw_value_initial` is proved above.
`carry_skip_realization_iff_value_recurrence` proves that the successor
signature is exactly equivalent to `∀ N, CarrySkipRealizes expansion N`.
`carrySkipRun_invariant`, `carrySkipRun_skips`,
`carrySkipRun_zeckendorf`, and
`nonnegative_digit_iff_mem_zeckendorf_of_realizes` prove every other state,
termination, count, and `k + 2` obligation.

### Target 3: exact event language

```lean
theorem negative_one_digit_iff_generalized_beatty
    (expansion : BasePhiNegativeExpansion) :
    ∀ N : Nat,
      negativeDigit expansion N 0 = true ↔
        ∃ n : Nat,
          (N : Int) =
            3 * ⌊(((n + 1 : Nat) : Real) * Real.goldenRatio)⌋ +
              ((n + 1 : Nat) : Int) + 1
```

The one-based-to-zero-based convention is explicit in `n + 1`.
`negativeOneCount_eq_generalizedBeatty_count` then transports it to the
transducer's event counter.
-/

end

end D5.S1.Words.Expansions.BasePhiCarryTransducer
