/- GID: D5/X_Frontier/BasePhiNegativePrefixTrident
   generality: I
   mirror-B: none(waiver:negative-base-phi-frontier)
   mirror-E: D5/E/S1/Words/BasePhiNegativePrefixTrident.result--json
   anchors: []
   digest: Classify admissible negative base-phi prefix occurrence sets by Lucas-gap trident families. -/

import D5.S1.Words.Expansions.BasePhiNegative

namespace D5.X_Frontier.BasePhiNegativePrefixTrident

open D5.S1.Words.Expansions.BasePhiNegative

/-!
The source question asks for an exact classification of occurrence sequences
for finite negative-position prefix cylinders in the two-sided base-phi
expansion. The regular `BasePhiNegative` module owns the integer-pair value
equation, non-adjacent digits, and the paper's `F`, `G`, and `H` gap families.
The finite scan is evidence for this classification, not its proof.

## Existing interface status

The supporting declarations in `BasePhiNegative` are retained with their exact
scope. `admissible_negative_prefix_iff_occurrence_set_nonempty` is an `rfl`
interface between two definitions. The three `vF_succ`/`vG_succ`/`vH_succ`
lemmas are definitional recurrence interfaces. The two `single_digit_*` lemmas
are only the depth-one Bool partition and disjointness theorem; they do not
identify either occurrence set with an `F`, `G`, or `H` formula. None of these
interfaces is a substantive classification milestone.

## Executable obstruction targets

1. Construct the canonical two-sided expansion and prove uniqueness. Finite
   support is carried by `Int →₀ Nat`; the statement exposes the binary,
   non-adjacency, and exact-value invariants rather than hiding them in a choice:

```lean
theorem canonical_base_phi_digits_exists_unique :
    ∀ N : Nat, ∃! digits : Int →₀ Nat,
      (∀ i : Int, digits i ≤ 1) ∧
      (∀ i : Int, digits i = 1 → digits (i + 1) = 0) ∧
      basePhiValue digits = (N : D5.S0.Carrier.GoldenInt)
```

2. Identify every nonnegative base-phi position with mathlib's occupied
   Fibonacci indices. `Finset.range N` counts exactly the earlier `d₋₁ = 1`
   events, and `k + 2` is the invariant alignment with mathlib's Fibonacci
   indices (`W_k = Nat.fib (k + 2)`):

```lean
theorem nonnegative_digit_iff_mem_zeckendorf_after_negative_one_skips
    (expansion : BasePhiNegativeExpansion) :
    ∀ N k : Nat,
      expansion.digit N (k : Int) = 1 ↔
        k + 2 ∈ Nat.zeckendorf
          (N + ((Finset.range N).filter
            (fun j => negativeDigit expansion j 0 = true)).card)
```

3. Characterize the first negative digit by the generalized Beatty sequence.
   The witness is quantified in Lean's zero-based `Nat`, so `n + 1` preserves
   the paper's one-based sequence index and excludes the spurious `N = 1` term:

```lean
theorem negative_one_digit_iff_generalized_beatty
    (expansion : BasePhiNegativeExpansion) :
    ∀ N : Nat,
      negativeDigit expansion N 0 = true ↔
        ∃ n : Nat,
          (N : Int) =
            3 * ⌊(((n + 1 : Nat) : ℝ) * Real.goldenRatio)⌋ +
              ((n + 1 : Nat) : Int) + 1
```

The second and third targets together provide the first exact cylinder formula;
only after them may a carry transducer transport longer prefixes into the
existing return-word layer. They are lemma signatures, not proved milestones.
-/

/- THEORIST_FRONTIER_CONTRACT_V2
{
  "schema": "trureturing-theorist-frontier-v2",
  "exact_statement": {
    "gid": "D5/X_Frontier/BasePhiNegativePrefixTrident.negative_prefix_trident_classification",
    "statement_sha256": "sha256:25ddd0972fd7b97c88f87ea47bb9843e5c014cdad5344c37451293f18cb4a0d9"
  },
  "motivation_gids": [
    "D5/S0/Conventions/WDigits",
    "D5/S1/Deficit/ZeckendorfDisplacementReading",
    "D5/S1/Words/Complexity/MechanicalSubshiftIntercept",
    "D5/S1/Words/GoldenMechanicalWord",
    "D5/S1/Words/GoldenSubstFixed",
    "D5/S1/Words/ReturnWords/GoldenOccurrenceGaps",
    "D5/S1/Words/ReturnWords/GoldenReturnItinerary",
    "D5/S1/Words/ReturnWords/GoldenReturnWords",
    "D5/S1/Words/ReturnWords/GoldenReturnWordsExact",
    "D5/S1/Words/ZeckendorfBeattyBridge",
    "D5/S1/Words/ZeckendorfOrder"
  ],
  "falsifier": "An admissible negative prefix w whose exact occurrence set is neither one Lucas-gap F/G/H sequence range nor a union of three such ranges sharing one Lucas pair.",
  "search_receipt_gids": ["D5/L/Words/dekking2023structure"],
  "computation_receipt_gids": ["D5/E/S1/Words/BasePhiNegativePrefixTrident.result--json"],
  "triage_class": "theorem"
}
-/

/- TASK D5-T0046
   Formalize the two-sided base-phi digit/value bridge and classify every
   admissible negative prefix as one Lucas-gap F/G/H family or a union of
   three such families sharing one Lucas pair. The N<=2,000,000 exact
   integer-pair scan is finite evidence only; it does not close this theorem.
-/

/- include_in_statement=true -/
theorem negative_prefix_trident_classification
    (expansion : BasePhiNegativeExpansion) :
    ∀ w : List Bool,
      AdmissibleNegativePrefix expansion w →
        (∃ a b r, 0 < r ∧ lucasParameter a ∧ lucasParameter b ∧
          occurrenceSet expansion w = sequenceRange (vF a b r)) ∨
        (∃ a b r, 0 < r ∧ lucasParameter a ∧ lucasParameter b ∧
          occurrenceSet expansion w = sequenceRange (vG a b r)) ∨
        (∃ a b r, 0 < r ∧ lucasParameter a ∧ lucasParameter b ∧
          occurrenceSet expansion w = sequenceRange (vH a b r)) ∨
        (∃ (a b : Int) (families : Fin 3 → GapFamily) (first : Fin 3 → Int),
          lucasParameter a ∧ lucasParameter b ∧ (∀ i, 0 < first i) ∧
          occurrenceSet expansion w =
            ⋃ i, sequenceRange (vForFamily (families i) a b (first i))) := by
  sorry

end D5.X_Frontier.BasePhiNegativePrefixTrident
