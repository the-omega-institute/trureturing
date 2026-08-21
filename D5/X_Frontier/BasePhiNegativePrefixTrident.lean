/- GID: D5/X_Frontier/BasePhiNegativePrefixTrident
   generality: I
   mirror-B: none(waiver:negative-base-phi-frontier)
   mirror-E: D5/E/S1/Words/BasePhiNegativePrefixTrident.result--json
   anchors: []
   digest: Classify admissible negative base-phi prefix occurrence sets by Lucas-gap trident families. -/

import D5.S1.Words.Expansions.BasePhiCarryTransducer
import D5.S1.Words.Expansions.BasePhiCanonicalExpansion

namespace D5.X_Frontier.BasePhiNegativePrefixTrident

open D5.S1.Words.Expansions.BasePhiNegative
open D5.S1.Words.Expansions.BasePhiCanonicalExpansion
open D5.S1.Scale

noncomputable section

/-!
The canonical-expansion bridge is useful here even before the return-word
classification is available.  It removes the otherwise arbitrary choice of
`BasePhiNegativeExpansion` from every occurrence-set statement.
-/

noncomputable def canonicalDigits (N : Nat) : Int →₀ Nat :=
  Classical.choose (basePhiExpansion_exists N)

theorem canonicalDigits_spec (N : Nat) :
    (∀ i : Int, canonicalDigits N i ≤ 1) ∧
      (∀ i : Int, canonicalDigits N i = 1 → canonicalDigits N (i + 1) = 0) ∧
      basePhiValue (canonicalDigits N) = (N : D5.S0.Carrier.GoldenInt) := by
  exact Classical.choose_spec (basePhiExpansion_exists N)

noncomputable def canonicalExpansion : BasePhiNegativeExpansion :=
  { digit := canonicalDigits
    binary := fun N i => (canonicalDigits_spec N).1 i
    canonical := fun N i => (canonicalDigits_spec N).2.1 i
    value_equation := fun N => (canonicalDigits_spec N).2.2 }

theorem expansion_digit_eq_canonical (expansion : BasePhiNegativeExpansion) (N : Nat) :
    expansion.digit N = canonicalDigits N := by
  obtain ⟨digits, hdigits, hunique⟩ := basePhiExpansion_existsUnique N
  exact (hunique (expansion.digit N) ⟨expansion.binary N, expansion.canonical N,
    expansion.value_equation N⟩).trans
    (hunique (canonicalDigits N) (canonicalDigits_spec N)).symm

theorem occurrenceSet_eq_canonical (expansion : BasePhiNegativeExpansion)
    (w : List Bool) :
    occurrenceSet expansion w = occurrenceSet canonicalExpansion w := by
  ext N
  have hdigits : expansion.digit N = canonicalExpansion.digit N := by
    exact expansion_digit_eq_canonical expansion N
  constructor <;> intro h
  · rcases h with ⟨hpositive, hoccurs⟩
    refine ⟨hpositive, ?_⟩
    simpa [NegativePrefixOccurs, reachesNegativeDepth, negativeDigit, hdigits] using hoccurs
  · rcases h with ⟨hpositive, hoccurs⟩
    refine ⟨hpositive, ?_⟩
    simpa [NegativePrefixOccurs, reachesNegativeDepth, negativeDigit, hdigits] using hoccurs

theorem occurrenceSet_nonempty_of_admissible (expansion : BasePhiNegativeExpansion)
    {w : List Bool} (h : AdmissibleNegativePrefix expansion w) :
    (occurrenceSet expansion w).Nonempty :=
  (admissible_negative_prefix_iff_occurrence_set_nonempty expansion w).mp h

theorem occurrenceSet_subset_positive (expansion : BasePhiNegativeExpansion)
    (w : List Bool) :
    occurrenceSet expansion w ⊆ {N | 0 < N} := by
  intro N hN
  exact hN.1

theorem admissible_prefix_no_adjacent_true (expansion : BasePhiNegativeExpansion)
    {w : List Bool} (h : AdmissibleNegativePrefix expansion w) :
    ∀ i : Nat, ∀ hi : i + 1 < w.length,
      ¬(w.get ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩ = true ∧
        w.get ⟨i + 1, hi⟩ = true) := by
  intro i hi hbits
  exact not_admissible_negative_prefix_of_adjacent_true expansion w i hi
    hbits.1 hbits.2 h

def TridentWitness (expansion : BasePhiNegativeExpansion) (w : List Bool) : Prop :=
  (∃ a b r, 0 < r ∧ lucasParameter a ∧ lucasParameter b ∧
      occurrenceSet expansion w = sequenceRange (vF a b r)) ∨
    (∃ a b r, 0 < r ∧ lucasParameter a ∧ lucasParameter b ∧
      occurrenceSet expansion w = sequenceRange (vG a b r)) ∨
    (∃ a b r, 0 < r ∧ lucasParameter a ∧ lucasParameter b ∧
      occurrenceSet expansion w = sequenceRange (vH a b r)) ∨
    (∃ (a b : Int) (families : Fin 3 → GapFamily) (first : Fin 3 → Int),
      lucasParameter a ∧ lucasParameter b ∧ (∀ i, 0 < first i) ∧
      occurrenceSet expansion w =
        ⋃ i, sequenceRange (vForFamily (families i) a b (first i)))

theorem admissible_negative_prefix_iff_canonical (expansion : BasePhiNegativeExpansion)
    (w : List Bool) :
    AdmissibleNegativePrefix expansion w ↔
      AdmissibleNegativePrefix canonicalExpansion w := by
  rw [admissible_negative_prefix_iff_occurrence_set_nonempty,
    admissible_negative_prefix_iff_occurrence_set_nonempty,
    occurrenceSet_eq_canonical]

theorem trident_witness_iff_canonical (expansion : BasePhiNegativeExpansion)
    (w : List Bool) :
    TridentWitness expansion w ↔ TridentWitness canonicalExpansion w := by
  simp only [TridentWitness, occurrenceSet_eq_canonical]

theorem trident_classification_reduces_to_canonical (expansion : BasePhiNegativeExpansion) :
    (∀ w : List Bool,
      AdmissibleNegativePrefix expansion w → TridentWitness expansion w) ↔
      (∀ w : List Bool,
        AdmissibleNegativePrefix canonicalExpansion w → TridentWitness canonicalExpansion w) := by
  constructor
  · intro h w hw
    exact (trident_witness_iff_canonical expansion w).mp
      (h w ((admissible_negative_prefix_iff_canonical expansion w).mpr hw))
  · intro h w hw
    exact (trident_witness_iff_canonical expansion w).mpr
      (h w ((admissible_negative_prefix_iff_canonical expansion w).mp hw))

def SameNegativeTail (M N : Nat) : Prop :=
  ∀ i : Nat, negativeDigit canonicalExpansion M i = negativeDigit canonicalExpansion N i

def negativeTailFiber (N : Nat) : Set Nat :=
  {M | 0 < M ∧ SameNegativeTail M N}

def fiberStart (q : Nat) : Prop :=
  q ∈ negativeTailFiber q ∧ ∀ M ∈ negativeTailFiber q, q ≤ M

def Core (w : List Bool) : Set Nat :=
  {q | fiberStart q ∧ NegativePrefixOccurs canonicalExpansion w q}

def prefixMultiplicity (w : List Bool) : Nat :=
  if w.head? = some true then 1 else 3

def LucasPair (a b : Int) : Prop :=
  ∃ k : Nat, 2 ≤ k ∧ a = goldenLucas (k + 1) ∧ b = goldenLucas k

def CoreLucasWitness (w : List Bool) : Prop :=
  ∃ (family : GapFamily) (a b r : Int),
    LucasPair a b ∧ 0 < r ∧
      Core w = sequenceRange (vForFamily family a b r)

inductive FrontierPhase where
  | F0o
  | F1o
  | F0e
  | G1e
  | G0o
  | H0e
  deriving DecidableEq

def frontierFamily : FrontierPhase → GapFamily
  | .F0o | .F1o | .F0e => .F
  | .G1e | .G0o => .G
  | .H0e => .H

structure FrontierReturnWord where
  phase : FrontierPhase
  a : Int
  b : Int
  first : Int
  enumerate : Nat → Nat
  gap : Nat → Int

def FrontierReturnWordFor (w : List Bool) (certificate : FrontierReturnWord) : Prop :=
  Set.range certificate.enumerate = Core w ∧
    (∀ n : Nat,
      (certificate.enumerate (n + 1) : Int) =
        certificate.enumerate n + certificate.gap n)

def FrontierGapPhase (certificate : FrontierReturnWord) : Prop :=
  ∀ n : Nat,
    certificate.gap n =
      if familyLetter (frontierFamily certificate.phase) n then
        certificate.a
      else
        certificate.b

def negative_tail_fiber_shape (N : Nat) (hN : 0 < N) : Prop :=
    (negativeDigit canonicalExpansion N 0 = true →
      negativeTailFiber N = ({N} : Set Nat)) ∧
    (negativeDigit canonicalExpansion N 0 = false →
      ∃! q : Nat, q ≤ N ∧ N ≤ q + 2 ∧
        negativeTailFiber N = {M | M = q ∨ M = q + 1 ∨ M = q + 2})

def core_occurrence_unique_lift {w : List Bool} (hw : w ≠ []) : Prop :=
    ∀ N ∈ occurrenceSet canonicalExpansion w,
      ∃! qj : Nat × Nat,
        qj.1 ∈ Core w ∧ qj.2 < prefixMultiplicity w ∧ N = qj.1 + qj.2

def prefix_cylinder_to_frontier_return_word {w : List Bool} (hw : w ≠ [])
    (hadmissible : AdmissibleNegativePrefix canonicalExpansion w) :
    Prop :=
  ∃ certificate : FrontierReturnWord,
    FrontierReturnWordFor w certificate

def frontier_return_word_lucas_phase {w : List Bool}
    {certificate : FrontierReturnWord}
    (hcertificate : FrontierReturnWordFor w certificate) :
    Prop :=
  LucasPair certificate.a certificate.b ∧
    0 < certificate.first ∧ FrontierGapPhase certificate

def frontier_return_word_to_core_lucas_family {w : List Bool}
    {certificate : FrontierReturnWord}
    (hcertificate : FrontierReturnWordFor w certificate)
    (hphase : LucasPair certificate.a certificate.b ∧
      0 < certificate.first ∧ FrontierGapPhase certificate) :
    Prop :=
    Core w = sequenceRange
      (vForFamily (frontierFamily certificate.phase)
        certificate.a certificate.b certificate.first)

def canonical_prefix_frontier_classification {w : List Bool} (hw : w ≠ [])
    (hadmissible : AdmissibleNegativePrefix canonicalExpansion w) :
    Prop :=
  CoreLucasWitness w

def occurrenceSet_lucas_gap_classification {w : List Bool} (hw : w ≠ [])
    (hadmissible : AdmissibleNegativePrefix canonicalExpansion w) :
    Prop :=
  ∃ (family : GapFamily) (a b r : Int),
      LucasPair a b ∧ 0 < r ∧
      if w.head? = some true then
        occurrenceSet canonicalExpansion w =
          sequenceRange (vForFamily family a b r)
      else
        occurrenceSet canonicalExpansion w =
          ⋃ j : Fin 3,
            sequenceRange (vForFamily family a b (r + (j.1 : Int)))

/-!
The source question asks for an exact classification of occurrence sequences
for finite negative-position prefix cylinders in the two-sided base-phi
expansion. The regular `BasePhiNegative` module owns the integer-pair value
equation, non-adjacent digits, and the paper's `F`, `G`, and `H` gap families.
The finite scan is evidence for this classification, not its proof.

## Existing interface status

The canonical module now closes the two-sided existence/uniqueness bridge, and
the carry module closes the deterministic carry/skip, raw-value, and
Zeckendorf membership interfaces. This file exposes the resulting reduction:
every `BasePhiNegativeExpansion` has the same digit function as the chosen
canonical expansion, so its occurrence sets can be compared without carrying a
choice of representation through the classification proof.

The declarations in `BasePhiNegative` retain their exact scope.
`admissible_negative_prefix_iff_occurrence_set_nonempty` is an `rfl` interface
between two definitions. The three `vF_succ`/`vG_succ`/`vH_succ` lemmas are
definitional recurrence interfaces. The two `single_digit_*` lemmas are only
the depth-one Bool partition and disjointness theorem; they do not identify an
occurrence set with an `F`, `G`, or `H` formula. The remaining classification
obligation is the missing return-word/first-negative-digit theorem connecting
the canonical carry orbit to those three families.

## Executable obstruction targets

1. Construct the canonical two-sided expansion and prove uniqueness. **Closed
   in `BasePhiCanonicalExpansion`.** Finite
   support is carried by `Int →₀ Nat`; the statement exposes the binary,
   non-adjacency, and exact-value invariants rather than hiding them in a choice:

```lean
theorem basePhiExpansion_existsUnique :
    ∀ N : Nat, ∃! digits : Int →₀ Nat,
      (∀ i : Int, digits i ≤ 1) ∧
      (∀ i : Int, digits i = 1 → digits (i + 1) = 0) ∧
      basePhiValue digits = (N : D5.S0.Carrier.GoldenInt)
```

2. Classify a complete negative-tail fiber as either a singleton or three
   consecutive positive inputs. **Open semantic target, executable as
   `negative_tail_fiber_shape`.** This is a carry/skip boundary-state theorem;
   it does not require a Beatty formula for the first negative digit.

```lean
theorem negative_tail_fiber_shape (N : Nat) (hN : 0 < N) :
    (negativeDigit canonicalExpansion N 0 = true →
      negativeTailFiber N = ({N} : Set Nat)) ∧
    (negativeDigit canonicalExpansion N 0 = false →
      ∃! q : Nat, q ≤ N ∧ N ≤ q + 2 ∧
        negativeTailFiber N = {M | M = q ∨ M = q + 1 ∨ M = q + 2})
```

3. Enumerate the starts of those fibers by the finite frontier quotient and
   classify its gap stream by one shared adjacent Lucas pair. **Open connector,
   split into `prefix_cylinder_to_frontier_return_word`,
   `frontier_return_word_lucas_phase`, and
   `frontier_return_word_to_core_lucas_family`.** The explicit
   `FrontierReturnWord` certificate targets `Core w`, not target-integer
   successor arithmetic.

```lean
theorem prefix_cylinder_to_frontier_return_word {w : List Bool} (hw : w ≠ [])
    (hadmissible : AdmissibleNegativePrefix canonicalExpansion w) :
    ∃ certificate : FrontierReturnWord,
      FrontierReturnWordFor w certificate

theorem frontier_return_word_lucas_phase {w : List Bool}
    {certificate : FrontierReturnWord}
    (hcertificate : FrontierReturnWordFor w certificate) :
    LucasPair certificate.a certificate.b ∧
      0 < certificate.first ∧ FrontierGapPhase certificate

theorem frontier_return_word_to_core_lucas_family {w : List Bool}
    {certificate : FrontierReturnWord}
    (hcertificate : FrontierReturnWordFor w certificate)
    (hphase : LucasPair certificate.a certificate.b ∧
      0 < certificate.first ∧ FrontierGapPhase certificate) :
    Core w = sequenceRange
      (vForFamily (frontierFamily certificate.phase)
        certificate.a certificate.b certificate.first)
```

4. Lift the unique core representative back to one arm or three disjoint
   translates sharing the same family and Lucas pair. **Open end-to-end target,
   executable as `core_occurrence_unique_lift` and
   `occurrenceSet_lucas_gap_classification`.** These declarations make the full
   route to `TridentWitness` type-checkable; none is reported as proved here.

Assault checkpoint (2026-08-21): the canonical two-sided
existence/uniqueness bridge and the carry transducer's structural lemmas are
closed. The complete-fiber shape, core frontier classification, unique lift,
and final shared-family classification now have executable Lean signatures and
remain open. The finite scan is still evidence only; no theorem claim is
promoted by this checkpoint.
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

end

end D5.X_Frontier.BasePhiNegativePrefixTrident
