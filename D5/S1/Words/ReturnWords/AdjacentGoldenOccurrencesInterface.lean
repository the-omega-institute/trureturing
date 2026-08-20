/- GID: D5/S1/Words/ReturnWords/AdjacentGoldenOccurrencesInterface
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Adjacent golden occurrences are exactly ordered starts with the same golden factor at both endpoints and no equal golden factor strictly between. -/

import Mathlib
import D5.S1.Words.ReturnWords.GoldenReturnWords

/- Provenance: Native proof over pinned mathlib. -/

/-!
SEARCH RECEIPT

The list of inspected candidates is NOT claimed to be exhaustive.

Pinned-mathlib reuse:
* `Mathlib/Data/Bool/Basic.lean:71-77` provides `Bool.decide_iff` and its
  directional wrappers. It characterizes exactly the Boolean equality exposed
  after unfolding `AdjacentGoldenOccurrences`.
* `Mathlib/Data/Finset/Filter.lean:155-169` provides
  `Finset.filter_eq_empty_iff`, `Finset.filter_nonempty_iff`, and
  `Finset.filter_false_of_mem`. The first is useful to consumers that want a
  pointwise absence statement, but using it here would replace rather than
  faithfully publish the requested filtered-finset conjunct.
* The inspected pinned-mathlib candidates did not include a theorem with this
  exact adjacency iff shape; this search is not a proof that no semantically
  equivalent theorem exists.

Pinned-Lean-core reuse:
* `Init/PropLemmas.lean:510-514` provides `decide_eq_true_iff` and
  `decide_eq_decide`; `decide_eq_true_iff` closes the proof after one
  definitional `change`.
* `Init/Prelude.lean:1020-1031` provides the directional family
  `decide_eq_true`, `decide_eq_false`, and `of_decide_eq_true`.
* `Init/SimpLemmas.lean:400-407` provides `decide_eq_true_eq`,
  `decide_eq_false_iff_not`, and related simp lemmas.
* The inspected pinned-core candidates included the unrelated sequence
  implementation `Seq.noAdjacentDuplicates` at
  `Lean/Meta/Tactic/Grind/AC/Seq.lean:208`; no exact occurrence-adjacency
  theorem was identified in those inspected files.

Repository reuse and duplication audit:
* `D5/S1/Words/ReturnWords/GoldenReturnWords.lean:16-26` defines the private
  Boolean implementation, the public proposition, and its `Decidable`
  instance. Its characterization at lines 28-32 is itself private.
* The same private theorem and two-line proof occur at
  `D5/S1/Words/ReturnWords/GoldenGapFirstReturn.lean:14-20`,
  `D5/S1/Words/ReturnWords/GoldenReturnWordsExact.lean:14-20`,
  `D5/S1/Words/ReturnWords/GoldenReturnItinerary.lean:15-21`, and
  `D5/S1/Words/ReturnWords/GoldenOccurrenceGaps.lean:18-24`.
* The other three private copies occur at
  `D5/S1/Words/Powers/GoldenCubePeriods.lean:132-138`,
  `D5/S1/Words/Powers/GoldenCubePeriodsSupport.lean:641-647`, and
  `D5/S1/Words/Palindromes/GoldenRichness.lean:88-94`; the last merely renames
  the factor variable from `w` to `p`.
* A textual search of the repository tree, excluding this interface file, for
  the exact identifiers `AdjacentGoldenOccurrences`,
  `adjacentGoldenOccurrencesBool`, and `adjacent_golden_occurrences_iff` found
  no additional public declaration with this exact iff shape; this does not
  rule out semantically equivalent results under other names. Because private
  declarations in frozen modules are inaccessible to importers, none supplies
  this public interface.

Conclusion:
* Pinned Lean core already proves the generic decide bridge in one step, so no
  local reconstruction of that logic is justified. This file remains useful
  as the missing public interface for the repository-specific private Boolean
  definition and provides a public replacement for seven downstream re-proofs
  without modifying their frozen modules.
-/

namespace D5.S1.Words

/-- Adjacent golden occurrences are exactly equal endpoint factors with no such factor between. -/
theorem adjacent_golden_occurrences_iff {n : Nat} {w : List Bool} {i j : Nat} :
    AdjacentGoldenOccurrences n w i j ↔
      i < j ∧ goldenFactor n i = w ∧ goldenFactor n j = w ∧
        (Finset.Ioo i j).filter (fun k => goldenFactor n k = w) = ∅ := by
  change decide (i < j ∧ goldenFactor n i = w ∧ goldenFactor n j = w ∧
    (Finset.Ioo i j).filter (fun k => goldenFactor n k = w) = ∅) = true ↔ _
  exact decide_eq_true_iff

#print axioms adjacent_golden_occurrences_iff

end D5.S1.Words
