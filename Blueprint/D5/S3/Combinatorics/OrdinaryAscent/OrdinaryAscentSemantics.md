# Ordinary ascent Semantics

## Abstract

Literal ordinary ascent words, actual admissible ranks and the Catalan-pair construction, with its precise carrier and boundary conditions.

**Definition 1.1 (Pattern).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.Pattern`

*Formalization.* `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.Pattern` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

The thirteen reduced patterns 00-0, 00-1, 01-0, 01-1, 01-2, 02-1, 10-0, 10-1, 10-2, 11-0, 12-0, 20-1 and 21-0.

**Definition 1.2 (Fits).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.Fits`

*Formalization.* `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.Fits` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

The literal equalities and strict inequalities defining each of the thirteen patterns on three nonnegative values.

**Definition 1.3 (Contains).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.Contains`

*Formalization.* `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.Contains` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

There exist indices i,i+1,k with i+1<k<length, and the values at those positions fit the indicated literal pattern. The first two positions are adjacent.

**Definition 1.4 (IsAscent).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.IsAscent`

*Formalization.* `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.IsAscent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

At position zero the value is zero. At each later position the value is at most one plus the strict adjacent-ascent count of the preceding prefix. Empty words are included.

**Definition 1.5 (avoiders).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.avoiders`

*Formalization.* `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.avoiders` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

The set of words of the stated length satisfying the ordinary ascent bound and avoiding every pattern in the given finite set.

**Definition 1.6 (Primitive).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.Primitive`

*Formalization.* `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.Primitive` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

Adjacent values are unequal. This imposes no pairwise distinctness of all values.

**Theorem 1.7 (contains append iff).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.contains_append_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.contains_append_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

Appending one letter preserves the old occurrences and creates exactly the occurrences that use the appended value as the third entry of an earlier adjacent pair.

**Theorem 1.8 (ascent take).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.ascent_take`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.ascent_take` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

Every initial segment of an ordinary ascent sequence is an ordinary ascent sequence, including empty and oversize takes.

**Theorem 1.9 (ascent append iff).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.ascent_append_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.ascent_append_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

A one-letter extension is ordinary precisely when the prefix is ordinary and the new letter is zero for an empty prefix, or at most one plus its ascent count otherwise.

**Theorem 1.10 (asc le).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.asc_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.asc_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

The strict adjacent-ascent count is at most length minus one, with natural subtraction handling the empty word.

**Theorem 1.11 (asc append).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.asc_append`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.asc_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

For an empty prefix the new ascent contribution is zero. Otherwise it is one exactly when the previous final value is strictly smaller than the appended letter.

**Theorem 1.12 (entry le asc).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.entry_le_asc`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.entry_le_asc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

Every actual entry of an ordinary ascent sequence is at most its total number of strict adjacent ascents.

**Theorem 1.13 (ascent isInversionSeq).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.ascent_isInversionSeq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.ascent_isInversionSeq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

An ordinary ascent sequence satisfies the existing zero-based inversion-sequence bounds, value at index i at most i. No converse or avoidance transfer is asserted.

**Theorem 1.14 (avoiders finite).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.avoiders_finite`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.avoiders_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

At every finite length and for every finite forbidden-pattern set, the actual ordinary avoiding-word set is finite.

## References

- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.Contains`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.Fits`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.IsAscent`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.Pattern`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.Primitive`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.asc_append`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.asc_le`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.ascent_append_iff`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.ascent_isInversionSeq`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.ascent_take`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.avoiders`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.avoiders_finite`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.contains_append_iff`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.entry_le_asc`
- Dependency: [D5/S3/Combinatorics/InversionSeq/InversionSeqDefs](../InversionSeq/InversionSeqDefs.md)
- Dependency: [D5/S3/Combinatorics/Permutation/WordAscents](../Permutation/WordAscents.md)
