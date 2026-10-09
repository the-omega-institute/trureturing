# Averaging the two orientation certificates

## Abstract

Complementary unused-edge distributions force a translated fourteen-cycle with at least ten distinguished-port visits.

**Definition 1.1 (Distinguished-port visits).**

Lean statement: `D5/S3/Combinatorics/Graph/ErdosGyarfasGarciaOrientationAveraging.uCount`

*Formalization.* `D5/S3/Combinatorics/Graph/ErdosGyarfasGarciaOrientationAveraging.uCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a fourteen-entry vertex sequence c, an unused-edge sequence e with three possible edge types, a vertex orientation sigma, and a translation h, uCount counts indices i at which sigma(trans(h,c(i))) differs from e(i). These are precisely the visits where the two used cycle edges include the distinguished port.

**Theorem 1.2 (A translate has ten distinguished-port visits).**

Lean statement: `D5/S3/Combinatorics/Graph/ErdosGyarfasGarciaOrientationAveraging.exists_many_u`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ErdosGyarfasGarciaOrientationAveraging.exists_many_u` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V be a nonempty finite type, and suppose h maps to trans(h,v) bijectively for every v. Suppose the two unused-edge sequences have multiplicities (6,4,4) and (2,6,6). For every orientation sigma, there is a translation h at which the first or the second sequence has at least ten distinguished-port visits.

Reindex each fixed-position sum by the translation bijection, then interchange the finite sums. At every oriented vertex, twice the number of distinguished-port visits in the first sequence plus that number in the second sequence is 28, independent of its orientation. Consequently twice the first translated total plus the second translated total is 28 times the size of V. If each translate had at most nine visits in both sequences, the same expression would be at most 27 times the size of V. Nonemptiness gives a contradiction.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/ErdosGyarfasGarciaOrientationAveraging.exists_many_u`
- Truth anchor: `D5/S3/Combinatorics/Graph/ErdosGyarfasGarciaOrientationAveraging.uCount`
