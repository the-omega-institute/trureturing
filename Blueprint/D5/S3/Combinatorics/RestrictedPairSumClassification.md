# Restricted pair sums force a subgroup carrier

## Abstract

Finite nonzero restricted pair sums in an arbitrary abelian group force the
adjoined-zero set to be an additive subgroup carrier once the cardinality is
at least three.

**Theorem 1.1 (Corrected restricted-pair-sum classification).**

Lean statement: `D5/S3/Combinatorics/RestrictedPairSumClassification.restricted_pair_sum_classification`

*Proof.* Machine-checked in Lean as
`D5/S3/Combinatorics/RestrictedPairSumClassification.restricted_pair_sum_classification`.
The proof uses finite translation bijectivity and the additive translation
stabilizer. ∎

*Citation.* Simone Costa; Stefano Della Fiore; Mattia Fontana; Lluís Vena
(2026). *Graham conjecture on small sets in abelian groups*, Theorem 2.4,
arXiv:2603.20961v1.

The source's printed `k >= 2` boundary is corrected here. In `Z/5Z`,
`A={1,4}` is a counterexample at cardinality two: the restricted sum is zero,
but `{0,1,4}` is not closed under diagonal sums. No novelty claim is made.

The contrapositive is a same-`Q` consumer for the original ordering setup:
when `insert 0 A` is not a subgroup, two original labels can be replaced by
their sum, preserving the number of labels, their total, and the unchanged
quotient. The integral basis pullback is literal. A proper covering interval
may contain exactly one member of the expanded adjacent pair, however, so the
split-block expansion across the new internal cut remains unresolved. The
original universal ordering and coefficient-one cover targets are open.

## References

- Truth anchor: `D5/S3/Combinatorics/RestrictedPairSumClassification.restricted_pair_sum_classification`
- Source note: `D5/L/Combinatorics/costa2026smallabelian`
