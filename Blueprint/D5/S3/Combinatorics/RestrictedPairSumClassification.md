# Restricted pair sums and additive stabilizers

## Abstract

The corrected finite restricted-pair-sum classification for arbitrary abelian groups.

**Theorem 1.1 (At least three nonzero elements force a subgroup carrier).**

Lean statement: `D5/S3/Combinatorics/RestrictedPairSumClassification.restricted_pair_sum_classification`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RestrictedPairSumClassification.restricted_pair_sum_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Simone Costa; Stefano Della Fiore; Mattia Fontana; Lluís Vena (2026). *Graham conjecture on small sets in abelian groups*. DOI: [10.48550/arXiv.2603.20961](https://doi.org/10.48550/arXiv.2603.20961). URL: <https://arxiv.org/html/2603.20961v1>.

*Commentary.*

For a finite A in an arbitrary AddCommGroup with 0 outside A and cardinality at least three, if every sum of distinct elements of A belongs to insert 0 A, then insert 0 A is the carrier of an additive subgroup. The elementary converse is not formalized in this module. The proof is the finite translation and translation-stabilizer argument of Simone Costa, Stefano Della Fiore, Mattia Fontana and Lluís Vena, arXiv:2603.20961v1, Theorem 2.4, with the corrected lower bound k >= 3. The printed k >= 2 boundary is false: A={1,4} in Z/5Z is the C5 counterexample. In the original quotient Q, if insert 0 A is not a subgroup carrier, the contrapositive supplies distinct a,b with a+b outside insert 0 A. Replacing a,b by a+b decreases the cardinality by one and preserves distinctness, nonzeroness, the total and the same original Q. A split interval at the expanded block's internal cut leaves the ordering expansion unresolved. The universal ordering target with the same original M and coefficient one in the original coordinates remains open.

## References

- Truth anchor: `D5/S3/Combinatorics/RestrictedPairSumClassification.restricted_pair_sum_classification`
