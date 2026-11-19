# Normal transversals and equal-cardinality conjugacy lifts

## Abstract

The actual quotient conjugacy-class criterion for perfect subgroup codes.

**Theorem 1.1 (Every quotient class lifts without collapsing conjugates).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/NormalQuotientClassCriterion.nlt_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/NormalQuotientClassCriterion.nlt_iff` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

For every normal subgroup H of every finite group G, a normal left transversal exists if and only if each actual element of G/H has a lift t whose full conjugacy class has the same cardinality as its quotient class. The projection from conjugates of t onto conjugates of its image is always surjective. Equality of their finite cardinalities makes it bijective. Choosing one lift for each quotient conjugacy class and taking its entire conjugacy class gives an actual conjugation-invariant transversal, with existence and uniqueness in every coset. The forward direction uses the actual specified normal transversal. Neither a count bound alone nor an order-specific group classification is substituted.

**Theorem 1.2 (The unaffected perfect-code criterion).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/NormalQuotientClassCriterion.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/NormalQuotientClassCriterion.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

A normal subgroup H of a finite group is a perfect code of some normal-connection-set loopless Cayley sum graph exactly when every x outside H has h in H such that the conjugacy class of xH in G/H and the conjugacy class of xh in G have equal cardinality. The graph may depend on H. The identity quotient class is handled separately by its identity lift; no coset or trivial subgroup is discarded. This is the perfect-code second part of antecedent Theorem 2.9, attributed as unaffected by the correction's missing total case. The proof uses the actual normalized perfect-code/NLT equivalence. It does not certify the antecedent's unrelated CFSG lemmas or assert total-code inheritance in quotients.

## References

- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/NormalQuotientClassCriterion.nlt_iff`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/NormalQuotientClassCriterion.result`
- Dependency: [D5/S3/Combinatorics/CayleySumCodes/PerfectCodeTransversal](PerfectCodeTransversal.md)
