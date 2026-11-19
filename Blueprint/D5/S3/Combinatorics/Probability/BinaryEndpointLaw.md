# When independent endpoint choices give a uniform binary image

## Abstract

Uniformity of finite binary images of independent endpoint choices.

**Theorem 1.1 (The fair generators determine uniformity).**

Lean statement: `D5/S3/Combinatorics/Probability/BinaryEndpointLaw.mass_eq_uniform_iff_span`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Probability/BinaryEndpointLaw.mass_eq_uniform_iff_span` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V be a finite vector space over the field with two elements. Choose a vector a(i) in V and a complex number p(i) for each index i in a finite set. Give the choice of a(i) weight p(i) and the choice of zero weight 1-p(i). Multiply these weights across indices. For each v in V, sum the resulting weights of all choices whose vectors add to v.

The resulting function is constant with value 1 divided by the cardinality of V exactly when the vectors a(i) for which p(i)=1/2 span V over the field with two elements. For real parameters in the unit interval this is the law of a sum of independent Bernoulli choices. Empty index sets, deterministic choices and the zero-dimensional space are included.

Each character moment factors into one term per index. A nontrivial character picks up a zero factor exactly when it takes value -1 on a fair generator. If the fair vectors span a proper subspace, a nonzero linear functional vanishing on that subspace supplies a character whose moment stays nonzero. If the fair vectors span V, all nontrivial moments vanish. The finite character basis then identifies the mass function.

## References

- Truth anchor: `D5/S3/Combinatorics/Probability/BinaryEndpointLaw.mass_eq_uniform_iff_span`
