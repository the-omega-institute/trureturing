# From the Recurrence to the Cubic

## Abstract

The Catalan-weighted recurrence implies the cubic equation for the ordinary generating series.

**Theorem 1.1 (The cubic from a Catalan recurrence).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeAlgebra.cubic_of_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeAlgebra.cubic_of_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Let a be a sequence of natural numbers with a at zero equal to one. If each positive term is its predecessor plus the Catalan-weighted sum of coefficients of powers of its generating series, then that series F satisfies 1 + (3x - 2)F + (1 - x)(1 - 2x)F squared + x cubed F cubed = 0.

## References

- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeAlgebra.cubic_of_recurrence`
