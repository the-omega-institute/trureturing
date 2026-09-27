# Finite Samples Do Not Determine Global Hankel Rank

## Abstract

Finite unary observations, even with a nonzero first Hankel block, do not determine the minimal dimension of a rational linear realization.

**Theorem 1.1 (Identical finite samples with different minimal dimensions).**

Lean statement: `D5/S3/Observer/Hankel/FiniteSampleRankAmbiguity.finite_sample_rank_ambiguity`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/FiniteSampleRankAmbiguity.finite_sample_rank_ambiguity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural number N there are two rational finite-dimensional linear systems whose responses agree on every unary word of length at most N. A unary word is a list over a one-element alphabet, and its response is the scalar Markov map at its length. Both infinite Hankel tail spaces are finite-dimensional.

The systems have state dimensions 1 and N+3. Each dimension is minimal among all finite-dimensional rational linear systems with the same complete response. Both empty-word responses equal 1, so the common one-by-one Hankel block is nonzero, including when N is zero.

Take the constant response 1 and the response 1 plus a unit pulse at length N+1. The first tail space is the constant line. The second is the space spanned by the constant sequence and the pulses at positions 0 through N+1. Its constant direction is a tail after the pulse, and each pulse is the difference between an earlier tail and that constant tail.

The map from a constant coefficient and N+2 pulse coefficients into sequences is injective: evaluation after the last pulse recovers the constant, and evaluation at each pulse position recovers its coefficient. Its range is exactly the second tail space, giving dimension N+3. The canonical realization of each tail space attains its Hankel rank and the universal lower bound on state dimension.

## References

- Truth anchor: `D5/S3/Observer/Hankel/FiniteSampleRankAmbiguity.finite_sample_rank_ambiguity`
- Dependency: [D5/S3/Observer/Hankel/SequenceHankelRealization](SequenceHankelRealization.md)
