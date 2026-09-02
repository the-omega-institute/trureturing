# Enumeration Invariance of Symmetric Zero Sums

## Abstract

Finite symmetric zero sums, their convergence, and their limiting value do not depend on the duplicate-free exhaustive enumeration of zeta zeros.

**Theorem 1.1 (Finite symmetric zero sums are enumeration invariant).**

$$\forall Z, Z': \operatorname{ZeroData}, g: \operatorname{WeilTestFunction}, T: \mathbb{R}, \operatorname{truncatedZeroSum}(Z, g, T) = \operatorname{truncatedZeroSum}(Z', g, T)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ZeroSumEnumerationInvariance.truncatedZeroSum_enum_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen equivalence from each ZeroData enumeration to the subtype of nontrivial zeta zeros induces a permutation of natural-number indices. It preserves the zero, spectral parameter, multiplicity, symmetric cutoff membership, and summand, so Finset.sum_equiv identifies the two finite sums.

**Theorem 1.2 (Symmetric convergence is enumeration invariant).**

$$\forall Z, Z': \operatorname{ZeroData}, g: \operatorname{WeilTestFunction}, \operatorname{SymmetricConvergent}(Z, g) \iff \operatorname{SymmetricConvergent}(Z', g)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ZeroSumEnumerationInvariance.symmetricConvergent_enum_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each direction transports the same complex limit through the finite-sum enumeration invariance theorem. No summability theorem or new convergence premise is introduced.

**Theorem 1.3 (The symmetric zero-sum value is enumeration invariant).**

$$\forall Z, Z': \operatorname{ZeroData}, g: \operatorname{WeilTestFunction}, h: \operatorname{SymmetricConvergent}(Z, g), h': \operatorname{SymmetricConvergent}(Z', g), \operatorname{zeroSum}(Z, g, h) = \operatorname{zeroSum}(Z', g, h')$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ZeroSumEnumerationInvariance.zeroSum_enum_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen convergence theorem for the second enumeration is rewritten using finite-sum invariance. The frozen uniqueness theorem for the first zero sum then identifies the two limits, including their possibly different convergence witnesses.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/ZeroSumEnumerationInvariance.symmetricConvergent_enum_invariant`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ZeroSumEnumerationInvariance.truncatedZeroSum_enum_invariant`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ZeroSumEnumerationInvariance.zeroSum_enum_invariant`
