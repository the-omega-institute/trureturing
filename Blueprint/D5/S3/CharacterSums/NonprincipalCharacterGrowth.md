# Cancellation within one period

## Abstract

Half-totient growth of a nonprincipal Dirichlet L-function

For a complex nonprincipal character of positive modulus q, each full period sums to zero. Its total absolute mass is the number of units modulo q. An incomplete period and its complement have opposite sums, so the norm of either sum is at most half that mass.

**Theorem 1.1 (Growth throughout the right half-plane).**

$$\operatorname{abs}\left(\operatorname{L}\left(s, chi\right)\right) \le \operatorname{phi}\left(q\right) \operatorname{abs}\left(s\right)/(2 \operatorname{Re}\left(s\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/NonprincipalCharacterGrowth.nonprincipal_growth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take any complex s with σ = Re(s) > 0. Write A(t) for the character sum over positive integers up to t. Partial summation on σ > 1 identifies L(s,χ) with s times the integral of A(t)t to the power −s−1 from one to infinity. Boundedness of A makes its Mellin integral holomorphic throughout σ > 0, so analytic continuation extends the identity to this half-plane.

The absolute value of the remaining power integrates to 1/σ. Multiplying by |s| and the incomplete-period bound φ(q)/2 gives the stated estimate.

## References

- Truth anchor: `D5/S3/CharacterSums/NonprincipalCharacterGrowth.nonprincipal_growth`
