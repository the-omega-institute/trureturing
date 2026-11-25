# Finite recovery of closed collision bands

## Abstract

Positive-part secants bound the closed collision band and recover it exactly on a finite right interval.

Let S be a finite set of indices, x(i) their real frequencies and c(i) their real weights. NonnegativePairs(c) means c(i)c(j)>=0 for every pair in S. ShellFree(r,delta) means every pair distance is at most r or at least r+delta. For real radius r, write E(r) for the sum of c(i)c(j) over ordered pairs in S with absolute frequency difference at most r. Write L(r) for the sum of c(i)c(j) max(0,r-|x(i)-x(j)|) over all ordered pairs.

**Theorem 1.1 (Secants bracket the closed band).**

$$\left(\operatorname{NonnegativePairs}\left(c\right) \land 0 < delta\right) \Rightarrow \left(\operatorname{L}\left(r\right) - \operatorname{L}\left(r - delta\right) \le delta \cdot \operatorname{E}\left(r\right) \land delta \cdot \operatorname{E}\left(r\right) \le \operatorname{L}\left(r + delta\right) - \operatorname{L}\left(r\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/FejerCollisionSecants.collision_ramp_secants` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume c(i)c(j)>=0 for all i,j in S and delta>0. Each pair at distance d<=r contributes exactly delta to the right increment of max(0,r-d), and at most delta to the left increment. A pair at distance d>r contributes zero to the left increment and a nonnegative amount to the right. Multiply by the nonnegative pair weights and sum both inequalities, including pairs on the boundary d=r.

**Theorem 1.2 (Exact right increment for signed data).**

$$\left(\forall delta \in \mathbb{R},\; \left(0 < delta \land \operatorname{ShellFree}\left(r, delta\right)\right) \Rightarrow \operatorname{L}\left(r + delta\right) - \operatorname{L}\left(r\right) = delta \cdot \operatorname{E}\left(r\right)\right) \land \left(\exists deltaZero \in \mathbb{R},\; 0 < deltaZero \land \left(\forall delta \in \mathbb{R},\; \left(0 < delta \land delta \le deltaZero\right) \Rightarrow \operatorname{L}\left(r + delta\right) - \operatorname{L}\left(r\right) = delta \cdot \operatorname{E}\left(r\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/FejerCollisionSecants.collision_ramp_exact_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any delta>0 with no pair distance strictly between r and r+delta, the exact increment equals delta E(r). Take delta0 to be the minimum of 1 and the finite set of positive gaps |x(i)-x(j)|-r for pairs outside the closed band. This minimum is positive even when the outer pair set is empty. For every 0<delta<=delta0, every pair is either already within the closed band or at distance at least r+delta. Its right increment is respectively delta or zero. Sum the exact pair identities. The weights may have either sign and r may be any real number.

For degree-p frequency sums and multinomial weights, put M(r)=r times the whole-line integral of the angular Fejer kernel K_r(t) multiplied by |S(t)|^(2p), for positive r. The exact triangular Fourier identity gives M(r)=L(r), since r max(0,1-|d|/r)=max(0,r-|d|). Thus for nonnegative original weights and 0<delta<r the two secant bounds hold with M in place of L, and for signed weights the right quotient recovers the closed-band collision mass exactly for all sufficiently small positive delta.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/FejerCollisionSecants.collision_ramp_exact_right`
- Truth anchor: `D5/S3/Fourier/Concentration/FejerCollisionSecants.collision_ramp_secants`
- Dependency: [D5/S3/Fourier/Concentration/FejerCollisionVariance](FejerCollisionVariance.md)
