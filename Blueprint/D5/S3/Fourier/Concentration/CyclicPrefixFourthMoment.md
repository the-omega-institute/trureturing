# The fourth moment of a cyclic prefix

## Abstract

The exact fourth moment of a cyclic prefix character sum includes the contribution of wrapped differences.

**Theorem 1.1 (Exact fourth moment of the prefix character sum).**

$$\begin{aligned}&\forall q,N:\mathbb{N},\quad q>0,\quad N \le q,\quad m = (2N-q-1)_{+},\\&3\sum_{k \in \mathbb{Z}/q\mathbb{Z}} |\left(B_{N}\right)\left(k\right)|^{4} = q(N(2N^{2}+1)+m(m+1)(m+2)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/CyclicPrefixFourthMoment.sum_prefixCharacter_norm_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write B_N(k) for the character sum at the first N natural-number indices. The residue difference r of an ordered pair has representative 0 ≤ r < q. Its possible integer differences are r and r−q. They occur with counts (N−r)_+ and (N−(q−r))_+, respectively. Positive parts truncate at zero.

The Fourier transform of the pair count is the squared norm of B_N(k). Fourier inversion identifies the sum of its squared norms with q times the sum of squared pair counts. The two individual squares sum to N(2N²+1)/3. Both counts are positive on q−N+1 ≤ r < N, an interval of length m. The cross term there is twice the sum of j(m+1−j) for 1 ≤ j ≤ m, giving the cubic correction after multiplication by three.

For N > 0, dividing by q²N² gives the squared mass of the normalized Fourier weights |B_N(k)|²/(qN). Cauchy–Schwarz then bounds the mass of any exceptional set using its cardinality and that squared mass.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/CyclicPrefixFourthMoment.sum_prefixCharacter_norm_four`
- Dependency: [D5/S3/Fourier/Concentration/CyclicFejerBand](CyclicFejerBand.md)
