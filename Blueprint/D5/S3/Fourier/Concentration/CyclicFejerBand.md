# A cyclic Fejér bound for frequency bands

## Abstract

The overlap of two finite cyclic prefixes gives a positive Fourier weight for the band.

**Theorem 1.1 (Cyclic band mass and the prefix character sum).**

$$\begin{aligned}&\forall q,H,N:\mathbb{N},\quad q>0,\quad H<N,\\&\forall M:\mathbb{Z}/q\mathbb{Z}\to \mathbb{R}_{\ge0},\\&(N-H)\sum_{r \in R_{H}} \operatorname{M}\left(r\right) + H\operatorname{M}\left(0\right) \le \frac{1}{q}\sum_{k \in \mathbb{Z}/q\mathbb{Z}} |\left(B_{N}\right)\left(k\right)|^{2} \Re \widehat{M}\left(k\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/CyclicFejerBand.band_le_positive_fourier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the positive integer q, the band R_H consists of the residues of all integers from -H to H. The function M takes nonnegative real values. The transform uses the negative character. The window B_N(k) is the sum of the positive character at the residues of the first N natural-number indices.

For a band residue represented by an integer z, translate one coordinate of the pairs (j,j), with 0 ≤ j < N-H, by |z|. Use the first coordinate for positive z and the second for negative z. This injects N-H prefix indices into the fibre of ordered pairs with residue difference z. At residue zero, all N pairs (j,j) contribute, giving the extra H M(0). The counts accommodate repeated residues when N exceeds q.

Summing fibrewise bounds the left-hand side by the pair sum. Fourier inversion expands the pair sum. Its two prefix sums are complex conjugates, so their product is the squared norm of B_N(k). Taking the real part preserves the signs of the Fourier contributions.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/CyclicFejerBand.band_le_positive_fourier`
