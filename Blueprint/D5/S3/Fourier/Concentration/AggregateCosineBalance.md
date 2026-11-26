# Failure of a shared cosine cutoff

## Abstract

One cutoff can separate the first two real cosine moments on every cycle of size at least seven.

For a modulus q, use the residues k from 0 to q−1. Let c(k) = cos(2πk/q) and d(k) = cos(4πk/q). All sums run over these residues.

**Theorem 1.1 (The signed squared readout and the zero cutoff).**

$$\begin{aligned}&\forall q \in \mathbb{N},\quad q \ge 7:\\&\sum_{k}(\operatorname{c}\left(k\right)-\operatorname{d}\left(k\right))(\operatorname{c}\left(k\right)+\operatorname{d}\left(k\right))^{2}=\frac{q}{4},\\&0<\sum_{k}(\operatorname{c}\left(k\right)-\operatorname{d}\left(k\right))\operatorname{max}\left(0, \operatorname{c}\left(k\right)+\operatorname{d}\left(k\right)\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/AggregateCosineBalance.aggregate_cosine_imbalance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Fourier expansion of (c−d)(c+d)² has frequencies between −6 and 6. The only constant contribution comes from c²d, where the terms 1+1−2 and −1−1+2 each contribute 1/8. Every nonconstant term sums to zero by character orthogonality when q ≥ 7.

The double-angle identity gives c+d = (2c−1)(c+1) and c−d = (1−c)(2c+1). A residue with c+d > 0 has c > 1/2, so every term in the clipped sum is nonnegative. At k=1 the angle lies strictly between zero and π/3, which makes this term positive.

Normalizing the positive part of c+d gives a probability weight because its value at k=0 is two. The clipped sum then shows that the first moment is strictly larger than the second.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/AggregateCosineBalance.aggregate_cosine_imbalance`
