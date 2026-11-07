# The power-border Delannoy conjecture

## Abstract

The power-border Delannoy diagonal ratio differs from exp(1) times the half-shift by a quantity tending to zero.

**Definition 1.1 (The additive-error power-border limit).**

$$claimPower \Leftrightarrow \operatorname{Filter}.\operatorname{Tendsto}\left((\operatorname{fun} (n:\mathbb{N}) \mapsto \frac{(\operatorname{GrauOllerMarcenVaronaFactorialBorderGrowth}.\operatorname{f}\left((\operatorname{fun} (k:\mathbb{N}) \mapsto k^{k}), n + 1, n + 1\right) : \mathbb{R})}{(\operatorname{GrauOllerMarcenVaronaFactorialBorderGrowth}.\operatorname{f}\left((\operatorname{fun} (k:\mathbb{N}) \mapsto k^{k}), n, n\right) : \mathbb{R})} - \operatorname{Real}.\operatorname{exp}\left(1\right) \cdot ((n : \mathbb{R}) + \frac{1}{2})), \operatorname{Filter}.\operatorname{atTop}, (\mathcal{N}(0))\right)$$

*Formalization.* `D5/S1/Recurrence/GrauOllerMarcenVaronaPowerBorderGrowth.claimPower` (`✓ std3`).

*Citation.* J. M. Grau, A. M. Oller-Marcén and J. L. Varona (2022). *A class of weighted Delannoy numbers*. DOI: [10.48550/arXiv.2501.09726](https://doi.org/10.48550/arXiv.2501.09726). URL: <https://arxiv.org/abs/2501.09726v2>.

*Commentary.*

Section 6, arXiv page 18: "The same phenomenon happens if f_{n,0} = f_{0,n} = n^n, with our conjecture now being f_{n+1,n+1}/f_{n,n} ≈ e · (n + 1/2) [20, OEIS A346385]." The preceding sentence defines a_n ≈ b_n to mean a_n − b_n → 0 when n → ∞. The border is the natural function k ↦ k^k, including 0^0 = 1. Diagonal entries are cast to the reals before division; the half is a real number.

**Theorem 1.2 (The power-border limit holds).**

$$\operatorname{Filter}.\operatorname{Tendsto}\left((\operatorname{fun} (n:\mathbb{N}) \mapsto \frac{(\operatorname{GrauOllerMarcenVaronaFactorialBorderGrowth}.\operatorname{f}\left((\operatorname{fun} (k:\mathbb{N}) \mapsto k^{k}), n + 1, n + 1\right) : \mathbb{R})}{(\operatorname{GrauOllerMarcenVaronaFactorialBorderGrowth}.\operatorname{f}\left((\operatorname{fun} (k:\mathbb{N}) \mapsto k^{k}), n, n\right) : \mathbb{R})} - \operatorname{Real}.\operatorname{exp}\left(1\right) \cdot ((n : \mathbb{R}) + \frac{1}{2})), \operatorname{Filter}.\operatorname{atTop}, (\mathcal{N}(0))\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/GrauOllerMarcenVaronaPowerBorderGrowth.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. M. Grau, A. M. Oller-Marcén and J. L. Varona (2022). *A class of weighted Delannoy numbers*. DOI: [10.48550/arXiv.2501.09726](https://doi.org/10.48550/arXiv.2501.09726). URL: <https://arxiv.org/abs/2501.09726v2>.

*Commentary.*

The scaled border ratio n b(n−1)/b(n) lies between zero and one. The logarithm remainder estimate and differentiability of exp give its first-order limit at exp(−1). Products of consecutive border ratios preserve the first-order expansion under a summable majorant. Dominated convergence in the exact border convolution transfers that expansion to the normalized diagonal. Reciprocal-ratio algebra gives the half-shift, and first-order ratio transfer gives the asserted additive limit. No explicit rate or second-order expansion is asserted.

## References

- Truth anchor: `D5/S1/Recurrence/GrauOllerMarcenVaronaPowerBorderGrowth.claimPower`
- Truth anchor: `D5/S1/Recurrence/GrauOllerMarcenVaronaPowerBorderGrowth.result`
- Dependency: [D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth](GrauOllerMarcenVaronaFactorialBorderGrowth.md)
