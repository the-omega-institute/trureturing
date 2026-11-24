# Fourier weight in a short range of cyclic frequencies

## Abstract

Short lifted frequencies incur a quadratic deficit from the spatial majorant.

**Theorem 1.1 (A quadratic deduction from the zero-mode budget).**

$$\begin{aligned}&\sum_{k \in J} \Re \widehat{F}\left(k\right)+\frac{8a}{q^{2}} (\sum_{r \in R} r^{2}) (\sum_{k \in J} k^{2})\\& \le |J| \sum_{x \in \mathbb{Z}/q\mathbb{Z}} \operatorname{F}\left(x\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/CyclicShortTimeWeight.low_fourier_weight_deficit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The modulus q is a positive integer and F is a nonnegative real function on the residue classes. The finite sets R and J contain integers. Reduction modulo q is injective on R. For a nonnegative real a, require F(r mod q) ≥ a for r in R and 2 |rk| ≤ q for every r in R and k in J. The transform uses the negative character. Repeated residues represented in J contribute once for each representative.

Subtract each selected real Fourier coefficient from the zero coefficient. The difference is a sum of F(x) times the character deficit at x. Keep the terms from R. On each pair from R and J, 2 |rk| ≤ q puts the angle in the principal interval. The cosine inequality on that interval bounds its deficit below by 8 r² k² / q². The two sums of squares factor because the bound holds on the full product of the two sets.

If the Fourier coefficients are nonnegative real and F(0)>0, divide by q F(0) to read their masses as a probability distribution. If J also has distinct residues, this bounds its probability mass and hence the weight left for frequencies outside J. These hypotheses apply to the cyclic prefix-pair kernel. An arithmetic bound on the remaining zero harmonics is a separate input.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/CyclicShortTimeWeight.low_fourier_weight_deficit`
