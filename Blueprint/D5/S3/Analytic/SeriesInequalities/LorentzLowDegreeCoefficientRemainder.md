# Bernstein Coefficient Tails of Taylor Polynomials

## Abstract

Original Bernstein arrays control the coefficient tails of centered Taylor truncations.

Write B(d,c) for the polynomial with normalized Bernstein coefficients c at degree d, T(P,p,r) for its Taylor polynomial through order r at p, and C(D,J,P) for the degree-D Bernstein coefficient transform. The norm of a finite array is its maximum coefficient modulus. These conventions include both endpoints.

**Theorem 1.1 (A uniform coefficient-tail estimate).**

$$\forall r \in \mathbb{N},\; \exists A \in \mathbb{R},\; \exists K \in \mathbb{R},\; 1\le A\land 1\le K\land \forall d \in \mathbb{N},\; \forall D \in \mathbb{N},\; 0< d\land A\cdot d\le D\Rightarrow \forall c \in Fin\left(d+1\right)\to \mathbb{C},\; \forall J \in \mathbb{N},\; J\le D\Rightarrow \left\lVert C\left(D, J, (B\left(d, c\right)-T\left(B\left(d, c\right), \frac{J}{D}, r\right))\right) \right\rVert\le K\cdot \frac{d}{D}^{\frac{r+1}{2}}\cdot \left\lVert c \right\rVert$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/LorentzLowDegreeCoefficientRemainder.taylor_coefficient_remainder_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Olga Holtz; Fedor Nazarov; Yuval Peres (2011). *New Coins from Old, Smoothly*. DOI: [10.1007/s00365-010-9108-5](https://doi.org/10.1007/s00365-010-9108-5). URL: <https://arxiv.org/abs/0808.1936v3>.

*Commentary.*

For every natural truncation order r, two constants A and K, both at least one, work for every input degree d and output degree D satisfying A d at most D. A complex disk bound obtained from the original coefficients is combined with centered finite-population product moments. Summation of the resulting geometric tail gives exponent (r+1)/2. No derivative bound on the input is assumed.

**Theorem 1.2 (An actual Bernstein representation).**

$$\forall r \in \mathbb{N},\; \exists A \in \mathbb{R},\; \exists K \in \mathbb{R},\; 1\le A\land 1\le K\land \forall d \in \mathbb{N},\; \forall D \in \mathbb{N},\; 0< d\land A\cdot d\le D\Rightarrow \forall c \in Fin\left(d+1\right)\to \mathbb{C},\; \forall J \in \mathbb{N},\; J\le D\Rightarrow \exists a \in Fin\left(D+1\right)\to \mathbb{C},\; B\left(d, c\right)-T\left(B\left(d, c\right), \frac{J}{D}, r\right)=B\left(D, a\right)\land \left\lVert a\left(J\right) \right\rVert\le K\cdot \frac{d}{D}^{\frac{r+1}{2}}\cdot \left\lVert c \right\rVert\land (d\le r\Rightarrow a=0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/LorentzLowDegreeCoefficientRemainder.taylor_coefficient_remainder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Olga Holtz; Fedor Nazarov; Yuval Peres (2011). *New Coins from Old, Smoothly*. DOI: [10.1007/s00365-010-9108-5](https://doi.org/10.1007/s00365-010-9108-5). URL: <https://arxiv.org/abs/0808.1936v3>.

*Commentary.*

At each chosen output index J, the Taylor center is J/D. The corresponding remainder has an actual degree-D coefficient array, whose Jth entry satisfies the uniform estimate. The entire array vanishes when d is at most r. The array can depend on J because its Taylor center does. This statement concerns ordinary Taylor truncation in the large-ratio regime; the Lorentz operator remainder is treated separately.

## References

- Truth anchor: `D5/S3/Analytic/SeriesInequalities/LorentzLowDegreeCoefficientRemainder.taylor_coefficient_remainder`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/LorentzLowDegreeCoefficientRemainder.taylor_coefficient_remainder_bound`
