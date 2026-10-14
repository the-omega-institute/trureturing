# The Low-Degree Lorentz Coefficient Remainder

## Abstract

The actual Lorentz remainder is uniformly small in the original Bernstein coefficient norm.

Write B(d,c) for the polynomial with original normalized degree-d Bernstein array c, and Q(m,r,P) for the Lorentz operator evaluated on the actual iterated derivatives of P at i/m. Its correction polynomials are the inverse convolution of the binomial central moments. Array norms are maximum coefficient moduli, and degree elevation is included in the polynomial identity.

**Theorem 1.1 (Exact polynomial reproduction).**

$$\forall m \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall P \in Polynomial\left(\mathbb{C}\right),\; 0< m\land natDegree\left(P\right)\le r\Rightarrow Q\left(m, r, P\right)=P$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/LorentzCoefficientRemainder.lorentz_reproduction` (`✓ std3`). ∎

*Citation.* Olga Holtz; Fedor Nazarov; Yuval Peres (2011). *New Coins from Old, Smoothly*. DOI: [10.1007/s00365-010-9108-5](https://doi.org/10.1007/s00365-010-9108-5). URL: <https://arxiv.org/abs/0808.1936v3>.

*Commentary.*

Every complex polynomial of degree at most r is reproduced for each positive grid size m. Finite Taylor expansion and the defining convolution identity cancel the nonconstant centered terms. This is the complex-scalar form of Lemma 14 of Holtz, Nazarov and Peres.

**Theorem 1.2 (A uniform bound for every original array).**

$$\forall r \in \mathbb{N},\; \exists K \in \mathbb{R},\; 1\le K\land \forall d \in \mathbb{N},\; \forall m \in \mathbb{N},\; 0< d\land d\le m\Rightarrow \forall c \in Fin\left(d+1\right)\to \mathbb{C},\; \exists a \in Fin\left(m+r+1\right)\to \mathbb{C},\; B\left(d, c\right)-Q\left(m, r, B\left(d, c\right)\right)=B\left(m+r, a\right)\land \left\lVert a \right\rVert\le K\cdot \frac{d}{m}^{\frac{r+1}{2}}\cdot \left\lVert c \right\rVert\land (d\le r\Rightarrow a=0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/LorentzCoefficientRemainder.low_degree_coefficient_remainder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Olga Holtz; Fedor Nazarov; Yuval Peres (2011). *New Coins from Old, Smoothly*. DOI: [10.1007/s00365-010-9108-5](https://doi.org/10.1007/s00365-010-9108-5). URL: <https://arxiv.org/abs/0808.1936v3>.

*Commentary.*

For every natural r, one constant K at least one works simultaneously for all m at least d at least one and every original complex coefficient array c. The remainder is represented at degree m+r by one array a, and the estimate holds for its full maximum norm. If d is at most r, this entire array is zero. No derivative hypothesis, selected input array, or quadratic separation of m from d is imposed.

The proof combines a local Taylor remainder with the effective Lorentz coefficient kernel. The large-ratio regime uses the centered Taylor coefficient estimate; a stability bound handles the complementary regime. Bernstein reconstruction supplies the same coefficient array for all output indices. This establishes the polynomial coefficient remainder and does not assert later smooth-function continuation or probabilistic factory constructions.

## References

- Truth anchor: `D5/S3/Analytic/SeriesInequalities/LorentzCoefficientRemainder.lorentz_reproduction`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/LorentzCoefficientRemainder.low_degree_coefficient_remainder`
- Dependency: [D5/S3/Analytic/SeriesInequalities/LorentzLocalCoefficientKernel](LorentzLocalCoefficientKernel.md)
