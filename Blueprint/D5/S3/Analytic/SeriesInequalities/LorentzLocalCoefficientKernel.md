# The Local Lorentz Coefficient Kernel

## Abstract

Inverse central-moment corrections give endpoint-sensitive local coefficient bounds.

The central moment is the Bernstein average of (i-mX) raised to its order. Its inverse convolution defines tau(m,n), with tau(m,0)=1. Write C(D,J,P) for the normalized Bernstein coefficient transform and R(m,p) for max(sqrt(p(1-p)/m),1/m). The polynomial Q(m,r,f) uses the prescribed jet f(n,i), the correction tau(m,n)/m^n, and the degree-m Bernstein basis, summed over n from zero to r and i from zero to m.

**Theorem 1.1 (Both ends of the correction array).**

$$\forall n \in \mathbb{N},\; \exists K \in \mathbb{R},\; 1\le K\land \forall m \in \mathbb{N},\; 0< m\Rightarrow \forall h \in \mathbb{N},\; h\le n\Rightarrow \left\lVert C\left(n, h, \frac{tau\left(m, n\right)}{m^{n}}\right) \right\rVert\le K\cdot min\left(\frac{m^{h}}{m^{n}}, \frac{m^{n-h}}{m^{n}}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/LorentzLocalCoefficientKernel.tau_coefficient_bound` (`✓ std3`). ∎

*Citation.* Olga Holtz; Fedor Nazarov; Yuval Peres (2011). *New Coins from Old, Smoothly*. DOI: [10.1007/s00365-010-9108-5](https://doi.org/10.1007/s00365-010-9108-5). URL: <https://arxiv.org/abs/0808.1936v3>.

*Commentary.*

For each correction order n, one constant controls every positive grid size m and every coefficient h from zero through n. Reflection supplies the symmetric minimum of the two endpoint bounds. This is Corollary 16 of Holtz, Nazarov and Peres in the normalized Bernstein basis; the proof here obtains the coefficient estimate from complex disk bounds for the actual moments.

**Theorem 1.2 (Hypergeometric averaging of the correction).**

$$\forall n \in \mathbb{N},\; \exists K \in \mathbb{R},\; 1\le K\land \forall m \in \mathbb{N},\; \forall D \in \mathbb{N},\; \forall J \in \mathbb{N},\; 0< m\land 0< D\land 2\cdot n\le D\land J\le D\Rightarrow \sum_{h=0}^{n} w\left(D, J, n, h\right)\cdot \left\lVert C\left(n, h, \frac{tau\left(m, n\right)}{m^{n}}\right) \right\rVert\le K\cdot R\left(m, \frac{J}{D}\right)^{n}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/LorentzLocalCoefficientKernel.weighted_tau_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Olga Holtz; Fedor Nazarov; Yuval Peres (2011). *New Coins from Old, Smoothly*. DOI: [10.1007/s00365-010-9108-5](https://doi.org/10.1007/s00365-010-9108-5). URL: <https://arxiv.org/abs/0808.1936v3>.

*Commentary.*

The weight w(D,J,n,h) is choose(n,h) times the falling factorials (J)h and (D-J)(n-h), divided by (D)n. When 2n is at most D, weighting the actual correction array gives the nth power of the endpoint-adapted radius, with a constant depending only on n.

**Theorem 1.3 (Only the effective local jets are needed).**

$$\forall r \in \mathbb{N},\; \exists K \in \mathbb{R},\; 1\le K\land \forall m \in \mathbb{N},\; 0< m\land r\le m\Rightarrow \forall J \in \mathbb{N},\; J\le m+r\Rightarrow \forall A \in \mathbb{R},\; 0\le A\Rightarrow \forall f \in \mathbb{N}\to \mathbb{N}\to \mathbb{C},\; (\forall n \in \mathbb{N},\; n\le r\Rightarrow \forall i \in \mathbb{N},\; i\le m\land i\le J\land J\le i+r\Rightarrow \left\lVert f\left(n, i\right) \right\rVert\le \frac{A}{R\left(m, \frac{J}{m+r}\right)^{n}})\Rightarrow \left\lVert C\left(m+r, J, Q\left(m, r, f\right)\right) \right\rVert\le K\cdot A$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/LorentzLocalCoefficientKernel.local_coefficient_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Olga Holtz; Fedor Nazarov; Yuval Peres (2011). *New Coins from Old, Smoothly*. DOI: [10.1007/s00365-010-9108-5](https://doi.org/10.1007/s00365-010-9108-5). URL: <https://arxiv.org/abs/0808.1936v3>.

*Commentary.*

One constant depending only on r controls all output coefficients, including J=0 and J=m+r. For each derivative order, only grid entries with i at most J and J at most i+r contribute. Arbitrary complex jets satisfying the displayed local bounds are allowed. This coefficient estimate refines the function-based estimates around Lemma 24 of Holtz, Nazarov and Peres. It requires r at most m; the polynomial remainder theorem uses reproduction outside its nonzero regime.

## References

- Truth anchor: `D5/S3/Analytic/SeriesInequalities/LorentzLocalCoefficientKernel.local_coefficient_bound`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/LorentzLocalCoefficientKernel.tau_coefficient_bound`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/LorentzLocalCoefficientKernel.weighted_tau_bound`
- Dependency: [D5/S3/Analytic/SeriesInequalities/LorentzLowDegreeCoefficientRemainder](LorentzLowDegreeCoefficientRemainder.md)
- Dependency: [D5/S3/Observer/BlockStructure/CommonDenominatorPolynomialBasis](../../Observer/BlockStructure/CommonDenominatorPolynomialBasis.md)
