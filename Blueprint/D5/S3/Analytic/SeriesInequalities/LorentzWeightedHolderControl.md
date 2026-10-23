# Weighted Derivative Kernels and Holder Control

## Abstract

Weighted Bernstein kernels control Lorentz approximation at both endpoints.

Let I=[0,1] and let D(n,p)=max(sqrt(p(1-p)/n),1/n). Write B(n,i,p) for the normalized Bernstein basis polynomial evaluated at p, and Bder(l,n,i,p) for its lth derivative. Write F(j,f,p) for the jth iterated derivative within I. The polynomial Q(m,r,f) is the actual Lorentz jet operator sampled from these derivatives on the degree-m grid. Der(j,V,p) evaluates the jth polynomial derivative of V at p. Qder(j,m,r,f,p) denotes its jth polynomial derivative evaluated at p. The hypothesis H(r,b,f,A) means that f is C^r on I, A is nonnegative, and the modulus of F(r,f,x)-F(r,f,y) is at most A times |x-y|^(b-r) for every x,y in I. All derivatives and norms allow complex values.

**Theorem 1.1 (A positive endpoint scale).**

$$\forall n \in \mathbb{N},\; 0< n\Rightarrow \forall p \in \mathbb{R},\; 0< D\left(n, p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/LorentzWeightedHolderControl.delta_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Olga Holtz; Fedor Nazarov; Yuval Peres (2011). *New Coins from Old, Smoothly*. DOI: [10.1007/s00365-010-9108-5](https://doi.org/10.1007/s00365-010-9108-5). URL: <https://arxiv.org/abs/0808.1936v3>.

*Commentary.*

The reciprocal grid size keeps the scale strictly positive, even at the endpoints.

**Theorem 1.2 (Uniform weighted derivative kernels).**

$$\forall l \in \mathbb{N},\; \forall g \in \mathbb{R},\; 0\le g\Rightarrow \exists K \in \mathbb{R},\; 0< K\land \forall n \in \mathbb{N},\; 0< n\Rightarrow \forall p \in [0,1],\; \sum_{i=0}^{n} \left|\frac{i}{n}-p\right|^{g}\cdot \left|Bder\left(l, n, i, p\right)\right|\le K\cdot D\left(n, p\right)^{g-l}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/LorentzWeightedHolderControl.weighted_derivative_kernel_bound` (`✓ std3`). ∎

*Citation.* Olga Holtz; Fedor Nazarov; Yuval Peres (2011). *New Coins from Old, Smoothly*. DOI: [10.1007/s00365-010-9108-5](https://doi.org/10.1007/s00365-010-9108-5). URL: <https://arxiv.org/abs/0808.1936v3>.

*Commentary.*

This is Lemma 17 of Holtz, Nazarov and Peres. The same constant works for all positive grid degrees and all points of the closed interval. The weight exponent can be any nonnegative real number, and the derivative order can exceed the degree. Centered exponential tilting bounds a complex disk; phase alignment then permits a Cauchy derivative estimate for the entire weighted sum.

**Theorem 1.3 (Simultaneous derivative approximation).**

$$\forall r \in \mathbb{N},\; \forall b \in \mathbb{R},\; r< b\Rightarrow \exists K \in \mathbb{R},\; 0< K\land \forall f \in \mathbb{R}\to \mathbb{C},\; \forall A \in \mathbb{R},\; H\left(r, b, f, A\right)\Rightarrow \forall m \in \mathbb{N},\; 0< m\Rightarrow \forall p \in [0,1],\; (\forall j \in \mathbb{N},\; j\le r\Rightarrow \left\lVert F\left(j, f, p\right)-Qder\left(j, m, r, f, p\right) \right\rVert\le K\cdot A\cdot D\left(m, p\right)^{b-j})\land \left\lVert Qder\left(r+1, m, r, f, p\right) \right\rVert\le K\cdot A\cdot D\left(m, p\right)^{b-(r+1)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/LorentzWeightedHolderControl.holder_derivative_control` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Olga Holtz; Fedor Nazarov; Yuval Peres (2011). *New Coins from Old, Smoothly*. DOI: [10.1007/s00365-010-9108-5](https://doi.org/10.1007/s00365-010-9108-5). URL: <https://arxiv.org/abs/0808.1936v3>.

*Commentary.*

The constant depends only on r and b. Taylor subtraction and exact Lorentz reproduction give every residual derivative through r and the next derivative of the approximating polynomial. This complex-valued seminorm formulation is a deduction from the method of HNP Lemmas 19 and 20, and allows every b>r.

**Theorem 1.4 (Comparison between two endpoint scales).**

$$\forall m \in \mathbb{N},\; 0< m\Rightarrow \forall x \in [0,1],\; \forall y \in [0,1],\; \frac{D\left(m, x\right)}{D\left(m, y\right)}\le 1+\frac{\left|x-y\right|}{D\left(m, x\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/LorentzWeightedHolderControl.inverse_delta_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Olga Holtz; Fedor Nazarov; Yuval Peres (2011). *New Coins from Old, Smoothly*. DOI: [10.1007/s00365-010-9108-5](https://doi.org/10.1007/s00365-010-9108-5). URL: <https://arxiv.org/abs/0808.1936v3>.

*Commentary.*

The scale at one point controls the reciprocal scale at another, with a correction proportional to their separation. Both endpoints remain in the domain.

**Theorem 1.5 (Preservation of the top Holder seminorm).**

$$\forall r \in \mathbb{N},\; \forall b \in \mathbb{R},\; r< b\land b< r+1\Rightarrow \exists L \in \mathbb{R},\; 0< L\land \forall f \in \mathbb{R}\to \mathbb{C},\; \forall A \in \mathbb{R},\; H\left(r, b, f, A\right)\Rightarrow \forall m \in \mathbb{N},\; 0< m\Rightarrow \forall x \in [0,1],\; \forall y \in [0,1],\; \left\lVert Qder\left(r, m, r, f, x\right)-Qder\left(r, m, r, f, y\right) \right\rVert\le L\cdot A\cdot \left|x-y\right|^{b-r}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/LorentzWeightedHolderControl.holder_seminorm_control` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Olga Holtz; Fedor Nazarov; Yuval Peres (2011). *New Coins from Old, Smoothly*. DOI: [10.1007/s00365-010-9108-5](https://doi.org/10.1007/s00365-010-9108-5). URL: <https://arxiv.org/abs/0808.1936v3>.

*Commentary.*

For r<b<r+1, near and distant pairs of points give a bound uniform in the grid degree. This is the seminorm estimate underlying HNP Lemma 21. It does not assert a bound for the complete C^b norm or for lower derivative sup norms.

**Theorem 1.6 (Weighted stability for complex polynomials).**

$$\forall r \in \mathbb{N},\; \forall e \in \mathbb{R},\; 0\le e\land e\le 1\Rightarrow \exists K \in \mathbb{R},\; 0< K\land \forall m \in \mathbb{N},\; 0< m\Rightarrow \forall A \in \mathbb{R},\; 0\le A\Rightarrow \forall V \in \mathbb{C}[X],\; (\forall x \in [0,1],\; \left\lVert Der\left(r+1, V, x\right) \right\rVert\le A\cdot D\left(m, x\right)^{-e})\Rightarrow \forall p \in [0,1],\; \left\lVert Der\left(r+1, L\left(m, r, V\right), p\right) \right\rVert\le K\cdot A\cdot D\left(m, p\right)^{-e}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/LorentzWeightedHolderControl.weighted_lorentz_stability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Olga Holtz; Fedor Nazarov; Yuval Peres (2011). *New Coins from Old, Smoothly*. DOI: [10.1007/s00365-010-9108-5](https://doi.org/10.1007/s00365-010-9108-5). URL: <https://arxiv.org/abs/0808.1936v3>.

*Commentary.*

Here V is an arbitrary complex polynomial and L(m,r,V) is its actual Lorentz operator. A weighted bound for the next derivative passes to L with a uniform constant. This complex-polynomial version follows the argument of HNP Lemma 22; it does not state that lemma for arbitrary functions.

## References

- Truth anchor: `D5/S3/Analytic/SeriesInequalities/LorentzWeightedHolderControl.delta_pos`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/LorentzWeightedHolderControl.holder_derivative_control`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/LorentzWeightedHolderControl.holder_seminorm_control`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/LorentzWeightedHolderControl.inverse_delta_comparison`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/LorentzWeightedHolderControl.weighted_derivative_kernel_bound`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/LorentzWeightedHolderControl.weighted_lorentz_stability`
- Dependency: [D5/S3/Analytic/SeriesInequalities/LorentzCoefficientRemainder](LorentzCoefficientRemainder.md)
