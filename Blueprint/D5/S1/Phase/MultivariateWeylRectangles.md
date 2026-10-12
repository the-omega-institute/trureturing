# Polynomial Equidistribution on Unrestricted Rectangles

## Abstract

Polynomial phases cancel over rectangles whose sides grow independently; distinct nonconstant monomials consequently have Haar averages for continuous observables.

For d natural, write B(N) for the tuples n with 0 <= n(i) < N(i), and A(N,f) for their normalized complex average. Let chi(alpha,Q,n) be exp(2 pi I alpha Q(n)), where Q is an integer polynomial in d variables. The average on an empty box is zero; all limit statements concern eventually positive side lengths. In the formulas, BoxAverage is A, polynomialPhase is chi, monomialOrbit(alpha,e,a) is the torus map defined by these shifted monomials, and HaarIntegral is integration against normalized Haar measure. Curve(B,t) has coordinate t^(B^i.val); Fin(d) uses indices zero through d-1.

**Theorem 1.1 (One threshold for all rectangular shapes).**

$$\forall (d:\mathbb{N}), \forall (alpha:\mathbb{R}\setminus\mathbb{Q}), \forall (Q:\operatorname{MvPolynomial}(\operatorname{Fin}(d),\mathbb{Z})), 0<\operatorname{totalDegree}(Q)\implies \forall (epsilon:\mathbb{R}), 0<epsilon\implies \exists (R:\mathbb{N}), 1\leq R\land (\forall (N:\operatorname{Fin}(d)\to \mathbb{N}), (\forall (i:\operatorname{Fin}(d)), R\leq N(i))\implies \left\lVert \operatorname{BoxAverage}(N,\operatorname{polynomialPhase}(alpha,Q)) \right\rVert<epsilon)$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/MultivariateWeylRectangles.polynomial_rectangular_cancellation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yuval Yifrach (2025). *A note on Weyl's equidistribution theorem*. DOI: [10.1007/s00605-025-02057-2](https://doi.org/10.1007/s00605-025-02057-2). URL: <https://doi.org/10.1007/s00605-025-02057-2>.

*Commentary.*

For every irrational real alpha and every integer polynomial Q of positive total degree, each positive epsilon admits an integer R >= 1 such that every box with N(i) >= R has |A(N,chi(alpha,Q))| < epsilon. There is no restriction on the ratios of side lengths.

Choose a coordinate with nonzero derivative of the highest homogeneous part. Distinct translations in this same coordinate have difference of degree exactly deg(Q)-1, with highest part equal to the translation difference times that derivative. Whole-box Cauchy-Schwarz bounds the smoothed average by the real parts of whole-box correlations. Fixing the finite smoothing length first makes all correlation thresholds simultaneous. The boundary error is at most twice the translation length divided by the chosen side length. Strong induction ends at the phase-independent geometric-sum bound for linear polynomials.

This is a formal derivation of the classical Weyl differencing method. No mathematical novelty is asserted. The derivation explicitly treats independently growing rectangles; a theorem stated only for Euclidean balls does not supply this averaging shape.

**Theorem 1.2 (Continuous observables of shifted monomial families).**

$$\forall (d:\mathbb{N}), \forall (K:\operatorname{Type}()), [\operatorname{Fintype}(K)], \forall (alpha:\mathbb{R}\setminus\mathbb{Q}), \forall (e:K\to \operatorname{Finsupp}(\operatorname{Fin}(d),\mathbb{N})), \forall (a:\operatorname{Fin}(d)\to \mathbb{N}), \forall (F:\operatorname{C}(\operatorname{UnitAddTorus}(K),\mathbb{C})), (\operatorname{Injective}(e)\land (\forall (j:K), e(j)\neq 0))\implies \lim_{N\to\infty} \operatorname{BoxAverage}(N,F\circ \operatorname{monomialOrbit}(alpha,e,a))=\operatorname{HaarIntegral}(F)$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/MultivariateWeylRectangles.monomial_rectangular_equidistribution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yuval Yifrach (2025). *A note on Weyl's equidistribution theorem*. DOI: [10.1007/s00605-025-02057-2](https://doi.org/10.1007/s00605-025-02057-2). URL: <https://doi.org/10.1007/s00605-025-02057-2>.

*Commentary.*

Let K be any finite index type and e:K -> (Fin d -> finite-support N) be injective, with every e(j) nonzero. For every fixed a:Fin d -> N, the j-coordinate of x(n) is alpha times the monomial with exponent e(j), evaluated at n+a, modulo one. For every continuous complex F on (R/Z)^K, A(N,F composed with x) tends to its normalized Haar integral as N tends to infinity in the coordinatewise order.

Every nonzero integer character gives a nonconstant integer polynomial: injectivity of e prevents cancellation of its nonzero coefficients. Translation preserves nonconstancy because the opposite translation is its inverse. The preceding cancellation theorem therefore handles all nonzero characters. Fourier density and uniformly bounded averaging operators extend convergence to every continuous observable. No condition requiring the coordinate monomials to occur is needed.

**Theorem 1.3 (A common integer parameter for all input coordinates).**

$$\forall (d:\mathbb{N}), \forall (K:\operatorname{Type}()), [\operatorname{Fintype}(K)], \forall (alpha:\mathbb{R}\setminus\mathbb{Q}), \forall (e:K\to \operatorname{Finsupp}(\operatorname{Fin}(d),\mathbb{N})), \forall (B:\mathbb{N}), \forall (F:\operatorname{C}(\operatorname{UnitAddTorus}(K),\mathbb{C})), (\operatorname{Injective}(e)\land (\forall (j:K), e(j)\neq 0)\land 2\leq B\land (\forall (j:K), \forall (i:\operatorname{Fin}(d)), e(j)(i)<B))\implies \lim_{L\to\infty} \frac{\sum_{t=1}^{L} F(\operatorname{monomialOrbit}(alpha,e,0)(\operatorname{Curve}(B,t)))}{L}=\operatorname{HaarIntegral}(F)$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/MultivariateWeylRectangles.monomial_curve_equidistribution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yuval Yifrach (2025). *A note on Weyl's equidistribution theorem*. DOI: [10.1007/s00605-025-02057-2](https://doi.org/10.1007/s00605-025-02057-2). URL: <https://doi.org/10.1007/s00605-025-02057-2>.

*Commentary.*

For the same irrational alpha and injective nonzero exponent family, let B >= 2 be strictly larger than every exponent digit e(j)(i). Set n(t)(i) = t^(B^i), using i = 0,...,d-1. The averages for t = 1,...,L of every continuous complex observable converge to normalized Haar measure.

The degree assigned to e(j) is the finite sum of e(j)(i) B^i. Uniqueness of fixed-length base-B expansions makes these degrees distinct, and nonzero exponent vectors make them positive. Evaluating every input monomial on n(t) gives exactly t to this encoded degree. The one-dimensional shifted rectangle conclusion then supplies sampling from one instead of zero.

**Theorem 1.4 (Open-set visits beyond every input threshold).**

$$\forall (d:\mathbb{N}), \forall (K:\operatorname{Type}()), [\operatorname{Fintype}(K)], \forall (alpha:\mathbb{R}\setminus\mathbb{Q}), \forall (e:K\to \operatorname{Finsupp}(\operatorname{Fin}(d),\mathbb{N})), \forall (B:\mathbb{N}), \forall (U:\operatorname{Set}(\operatorname{UnitAddTorus}(K))), \forall (T:\mathbb{N}), (0<d\land \operatorname{Injective}(e)\land (\forall (j:K), e(j)\neq 0)\land (\forall (i:\operatorname{Fin}(d)), \exists (j:K), e(j)=\operatorname{single}(i,1))\land (\forall (j:K), \forall (i:\operatorname{Fin}(d)), e(j)(i)<B)\land \operatorname{IsOpen}(U)\land \operatorname{Nonempty}(U))\implies \exists (t:\mathbb{N}), \operatorname{max}(T,1)\leq t\land \operatorname{monomialOrbit}(alpha,e,0)(\operatorname{Curve}(B,t))\in U\land (\forall (i:\operatorname{Fin}(d)), T\leq \operatorname{Curve}(B,t)(i))$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/MultivariateWeylRectangles.monomial_curve_visits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yuval Yifrach (2025). *A note on Weyl's equidistribution theorem*. DOI: [10.1007/s00605-025-02057-2](https://doi.org/10.1007/s00605-025-02057-2). URL: <https://doi.org/10.1007/s00605-025-02057-2>.

*Commentary.*

Assume d > 0 and that every input monomial occurs in the exponent family. A base larger than all digits is then at least two. For every nonempty open U in the torus and every natural T, there is t >= max(T,1) such that x(n(t)) belongs to U and all n(t)(i) >= T.

A nonnegative continuous function supported in U and positive at one point has positive Haar integral. If a tail of the curve avoided U, its Cesaro averages would instead converge to zero, contradicting the preceding limit. Positive integer weights imply t^(B^i) >= t for t >= 1, giving all coordinate bounds at the same visit.

## References

- Truth anchor: `D5/S1/Phase/MultivariateWeylRectangles.monomial_curve_equidistribution`
- Truth anchor: `D5/S1/Phase/MultivariateWeylRectangles.monomial_curve_visits`
- Truth anchor: `D5/S1/Phase/MultivariateWeylRectangles.monomial_rectangular_equidistribution`
- Truth anchor: `D5/S1/Phase/MultivariateWeylRectangles.polynomial_rectangular_cancellation`
- Dependency: [D5/S1/Phase/CharacterAverage](CharacterAverage.md)
