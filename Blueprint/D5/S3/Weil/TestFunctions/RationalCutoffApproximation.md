# Rational Polynomial Tests with a Fixed Cutoff

## Abstract

Every even smooth compactly supported complex test can be approximated by two rational polynomials under a fixed smooth plateau. The approximation controls both the physical zeroth and second L1 derivatives and the complete paired Weil square sum.

All physical integrals below use Lebesgue measure on the real line. D denotes the physical derivative, P(p,x) is the real evaluation of a rational polynomial, S(p,x)=(P(p,x)+P(p,-x))/2, and I is the imaginary unit. A WeilTestFunction is even, smooth of every finite order, complex valued, and compactly supported.

**Theorem 1.1 (Simultaneous rational approximation of three jets).**

$$\forall f \in \mathbb{R} \to \mathbb{R}, B \in \mathbb{R}, e \in \mathbb{R},\; \left(\left(\operatorname{ContDiff}\left(\mathbb{R}, \infty, f\right) \land 0 < B\right) \land 0 < e\right) \Rightarrow \left(\exists p \in \operatorname{Polynomial}\left(\mathbb{Q}\right),\; \forall x \in \operatorname{Icc}\left(-B, B\right),\; \left(\left\lVert f\left(x\right) - \operatorname{P}\left(p, x\right) \right\rVert \le e \land \left\lVert \operatorname{D}\left(f\right)\left(x\right) - \operatorname{P}\left(\operatorname{derivative}\left(p\right), x\right) \right\rVert \le e\right) \land \left\lVert \operatorname{D}\left(\operatorname{D}\left(f\right)\right)\left(x\right) - \operatorname{P}\left(\operatorname{derivative}\left(\operatorname{derivative}\left(p\right)\right), x\right) \right\rVert \le e\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/RationalCutoffApproximation.exists_rational_two_jet` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply real Weierstrass approximation to the continuous second derivative. Approximate its finitely many polynomial coefficients by rational numbers, with an error that bounds their weighted sum on the whole interval. Integrate the rational polynomial twice, choosing zero constants, then add rational approximations to f(0) and Df(0). The mean value inequality bounds both accumulated integration errors.

**Definition 1.2 (Even rational polynomial pair).**

$$\forall p \in \operatorname{Polynomial}\left(\mathbb{Q}\right), q \in \operatorname{Polynomial}\left(\mathbb{Q}\right), x \in \mathbb{R},\; \operatorname{rationalEvenPolynomial}\left(p, q, x\right) = \operatorname{S}\left(p, x\right) + I \cdot \operatorname{S}\left(q, x\right)$$

*Formalization.* `D5/S3/Weil/TestFunctions/RationalCutoffApproximation.rationalEvenPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real and imaginary components use independently chosen rational polynomials. Reflection averaging makes their combination even.

**Definition 1.3 (A fixed smooth plateau).**

$$\forall R \in \mathbb{N}, p \in \operatorname{Polynomial}\left(\mathbb{Q}\right), q \in \operatorname{Polynomial}\left(\mathbb{Q}\right), x \in \mathbb{R},\; 0 < R \Rightarrow \operatorname{H}\left(R, p, q\right)\left(x\right) = \operatorname{chi}\left(R, x\right) \cdot \operatorname{rationalEvenPolynomial}\left(p, q, x\right)$$

*Formalization.* `D5/S3/Weil/TestFunctions/RationalCutoffApproximation.rationalCutoffTest` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a positive natural R, chi(R) is radiusBump(2R), with inner radius R and outer radius 2R. It equals one on [-R,R], vanishes outside [-2R,2R], takes values between zero and one, and is even and smooth. H(R,p,q) is the resulting Weil test. The radius is fixed before the polynomials are chosen.

Write J(f)=integral |f| + integral |D(Df)|. For actual zero data Z, write W(Z,f) for zeroSum of the convolution square of f, with its canonical symmetric convergence proof. Equivalently it is the absolutely convergent sum over all distinct nontrivial zeros of m(n) times F(f,gamma(n)) times conj(F(f,conj(gamma(n)))); F uses the kernel exp(-i z x). Each m(n) is the actual analytic multiplicity.

**Theorem 1.4 (Density in the physical two-jet seminorm).**

$$\forall g \in WeilTestFunction, R \in \mathbb{N}, e \in \mathbb{R},\; \left(\left(0 < R \land \operatorname{tsupport}\left(g\right) \subseteq \operatorname{Icc}\left(-R, R\right)\right) \land 0 < e\right) \Rightarrow \left(\exists p \in \operatorname{Polynomial}\left(\mathbb{Q}\right), q \in \operatorname{Polynomial}\left(\mathbb{Q}\right),\; \operatorname{tsupport}\left(\operatorname{H}\left(R, p, q\right)\right) \subseteq \operatorname{Icc}\left(-\left(2 \cdot R\right), 2 \cdot R\right) \land \operatorname{J}\left(g - \operatorname{H}\left(R, p, q\right)\right) < e\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/RationalCutoffApproximation.exists_rational_cutoff_two_jet` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Approximate the real and imaginary parts through order two on [-2R,2R], then average each error with its reflection. Multiplication by chi leaves the original supported test unchanged. For the even error a, the second derivative of chi times a is chi'' times a plus twice chi' times a' plus chi times a''. Compactness bounds both derivatives of chi. Integrating the uniform bounds over an interval of length 4R gives J.

**Theorem 1.5 (Approximation of the complete Weil square sum).**

$$\forall Z \in ZeroData, g \in WeilTestFunction, R \in \mathbb{N}, e \in \mathbb{R},\; \left(\left(0 < R \land \operatorname{tsupport}\left(g\right) \subseteq \operatorname{Icc}\left(-R, R\right)\right) \land 0 < e\right) \Rightarrow \left(\exists p \in \operatorname{Polynomial}\left(\mathbb{Q}\right), q \in \operatorname{Polynomial}\left(\mathbb{Q}\right),\; \left(\operatorname{tsupport}\left(\operatorname{H}\left(R, p, q\right)\right) \subseteq \operatorname{Icc}\left(-\left(2 \cdot R\right), 2 \cdot R\right) \land \operatorname{J}\left(g - \operatorname{H}\left(R, p, q\right)\right) < e\right) \land \left\lVert \operatorname{W}\left(Z, g\right) - \operatorname{W}\left(Z, \operatorname{H}\left(R, p, q\right)\right) \right\rVert < e\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/RationalCutoffApproximation.exists_rational_cutoff_approximation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The symmetric spectral ball of radius 6 is finite. The rational fourth-moment tail at T=5 proves summability of its entire complement. Together they give a finite full moment M=sum m(n)/(1+Re(gamma(n))^2)^2.

Let d=g-H. The physical error gives a strip coefficient Cd at most exp(R) times J(d), while Cg is the zeroth-plus-second weighted integral for g. Both transform factors lie in the closed half strip. The difference of their paired products is bounded, after summation, by Cd(2Cg+Cd)M. Choosing the physical tolerance sufficiently small proves the two error inequalities simultaneously.

The conjugate frequency is retained even for zeros away from the critical line. No critical-line hypothesis, interpolation identity for H, or vanishing residual at an exceptional zero is required. The conclusion gives existence of rational coefficients; it supplies neither an effective degree or denominator bound nor a numerical evaluator.

## References

- Truth anchor: `D5/S3/Weil/TestFunctions/RationalCutoffApproximation.exists_rational_cutoff_approximation`
- Truth anchor: `D5/S3/Weil/TestFunctions/RationalCutoffApproximation.exists_rational_cutoff_two_jet`
- Truth anchor: `D5/S3/Weil/TestFunctions/RationalCutoffApproximation.exists_rational_two_jet`
- Truth anchor: `D5/S3/Weil/TestFunctions/RationalCutoffApproximation.rationalCutoffTest`
- Truth anchor: `D5/S3/Weil/TestFunctions/RationalCutoffApproximation.rationalEvenPolynomial`
- Dependency: [D5/S3/Weil/BurnolGram/ExplicitWeilFourthMomentTail](../BurnolGram/ExplicitWeilFourthMomentTail.md)
- Dependency: [D5/S3/Weil/InterpolationJets/QuantitativeEvenSeed](../InterpolationJets/QuantitativeEvenSeed.md)
- Dependency: [D5/S3/Weil/ZetaBridge/OffLineNonrealZeroNegativeWeilSquare](../ZetaBridge/OffLineNonrealZeroNegativeWeilSquare.md)
