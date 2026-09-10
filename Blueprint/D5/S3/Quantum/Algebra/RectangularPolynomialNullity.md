# Rectangular Polynomial Nullity

## Abstract

Rectangular support bounds the dimension of a polynomial subspace with conditional derivative closure.

**Theorem 1.1 (The rectangular dimension bound).**

$$\forall K, sigma: Type, \operatorname{Field}\left(K\right), \operatorname{CharZero}\left(K\right), \operatorname{Fintype}\left(sigma\right),\ \forall a: sigma \to Nat,\ \forall L: \operatorname{Submodule}\left(K, \operatorname{MvPolynomial}\left(sigma, K\right)\right), \operatorname{FiniteDimensional}\left(K, L\right),\ (\forall b: K, \operatorname{C}\left(b\right) \in L \implies b = 0) \implies\ (\forall p \in L, \operatorname{constantCoeff}\left(p\right) = 0 \implies \forall i \in sigma, \operatorname{pderiv}\left(i, p\right) \in L) \implies\ (\forall p \in L, \forall d \in \operatorname{support}\left(p\right), \forall i \in sigma, d(i) \leq a(i)) \implies\ \operatorname{finrank}\left(K, L\right) \leq \operatorname{FinsetSup}\left(\operatorname{univ}\left(sigma\right), a\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/RectangularPolynomialNullity.stationary_rectangular_nullity_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K be any field of characteristic zero, sigma any finite type, and a a function from sigma to the natural numbers. Let L be a finite-dimensional K-linear subspace of MvPolynomial sigma K. Suppose every constant polynomial C(b) belonging to L has b equal to zero. Suppose also that every partial derivative of a member p of L belongs to L whenever the constant coefficient of p vanishes. Finally, for every p in L, every exponent d in its support, and every i in sigma, assume d(i) is at most a(i). Then the dimension of L is at most Finset.sup univ a. This is the finite supremum of the natural numbers a(i), with value zero for an empty sigma.

If this supremum is zero, all a(i) vanish. Every supported exponent is then zero, so every polynomial in L is constant. The exclusion of nonzero constants gives L equal to the zero subspace. This argument also covers an empty sigma. If the supremum is positive and the dimension of L is less than two, the bound follows directly from the natural-number inequalities.

In the remaining case, conditional polynomial rigidity supplies one nonzero function c from sigma to K such that every member of L is F(ell) for a univariate polynomial F over K, where ell is the sum of c(j) times X(j). Choose i with c(i) nonzero. For each natural number n, the coefficient of the pure monomial X(i) to the power n in F(ell) equals the coefficient of degree n in F times c(i) to the power n. The multinomial coefficient formula and the expansion of polynomial evaluation give this identity.

For nonzero F, its leading coefficient and c(i) are nonzero. Thus the pure monomial of degree F.natDegree occurs in F(ell), and the rectangular support condition bounds F.natDegree by a(i). The zero polynomial satisfies the same natural-degree bound. The coefficient identity also shows that evaluation at ell is injective, by cancelling each nonzero power of c(i).

Take the inverse image S of L under this evaluation map. It is a linear subspace of the univariate polynomials of degree less than a(i) plus one. It is proper: that ambient space contains one, whereas S cannot contain one because evaluation sends one to the forbidden nonzero constant in L. The monomial basis gives the ambient space dimension a(i) plus one, so S has dimension at most a(i). Evaluation restricts to a linear bijection from S to L: injectivity was proved above, and surjectivity is the common-linear-form representation. Hence L has the same dimension as S, bounded by a(i) and therefore by the finite supremum of a.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/RectangularPolynomialNullity.stationary_rectangular_nullity_bound`
- Dependency: [D5/S3/Quantum/Algebra/ConditionalPolynomialRigidity](ConditionalPolynomialRigidity.md)
