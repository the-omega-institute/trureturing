# Conditional Polynomial Rigidity

## Abstract

Conditional closure under partial derivatives forces a polynomial subspace to depend on one linear form.

**Theorem 1.1 (A shared linear form).**

$$\forall K, sigma: Type, \operatorname{Field}\left(K\right), \operatorname{CharZero}\left(K\right), \operatorname{Fintype}\left(sigma\right),\ \forall L: \operatorname{Submodule}\left(K, \operatorname{MvPolynomial}\left(sigma, K\right)\right), \operatorname{FiniteDimensional}\left(K, L\right),\ (\forall a: K, \operatorname{C}\left(a\right) \in L \implies a = 0) \implies\ (\forall p \in L, \operatorname{constantCoeff}\left(p\right) = 0 \implies \forall i \in sigma, \operatorname{pderiv}\left(i, p\right) \in L) \implies\ 2 \leq \operatorname{finrank}\left(K, L\right) \implies\ \exists c: sigma \to K, c \neq 0 \land (\forall p \in L, \exists F: \operatorname{Polynomial}\left(K\right), p = \operatorname{aeval}\left(\sum_{i \in sigma} c(i) \cdot X_{i}, F\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/ConditionalPolynomialRigidity.conditional_derivative_closed_subspace_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K be any field of characteristic zero and sigma any finite type. Let L be a finite-dimensional K-linear subspace of the polynomial ring in variables indexed by sigma. Suppose the only constant polynomial in L is zero, and whenever p belongs to L and its constant coefficient vanishes, every partial derivative of p also belongs to L. If the dimension of L is at least two, there is one nonzero function c from sigma to K such that every p in L equals F(ell) for some univariate polynomial F over K, where ell is the sum of c(i) times X(i). The same c works for all p; F may depend on p.

Evaluation at zero is a linear map from L to the one-dimensional space K. The dimension assumption gives a nonzero element in its kernel. Choose a nonzero p in L of minimum total degree m. Its constant coefficient is nonzero: otherwise conditional closure puts every partial derivative in L, and a nonzero partial has strictly smaller total degree. All partials would therefore vanish. In characteristic zero this makes p constant, and its zero constant coefficient would make p zero.

Choose a nonzero q of least total degree n in the evaluation kernel. Some partial derivative of q is nonzero, so minimality of p gives m less than n. For any r in L of degree less than n, subtract r(0)/p(0) times p. This difference still has degree less than n and has zero evaluation; minimality of q makes it zero. Hence each partial derivative of q equals c(i) times p, with some c(i) nonzero. Commuting mixed partials gives c(j) times partial_i p equals c(i) times partial_j p. Polynomial tangent descent then gives p in K[ell].

Suppose L has an element outside K[ell], and choose one, h, of minimum total degree. Set g equal to h minus h(0)/p(0) times p. Then g lies in L, has zero constant coefficient, remains outside K[ell], and has degree no greater than that of h. Each partial derivative of g lies in L and has smaller degree when nonzero, so each lies in K[ell].

Fix indices i and j. The polynomial c(j) times partial_i g minus c(i) times partial_j g belongs to L by conditional closure. Every partial derivative of this polynomial is zero: commute mixed partials and use tangent descent on each partial of g, which already lies in K[ell]. It is therefore constant, and the exclusion of nonzero constants from L makes it zero. Tangent descent now puts g in K[ell], a contradiction. Thus L is contained in K[ell], and membership in this subalgebra gives the required univariate representation.

Products by elements of K denote scalar actions. Individual coefficients c(i) may vanish, and no order or positivity is assumed. No additional nonemptiness assumption is imposed on sigma. The conclusion is containment in K[ell]; the subspace L need not be an algebra and contains no nonzero constant.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/ConditionalPolynomialRigidity.conditional_derivative_closed_subspace_rigidity`
- Dependency: [D5/S3/Quantum/Algebra/PolynomialTangentDescent](PolynomialTangentDescent.md)
