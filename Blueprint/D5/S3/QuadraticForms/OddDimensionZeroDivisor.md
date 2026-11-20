# Zero divisors of bilinear maps

## Abstract

A bilinear map whose target has dimension at most that of its first factor and whose second factor has dimension at least two has a zero divisor, provided every polynomial whose degree is the dimension of the first factor has a root whenever the two dimensions are equal; over the real numbers this holds in every odd dimension.

**Lemma 1.1 (An endomorphism of odd dimension over a real closed field has an eigenvalue).**

$$\forall K \in \operatorname{Type}*, U \in \operatorname{Type}*,\; [\operatorname{Field}\left(K\right)] [\operatorname{IsRealClosed}\left(K\right)] [\operatorname{AddCommGroup}\left(U\right)] [\operatorname{Module}\left(K, U\right)] [\operatorname{FiniteDimensional}\left(K, U\right)] \forall f \in \operatorname{End}\left(K, U\right),\; \operatorname{Odd}\left(\operatorname{finrank}\left(K, U\right)\right) \Rightarrow \left(\exists c \in K,\; \operatorname{HasEigenvalue}\left(f, c\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/OddDimensionZeroDivisor.exists_hasEigenvalue_of_odd_finrank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K be a real closed field and U a finite-dimensional vector space over K of odd dimension. Every linear endomorphism f of U has an eigenvalue c in K, that is, f - c is not injective. In the display End(K, U) is the space of K-linear endomorphisms of U and finrank(K, U) is the dimension of U. The characteristic polynomial of f has degree finrank(K, U), which is odd, and over a real closed field every polynomial of odd degree has a root; a root of the characteristic polynomial is an eigenvalue. The real numbers form a real closed field, so every endomorphism of an odd-dimensional real vector space has a real eigenvalue. In even dimension the statement fails: the rotation of the real plane by a right angle has characteristic polynomial x^2 + 1 and no real eigenvalue. The statement is the classical odd-degree argument; it is used for the eigenvalue of an endomorphism of the three-dimensional space of pure quaternions in the theory of conjugation-invariant bilinear forms.

**Theorem 1.2 (Zero divisors of bilinear maps).**

$$\forall K \in \operatorname{Type}*, U \in \operatorname{Type}*, V \in \operatorname{Type}*, W \in \operatorname{Type}*,\; [\operatorname{Field}\left(K\right)] [\operatorname{AddCommGroup}\left(U\right)] [\operatorname{Module}\left(K, U\right)] [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(K, V\right)] [\operatorname{AddCommGroup}\left(W\right)] [\operatorname{Module}\left(K, W\right)] [\operatorname{FiniteDimensional}\left(K, W\right)] \forall m \in \operatorname{LinearMap}\left(K, U, \operatorname{LinearMap}\left(K, V, W\right)\right),\; \left(\operatorname{finrank}\left(K, W\right) = \operatorname{finrank}\left(K, U\right) \Rightarrow \left(\forall f \in \operatorname{Polynomial}\left(K\right),\; \operatorname{natDegree}\left(f\right) = \operatorname{finrank}\left(K, U\right) \Rightarrow \left(\exists x \in K,\; \operatorname{IsRoot}\left(f, x\right)\right)\right)\right) \Rightarrow \left(\operatorname{finrank}\left(K, W\right) \le \operatorname{finrank}\left(K, U\right) \Rightarrow \left(2 \le \operatorname{finrank}\left(K, V\right) \Rightarrow \left(\exists a \in U,\; \exists b \in V,\; a \ne 0 \land \left(b \ne 0 \land \operatorname{m}\left(a, b\right) = 0\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/OddDimensionZeroDivisor.exists_zero_divisor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K be a field, U, V, W vector spaces over K with W finite-dimensional, and m a K-bilinear map, written as a linear map from U to the linear maps from V to W. Suppose that dim W <= dim U, that dim V >= 2, and that, when dim W = dim U, every polynomial f over K of degree dim U has a root x in K. Then there are a nonzero a in U and a nonzero b in V with m(a, b) = 0. Here dim is finrank over K, which is 0 for an infinite-dimensional space. Proof. If dim U were 0, then dim W = 0 = dim U and the constant polynomial 1, of degree 0, would need a root; so dim U is positive and U is finite-dimensional. Choose linearly independent b and c in V. If the linear map a -> m(a, b) is not injective, a nonzero element of its kernel together with b is a zero divisor. Otherwise it is injective from U to W with dim W <= dim U, hence an isomorphism e, and dim W = dim U. The endomorphism e^(-1) composed with a -> m(a, c) has a characteristic polynomial of degree dim U, which has a root mu by hypothesis; an eigenvector a for mu satisfies m(a, c) = mu m(a, b), so m(a, c - mu b) = 0, and c - mu b is nonzero because b and c are independent. Over the real numbers every polynomial of odd degree has a root, so the conclusion holds whenever dim U is odd; in particular every bilinear multiplication on R^n with n odd and n >= 3 has zero divisors. The case U = V = W = R^3 follows by applying the theorem with the root condition supplied by the odd-degree root theorem of real closed fields; this specialization has been checked against the Lean statement and is not a separate declaration. Over an algebraically closed field the root condition holds in every dimension.

Each hypothesis is needed; none of the following examples is formalized. The root condition: multiplication in the field Q(2^(1/3)), viewed as a bilinear map on Q^3, has no zero divisors, and the polynomial x^3 - 2 of degree 3 has no rational root; multiplication of complex numbers, viewed as a bilinear map on R^2, has no zero divisors, and x^2 + 1 has no real root. In both cases dim W = dim U, which is the only case in which the root condition is required. The bound dim W <= dim U: the tensor product map from R^3 x R^3 to R^3 tensor R^3, a space of dimension 9, has no zero divisors. The bound dim V >= 2: scalar multiplication R^3 x R -> R^3 has no zero divisors. Finite dimension of W: composing the tensor product map with an embedding of R^9 into an infinite-dimensional space W gives finrank W = 0, so the dimension bound holds and the root condition is not required, but there is still no zero divisor. The theorem is an elementary consequence of the classical theory of real division algebras: by a theorem of H. Hopf, a finite-dimensional real division algebra has dimension a power of two, and by the work of Bott, Milnor and Kervaire its dimension is 1, 2, 4 or 8. The odd-dimensional case treated here needs only the eigenvalue argument above.

## References

- Truth anchor: `D5/S3/QuadraticForms/OddDimensionZeroDivisor.exists_hasEigenvalue_of_odd_finrank`
- Truth anchor: `D5/S3/QuadraticForms/OddDimensionZeroDivisor.exists_zero_divisor`
