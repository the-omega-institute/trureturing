# Coefficient-Driven Jacobi Characteristic Polynomial

## Abstract

Strict coefficient Hankel data and self-adjoint companion multiplication produce a monic orthogonal basis whose positive Jacobi recurrence has charpoly q.

**Theorem 1.1 (Coefficient data produce a positive Jacobi recurrence with charpoly q).**

$$\begin{aligned}\forall E: \operatorname{RealInnerProductSpace}\left(\right), q: \operatorname{Polynomial}\left(\mathbb{R}\right),\\b: \operatorname{Basis}\left(\operatorname{Fin}\left(\operatorname{natDegree}\left(q\right)\right), \mathbb{R}, E\right), m: \mathbb{N} \to \mathbb{R},\\\operatorname{Monic}\left(q\right) \land \operatorname{HankelInnerProduct}\left(b, m\right) \land \operatorname{StrictPositiveHankel}\left(b, m\right) \land \operatorname{SelfAdjoint}\left(\operatorname{coefficientMultiplication}\left(q, b\right)\right) \Rightarrow\\J = \operatorname{toMatrix}\left(\operatorname{gramSchmidtBasis}\left(b\right), \operatorname{gramSchmidtBasis}\left(b\right), \operatorname{coefficientMultiplication}\left(q, b\right)\right), h(i) = \operatorname{inner}\left(\operatorname{gramSchmidtBasis}\left(b\right)\left(i\right), \operatorname{gramSchmidtBasis}\left(b\right)\left(i\right)\right),\\(\forall i, j \in \operatorname{Fin}\left(\operatorname{natDegree}\left(q\right)\right), i \neq j \Rightarrow \operatorname{inner}\left(\operatorname{gramSchmidtBasis}\left(b\right)\left(i\right), \operatorname{gramSchmidtBasis}\left(b\right)\left(j\right)\right) = 0) \land\\(\forall i \in \operatorname{Fin}\left(\operatorname{natDegree}\left(q\right)\right), \operatorname{repr}\left(b, \operatorname{gramSchmidtBasis}\left(b\right)\left(i\right), i\right) = 1) \land\\(\forall i, j \in \operatorname{Fin}\left(\operatorname{natDegree}\left(q\right)\right), (i + 1 < j \lor j + 1 < i) \Rightarrow J_{i,j} = 0) \land\\(\forall j \in \operatorname{Fin}\left(\operatorname{natDegree}\left(q\right)\right), 0 < j \Rightarrow J_{j,j - 1} = 1 \land J_{j - 1,j} = \frac{h\left(j\right)}{h\left(j - 1\right)} \land 0 < J_{j - 1,j}) \land\\\operatorname{charpoly}\left(J\right) = q.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Moments/CoefficientDrivenJacobiCharacteristicPolynomial.coefficient_driven_jacobi_characteristic_polynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let q be monic and let b be a power basis indexed below its degree. Equip the coefficient space with an inner product represented by a strictly positive finite Hankel form. The multiplication operator is the explicit companion-shaped matrix read from the coefficients of q, and is assumed self-adjoint for this Hankel inner product.

Gram--Schmidt in degree order gives an orthogonal basis p whose leading power-basis coordinate is one. Degree triangularity makes companion multiplication upper Hessenberg, while self-adjointness supplies the reflected zeros, so its matrix J in the p basis is tridiagonal.

For every positive index j, the subdiagonal entry is one and the opposite entry is h(j)/h(j-1), where h is the squared norm. Strict Hankel positivity makes this ratio positive. Finally, change-of-basis invariance reduces the characteristic polynomial to that of the companion matrix; the pinned power-basis theorem identifies it with q.

This declaration stops at the coefficient-driven Jacobi construction. It does not perform Cholesky factorization, construct chain weights, or identify the final chain polynomial.

## References

- Truth anchor: `D5/S3/Constants/Moments/CoefficientDrivenJacobiCharacteristicPolynomial.coefficient_driven_jacobi_characteristic_polynomial`
