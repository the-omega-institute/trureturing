# Coefficient Multiplication Trace Moments

## Abstract

Coefficient multiplication power traces recover root moments with algebraic multiplicity.

**Theorem 1.1 (Every normalized power trace is the corresponding root moment).**

$$\begin{aligned}\forall q: \operatorname{Polynomial}\left(\mathbb{R}\right), roots: \operatorname{Fin}\left(\operatorname{natDegree}\left(q\right)\right) \to \mathbb{C},\\0 < \operatorname{natDegree}\left(q\right) \land \operatorname{map}\left(ofRealHom, q\right) = \prod_{j \in \operatorname{Fin}\left(\operatorname{natDegree}\left(q\right)\right)} (X - \operatorname{C}\left(roots\left(j\right)\right)) \Rightarrow\\\forall n \in \mathbb{N}, \frac{\operatorname{tr}\left(\operatorname{coefficientMultiplicationMatrix}\left(q\right)^{n}\right)}{\operatorname{natDegree}\left(q\right)} = \operatorname{rootPowerMoment}\left(roots, n\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Moments/CoefficientMultiplicationTraceMoments.coefficient_multiplication_trace_pow_eq_rootPowerMoment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let q be a real polynomial of positive degree d, with a specified factorization into d monic linear factors over the complex numbers. The indexed factors retain algebraic multiplicity. This factorization already forces q to be monic. For every natural exponent, including zero, the real trace of the coefficient multiplication matrix power, divided by d, equals rootPowerMoment for that root list.

Put the roots on the diagonal of a lower bidiagonal matrix T and put ones on its subdiagonal. The Krylov columns T^j e_0 form an upper triangular matrix P with diagonal one. Its determinant is therefore one even when roots repeat or vanish. Cayley-Hamilton supplies the last column of the intertwining identity P S = T P, where S is the complex image of the real coefficient multiplication matrix.

The intertwining identity extends to every power. Invariance of trace under conjugation reduces the trace to T, whose power has diagonal entries equal to the corresponding root powers. Taking real parts and dividing by d connects the coefficient matrix definition to the root moment definition. Distinctness, real roots, positivity and nonzero roots are not required.

## References

- Truth anchor: `D5/S3/Constants/Moments/CoefficientMultiplicationTraceMoments.coefficient_multiplication_trace_pow_eq_rootPowerMoment`
- Dependency: [D5/S0/Observation/PowerTraceCharacteristicPolynomialSaturation](../../../S0/Observation/PowerTraceCharacteristicPolynomialSaturation.md)
- Dependency: [D5/S3/Constants/Moments/CoefficientDrivenJacobiCharacteristicPolynomial](CoefficientDrivenJacobiCharacteristicPolynomial.md)
- Dependency: [D5/S3/Constants/NewtonHankelRealRootCriterion](../NewtonHankelRealRootCriterion.md)
