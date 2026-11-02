# Approximate Oriented Anchor Repair

## Abstract

Uniform polar isometric repair from finite oriented approximate comparisons.

H and W are complex finite-dimensional inner-product spaces in independent universes; finite dimension supplies completeness. The orthonormal basis a has d entries, with d at least one. W is the same complete all-outcome, shared-reference output used by the actual arbitrary map F. The theorem assumes neither linearity nor unit-sphere surjectivity of F, and no orthogonality of its output anchors. Every norm on a vector is its genuine Hilbert norm; every norm on an operator is the induced operator norm.

**Definition 1.1 (Actual linear basis extension).**

$$\forall H \in FiniteComplexHilbertSpace, W \in FiniteComplexHilbertSpace, d \in Natural, a \in \operatorname{OrthonormalBasis}\left(\operatorname{Fin}\left(d\right), Complex, H\right), F \in \operatorname{Function}\left(H, W\right),\; \operatorname{basisExtension}\left(a, F\right) = \operatorname{continuousLinearBasisExtension}\left(a, \operatorname{compose}\left(F, a\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/ApproximateOrientedAnchorRepair.basisExtension` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This definition is used by the complete repair theorem.

**Definition 1.2 (Coordinate error scale).**

$$\forall d \in Natural, delta \in Real,\; \operatorname{eta}\left(d, delta\right) = \operatorname{sqrt}\left(\frac{d}{2}\right) \cdot delta$$

*Formalization.* `D5/S3/Quantum/Foundation/ApproximateOrientedAnchorRepair.eta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This definition is used by the complete repair theorem.

**Definition 1.3 (Gram perturbation scale).**

$$\forall d \in Natural, delta \in Real,\; \operatorname{kappa}\left(d, delta\right) = \frac{d - 1}{\operatorname{sqrt}\left(2\right)} \cdot delta$$

*Formalization.* `D5/S3/Quantum/Foundation/ApproximateOrientedAnchorRepair.kappa` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This definition is used by the complete repair theorem.

Natural numbers in real formulas are cast to the reals before subtraction or division. In the four-direction formulas, i is the complex imaginary unit and k is coerced from Fin(4) to a natural exponent. The anchors are exactly a(j), i a(j), -a(j), -i a(j). The norm and phase calibration are exact. Only their squared-distance comparisons carry the common additive error delta, uniformly for every unit input and every literal anchor.

**Theorem 1.4 (Uniform finite-anchor polar repair).**

$$\forall H \in FiniteComplexHilbertSpace, W \in FiniteComplexHilbertSpace, d \in Natural, a \in \operatorname{OrthonormalBasis}\left(\operatorname{Fin}\left(d\right), Complex, H\right), F \in \operatorname{Function}\left(H, W\right), delta \in Real,\; \left(1 \le d \land \left(0 \le delta \land \left(\left(\forall x \in H,\; \operatorname{norm}\left(x\right) = 1 \Rightarrow \operatorname{norm}\left(\operatorname{apply}\left(F, x\right)\right) = 1\right) \land \left(\left(\forall j \in \operatorname{Fin}\left(d\right), k \in \operatorname{Fin}\left(4\right),\; \operatorname{apply}\left(F, \operatorname{smul}\left(\operatorname{pow}\left(i, k\right), \operatorname{apply}\left(a, j\right)\right)\right) = \operatorname{smul}\left(\operatorname{pow}\left(i, k\right), \operatorname{apply}\left(F, \operatorname{apply}\left(a, j\right)\right)\right)\right) \land \left(\left(\forall x \in H,\; \operatorname{norm}\left(x\right) = 1 \Rightarrow \left(\forall j \in \operatorname{Fin}\left(d\right), k \in \operatorname{Fin}\left(4\right),\; \operatorname{pow}\left(\operatorname{norm}\left(\operatorname{apply}\left(F, x\right) - \operatorname{apply}\left(F, \operatorname{smul}\left(\operatorname{pow}\left(i, k\right), \operatorname{apply}\left(a, j\right)\right)\right)\right), 2\right) \le \operatorname{pow}\left(\operatorname{norm}\left(x - \operatorname{smul}\left(\operatorname{pow}\left(i, k\right), \operatorname{apply}\left(a, j\right)\right)\right), 2\right) + delta\right)\right) \land \operatorname{kappa}\left(d, delta\right) < 1\right)\right)\right)\right)\right) \Rightarrow \left(\operatorname{IsStrictlyPositive}\left(\operatorname{compose}\left(\operatorname{adjoint}\left(\operatorname{basisExtension}\left(a, F\right)\right), \operatorname{basisExtension}\left(a, F\right)\right)\right) \land \left(\exists U \in \operatorname{ComplexLinearIsometry}\left(H, W\right),\; \operatorname{toContinuousLinearMap}\left(U\right) = \operatorname{compose}\left(\operatorname{basisExtension}\left(a, F\right), \operatorname{ringInverse}\left(\operatorname{positiveSqrt}\left(\operatorname{compose}\left(\operatorname{adjoint}\left(\operatorname{basisExtension}\left(a, F\right)\right), \operatorname{basisExtension}\left(a, F\right)\right)\right)\right)\right) \land \left(\operatorname{norm}\left(\operatorname{compose}\left(\operatorname{adjoint}\left(\operatorname{basisExtension}\left(a, F\right)\right), \operatorname{basisExtension}\left(a, F\right)\right) - \operatorname{identity}\left(H\right)\right) \le \operatorname{kappa}\left(d, delta\right) \land \left(\operatorname{norm}\left(\operatorname{basisExtension}\left(a, F\right) - \operatorname{toContinuousLinearMap}\left(U\right)\right) \le 1 - \operatorname{sqrt}\left(1 - \operatorname{kappa}\left(d, delta\right)\right) \land \left(\forall x \in H,\; \operatorname{norm}\left(x\right) = 1 \Rightarrow \operatorname{norm}\left(\operatorname{apply}\left(F, x\right) - \operatorname{apply}\left(U, x\right)\right) \le \operatorname{min}\left(2, \operatorname{sqrt}\left(\operatorname{kappa}\left(d, delta\right) + 2 \cdot \operatorname{eta}\left(d, delta\right)\right) + 1 - \operatorname{sqrt}\left(1 - \operatorname{kappa}\left(d, delta\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ApproximateOrientedAnchorRepair.finite_oriented_anchor_polar_repair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All the displayed original premises are retained; the conclusion holds for every unit input.

This is V80 Theorem 14.1 with the standing complete-output definitions 2.1 through 3.2 and section 14. IsStrictlyPositive means that the positive Gram operator is invertible; in finite dimension it is positive definite. positiveSqrt is Mathlib CFC.sqrt and ringInverse is its two-sided inverse, so the displayed U is precisely B(B*B)^(-1/2), with the same adjoint and phase conventions. No relation between the dimensions of H and W is assumed in advance. Delta zero and d one remain included.

The proof reconstructs real and imaginary coordinates from the opposite anchors and uses Parseval to obtain norm(B*F(x)-x) <= eta. At basis inputs the Gram diagonal is one and the off-diagonal modulus is at most delta/sqrt(2). Mathlib Gershgorin and continuous functional calculus put the spectrum in [1-kappa,1+kappa], prove positivity, and bound the positive square root. Its inverse produces the stated polar isometry. The norm-square expansion gives norm(F(x)-B(x)) squared <= kappa+2 eta; the triangle inequality and the distance bound two give the literal minimum. Standard spectral, inverse-square-root, Parseval and scalar-root machinery is reused from pinned Mathlib. The new bridge relates actual nonlinear finite comparisons to the uniform repair; it does not assume any of the coordinate, Gram or polar conclusions.

This proves existence of a nearby mathematical representation on the same complete output. It supplies no physical implementation or internal control claim. It makes no sampled-input, arbitrary-amplitude approximate comparison, outcome-projection or sharpness claim.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/ApproximateOrientedAnchorRepair.basisExtension`
- Truth anchor: `D5/S3/Quantum/Foundation/ApproximateOrientedAnchorRepair.eta`
- Truth anchor: `D5/S3/Quantum/Foundation/ApproximateOrientedAnchorRepair.finite_oriented_anchor_polar_repair`
- Truth anchor: `D5/S3/Quantum/Foundation/ApproximateOrientedAnchorRepair.kappa`
