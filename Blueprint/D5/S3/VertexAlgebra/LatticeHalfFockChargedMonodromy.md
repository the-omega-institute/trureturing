# Actual Cover Monodromy

## Abstract

Coordinate monodromy of actual native charged coefficients

D has arbitrary finite rank, integral symmetric even-diagonal Gram matrix; hu:IsUnit D.G.det. Charges a are unrestricted and e ranges over all integers. States lie in the full native oscillator polynomial algebra tensor the actual quotient ground module selected from actual_twisted_ground_representation D hu. There is no occupation cutoff or positivity assumption.

**Theorem 1.1 (Native coefficient identity).**

$$\operatorname{A}\left(-a, e\right)=\operatorname{smul}\left(\operatorname{zpow}\left(-1, e\right), \operatorname{A}\left(a, e\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedMonodromy.charged_coefficient_coordinate_monodromy` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Exactly chargedCoefficient D hu (-a) e=(-1)^e smul chargedCoefficient D hu a e, as endomorphisms of ActualTensor D hu. The odd logarithm changes sign under x -> -x; native creation coefficients acquire (-1)^degree, and finite translation coefficients acquire the same odd-frequency substitution sign. The norm q_a is even and q_(-a)=q_a, so the product of term signs is (-1)^e and the scalar 2^(-q_a) is unchanged.

Native K_eq_kernel and mod-two reduction identify the quotient lifts of -a and a, hence U_(-a)=U_a. No replacement of U_(-a) by U_a inverse is made: the square of U_a retains the half-norm sign of the actual representation. This is coordinate monodromy for z=x^2, not an all-state twisted Jacobi or reconstruction theorem. Classical provenance, zero novelty claim. Full moonshine, orbifold, fusion, string and AdS/CFT realization remain open.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedMonodromy.charged_coefficient_coordinate_monodromy`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients](LatticeHalfFockChargedTensorCoefficients.md)
