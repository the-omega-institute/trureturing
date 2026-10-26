# Actual Cover Monodromy

## Abstract

Coordinate monodromy of actual native charged coefficients

D has arbitrary finite rank, integral symmetric even-diagonal Gram matrix; hu:IsUnit D.G.det. Charges a are unrestricted and e ranges over all integers. States lie in the full native oscillator polynomial algebra tensor the actual quotient ground module selected from actual_twisted_ground_representation D hu. There is no occupation cutoff or positivity assumption.

**Theorem 1.1 (Native coefficient identity).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockChargedMonodromy.charged_coefficient_coordinate_monodromy`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedMonodromy.charged_coefficient_coordinate_monodromy` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Exactly chargedCoefficient D hu (-a) e=(-1)^e smul chargedCoefficient D hu a e, as endomorphisms of ActualTensor D hu. The odd logarithm changes sign under x -> -x; native creation coefficients acquire (-1)^degree, and finite translation coefficients acquire the same odd-frequency substitution sign. The norm q_a is even and q_(-a)=q_a, so the product of term signs is (-1)^e and the scalar 2^(-q_a) is unchanged.

Native K_eq_kernel and mod-two reduction identify the quotient lifts of -a and a, hence U_(-a)=U_a. No replacement of U_(-a) by U_a inverse is made: the square of U_a retains the half-norm sign of the actual representation. This is coordinate monodromy for z=x^2, not an all-state twisted Jacobi or reconstruction theorem. Classical provenance, zero novelty claim. Full moonshine, orbifold, fusion, string and AdS/CFT realization remain open.

**Theorem 1.2 (Ground reflection in the actual quotient).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockChargedMonodromy.ground_neg`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedMonodromy.ground_neg` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The actual ground-action endomorphisms for a and -a are equal because their mod-two quotient lifts agree.

**Theorem 1.3 (Norm reflection).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockChargedMonodromy.norm_neg`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedMonodromy.norm_neg` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The integral lattice norm is unchanged under charge negation.

**Theorem 1.4 (Even lattice norm).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockChargedMonodromy.norm_even`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedMonodromy.norm_even` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Every integral charge has even norm for the given symmetric even-diagonal Gram matrix.

**Theorem 1.5 (Creation coefficient reflection).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockChargedMonodromy.creation_neg`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedMonodromy.creation_neg` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every signed creation degree e, charge negation multiplies its oscillator coefficient by (-1)^e. Negative degrees remain zero. These identities give the exact coordinate characters used in the reflected charged residue kernels.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedMonodromy.charged_coefficient_coordinate_monodromy`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedMonodromy.creation_neg`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedMonodromy.ground_neg`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedMonodromy.norm_even`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedMonodromy.norm_neg`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients](LatticeHalfFockChargedTensorCoefficients.md)
