# Original lattice discriminant S, Weil and Milgram laws

## Abstract

The literal shifted theta series of every positive even integral lattice transforms by its actual discriminant pairing. Negative Fourier operators on all functions satisfy the phased Weil relations, and the original positive Gaussian fixes the Milgram phase. All natural ranks are included. No fusion, Monster, sewing, CFT, string or AdS realization is asserted.

The three theorem statements are classical: Borcherds, Section 4, Theorem 4.1 and Corollary 4.2. The cited Library note maps the original Gram cokernel to the lattice discriminant and checks the signs and principal branch. His finite S operator is exp(-pi i rank/4) times the unphased S defined here, while his T has the same positive quadratic sign. The repository authors the Lean derivations, including the theta-orbit proof of Milgram; it does not claim authorship of these statements.

**Definition 1.1 (Positive cardinal normalization).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil.rho`

*Formalization.* `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil.rho` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The scalar rho is the complex cast of the positive real square root of the cardinality of the actual Gram cokernel. Positivity of the original real Gram matrix identifies its square with det G and makes rho nonzero.

**Definition 1.2 (Negative Fourier operator).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil.weilS`

*Formalization.* `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil.weilS` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On every complex function f on the original discriminant A, S f at a is rho inverse times the sum over b of exp(-2 pi i B(a,b)) f(b). This is a complex linear endomorphism on the whole function space.

**Definition 1.3 (Positive Fourier inverse).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil.weilSplus`

*Formalization.* `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil.weilSplus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The positive Fourier operator has kernel exp(+2 pi i B(a,b)) divided by rho. It is both a left and a right inverse of the negative operator on every function.

**Definition 1.4 (Original half-norm operator).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil.weilT`

*Formalization.* `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil.weilT` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complex linear operator T multiplies f(a) by exp(2 pi i q(a)), where q is the half norm of the original even integral Gram lattice modulo integers.

**Definition 1.5 (Charge conjugation).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil.chargeConjugation`

*Formalization.* `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil.chargeConjugation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complex linear operator C sends f(a) to f(-a) on every complex function. No evenness assumption is imposed on f.

**Definition 1.6 (Positive normalized Gauss sum).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil.gaussPhase`

*Formalization.* `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil.gaussPhase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the actual finite discriminant, gamma is rho inverse times the sum of exp(+2 pi i q(a)) over every class a. The positive sign is part of this definition.

**Theorem 1.7 (All original shifted sectors under inversion).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil.sector_S`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil.sector_S` (`✓ std3`). ∎

*Citation.* Richard E. Borcherds (1998). *Automorphic forms with singularities on Grassmannians*. DOI: [10.1007/s002220050232](https://doi.org/10.1007/s002220050232).

*Commentary.*

For every original LatticeData D with positive real Gram matrix, every discriminant class a and every tau with positive imaginary part, Theta_a(-1/tau) equals (-i tau) to the principal power rank/2, divided by sqrt(det G), times the sum over c of exp(-2 pi i B(a,c)) Theta_c(tau). Coordinate Poisson summation applies to the literal translated Gaussian. Translation has a positive Fourier phase; integer negation converts the absolutely convergent dual sum to the existing negative inverse coefficient. Compact normal convergence is transported through the translated compact set, including empty sets and rank zero.

**Theorem 1.8 (Full function-space Weil identities).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil.finite_weil_relations`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil.finite_weil_relations` (`✓ std3`). ∎

*Citation.* Richard E. Borcherds (1998). *Automorphic forms with singularities on Grassmannians*. DOI: [10.1007/s002220050232](https://doi.org/10.1007/s002220050232).

*Commentary.*

For every original positive even integral lattice, rho is nonzero and rho squared is the discriminant cardinality. On the whole complex function space, S squared equals C, S to the fourth equals the identity, and both products S Splus and Splus S equal the identity. With composition S after T, (S T) cubed equals gamma C. Character orthogonality and a finite completed-square identity prove these relations independently of theta values. These are phased relations; they do not assert an unphased modular representation or isometry for the supremum norm.

**Theorem 1.9 (Milgram phase of the original positive even lattice).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil.milgram`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil.milgram` (`✓ std3`). ∎

*Citation.* Richard E. Borcherds (1998). *Automorphic forms with singularities on Grassmannians*. DOI: [10.1007/s002220050232](https://doi.org/10.1007/s002220050232).

*Commentary.*

For every natural rank, the positive normalized Gauss sum of the original positive even integral Gram lattice equals exp(pi i rank/4). The actual theta S and T transformations along i, (-1+i)/2, -1+i and i combine with the full-space cubic relation. The principal logs of 1-i and (1-i)/2 add to Log(-i), giving exp(-pi i rank/4) for the product of weight factors. Representative independence identifies the original zero sector at i with a convergent positive real Gaussian sum; its zero-vector term is one, so its real part is at least one. Cancelling this nonzero original theta value fixes the positive phase. No positive-rank, even-rank or diagonal restriction is imposed.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil.chargeConjugation`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil.finite_weil_relations`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil.gaussPhase`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil.milgram`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil.rho`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil.sector_S`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil.weilS`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil.weilSplus`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil.weilT`
- Dependency: [D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta](LatticeDiscriminantTheta.md)
