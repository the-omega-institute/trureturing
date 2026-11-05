# PairedIdealIntersectionObstructions

## Abstract

Actual ideal-intersection graphs and uniform higher-prime Laplacian obstructions.

The public mathematical input is unit-exponent.tex at immutable revision b93becea662a746badeadba42fdc3d3eb3db9382. General endpoint arguments follow the completed mathematical note supplied 2026-11-02. The formal proofs and this exposition are independently authored; no priority claim follows.

**Definition 1.1 (Weighted paired tensor).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionObstructions.tensorK`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionObstructions.tensorK` (`✓ std3`).

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

E_k is diagonal(k+1,1), F_k has rows (1,k) and (1,0), and K_a=(a+1)E_b tensor E_c+a F_b tensor F_c. The coordinate order is empty tail, c tail, b tail, full tail.

**Definition 1.2 (Symmetric representative).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionObstructions.symmetricK`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionObstructions.symmetricK` (`✓ std3`).

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

Replacing F_k by H_k with rows (1,sqrt(k)) and (sqrt(k),0) gives the symmetric representative. The positive diagonal has entries 1,sqrt(c),sqrt(b),sqrt(b)sqrt(c).

**Theorem 1.3 (General strict tensor lower bound).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionObstructions.symmetricK_sub_one_posDef`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionObstructions.symmetricK_sub_one_posDef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For every real a>0 and b,c at least zero, the symmetric representative minus the identity is positive definite. E+H is positive definite because its quadratic form is (sqrt(k)x0+x1) squared+2 x0 squared; E-H is positive semidefinite with form (sqrt(k)x0-x1) squared. The sum EE+HH equals half the sum of their respective two-factor tensor products, so is positive definite. Also EE-I=(E_b-I) tensor E_c+I tensor(E_c-I) is positive semidefinite. Thus K-I=a(EE+HH)+(EE-I) is positive definite. This proves the supporting (a,a,b,c) bound uniformly, with no integer instance enumeration.

**Theorem 1.4 (Nonzero weighted eigenvector transport).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionObstructions.tensor_eigenpair_of_symmetric`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionObstructions.tensor_eigenpair_of_symmetric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The positive diagonal D satisfies D K=S D. Dividing a symmetric eigenvector coordinatewise by its positive diagonal entries preserves nonzero vectors and gives an eigenvector of the original weighted operator with the same eigenvalue.

**Theorem 1.5 (H4 paired eigenvalue in (1,3)).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionObstructions.two_symmetric_low_eigenpair`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionObstructions.two_symmetric_low_eigenpair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The general lower bound gives every paired eigenvalue greater than one. At a=2 the empty/full principal block of S-3I has determinant -4bc. An explicit negative direction, with empty coordinate 2 sqrt(b)sqrt(c) and full coordinate -(3(b+1)(c+1)-1), gives a strict negative quadratic form. The Hermitian spectral expansion yields an eigenvalue below three.

**Theorem 1.6 (Characteristic transport under diagonal geometry).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionObstructions.tensor_symmetric_charpoly`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionObstructions.tensor_symmetric_charpoly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The proved diagonal intertwining has nonzero determinant. The existing Mathlib characteristic-polynomial supplier transports every scalar shift to the symmetric representative. This identity is a binding helper for the general modular spectral argument.

**Theorem 1.7 (Exact scalar-shift determinant transport).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionObstructions.tensor_symmetric_det_shift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionObstructions.tensor_symmetric_det_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

Taking determinants in the proved diagonal intertwining and cancelling the nonzero positive diagonal determinant gives equality of scalar-shift determinants.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionObstructions.symmetricK`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionObstructions.symmetricK_sub_one_posDef`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionObstructions.tensorK`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionObstructions.tensor_eigenpair_of_symmetric`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionObstructions.tensor_symmetric_charpoly`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionObstructions.tensor_symmetric_det_shift`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionObstructions.two_symmetric_low_eigenpair`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/IdealIntersectionObstructions](IdealIntersectionObstructions.md)
- Dependency: [D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionEndpoints](PairedIdealIntersectionEndpoints.md)
