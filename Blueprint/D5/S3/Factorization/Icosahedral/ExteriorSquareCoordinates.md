# Coordinates for the Icosahedral Exterior Square

## Abstract

Explicit centered coordinates transport the A5 action to its real exterior square.

**Definition 1.1 (The alternating group permutes the five coordinates).**

Lean statement: `D5/S3/Factorization/Icosahedral/ExteriorSquareCoordinates.coordinatePermutationRepresentation`

*Formalization.* `D5/S3/Factorization/Icosahedral/ExteriorSquareCoordinates.coordinatePermutationRepresentation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The alternating group acts by inverse coordinate permutation on real five-space, preserving the centered hyperplane.

**Definition 1.2 (Wedge coordinates transport the exterior-square representation).**

Lean statement: `D5/S3/Factorization/Icosahedral/ExteriorSquareCoordinates.exteriorSquareCoordinateEquiv`

*Formalization.* `D5/S3/Factorization/Icosahedral/ExteriorSquareCoordinates.exteriorSquareCoordinateEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An explicit centered basis and its six wedge pairs identify the second exterior power with real six-space equivariantly.

**Definition 1.3 (The Hodge matrix defines a real endomorphism).**

Lean statement: `D5/S3/Factorization/Icosahedral/ExteriorSquareCoordinates.hodgeEndomorphism`

*Formalization.* `D5/S3/Factorization/Icosahedral/ExteriorSquareCoordinates.hodgeEndomorphism` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The repository's existing integral Hodge matrix acts on the transported six-dimensional coordinate space.

**Lemma 1.4 (The transported exterior action is the explicit real matrix action).**

$$rho(g) = mulVecLin(A(g))$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Icosahedral/ExteriorSquareCoordinates.coordinateExteriorSquare_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On every wedge basis vector, the transported A5 action agrees with the real cast of the integral matrix of two-by-two minors.

## References

- Truth anchor: `D5/S3/Factorization/Icosahedral/ExteriorSquareCoordinates.coordinateExteriorSquare_apply`
- Truth anchor: `D5/S3/Factorization/Icosahedral/ExteriorSquareCoordinates.coordinatePermutationRepresentation`
- Truth anchor: `D5/S3/Factorization/Icosahedral/ExteriorSquareCoordinates.exteriorSquareCoordinateEquiv`
- Truth anchor: `D5/S3/Factorization/Icosahedral/ExteriorSquareCoordinates.hodgeEndomorphism`
- Dependency: [D5/S3/Arith/Lattices/ExactDualLatticeFormula](../../Arith/Lattices/ExactDualLatticeFormula.md)
