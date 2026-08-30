# The Icosahedral Exterior-Square Decomposition

## Abstract

The real exterior square of the centered A5 representation is two conjugate threes.

**Theorem 1.1 (The positive Hodge eigenspace has dimension three).**

$$finrank(\mathbb{R}, V_3) = 3$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Icosahedral/ExteriorSquareThreePlusThree.V3_finrank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The last three wedge coordinates form an explicit linear chart from the positive square-root-of-five Hodge eigenspace to real three-space.

**Theorem 1.2 (The negative Hodge eigenspace has dimension three).**

$$finrank(\mathbb{R}, V_3') = 3$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Icosahedral/ExteriorSquareThreePlusThree.V3Prime_finrank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The conjugate eigenbasis gives an explicit chart from the negative square-root-of-five Hodge eigenspace to real three-space.

**Theorem 1.3 (The positive icosahedral summand is irreducible).**

$$Irreducible(A_5, V_3)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Icosahedral/ExteriorSquareThreePlusThree.V3_irreducible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An exact orbit-frame certificate shows that every nonzero orbit spans all three coordinates, excluding a proper nonzero subrepresentation.

**Theorem 1.4 (The negative icosahedral summand is irreducible).**

$$Irreducible(A_5, V_3')$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Icosahedral/ExteriorSquareThreePlusThree.V3Prime_irreducible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugating the integral quadratic frame certificate gives the same orbit-spanning argument for the negative eigenspace.

**Theorem 1.5 (The two icosahedral summands are Galois conjugate).**

$$Q5GaloisConjugate(V_3, V_3')$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Icosahedral/ExteriorSquareThreePlusThree.V3_V3Prime_galois_conjugate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both coordinate actions come from one exact matrix family over Q(sqrt 5): the two real actions use the embeddings sending sqrt 5 to plus or minus the positive real square root.

**Theorem 1.6 (The exterior square is equivariantly the product of the two threes).**

$$\Lambda^{2} V_4 \equiv V_3 \times V_3'$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Icosahedral/ExteriorSquareThreePlusThree.exteriorSquareV4_equiv_V3_prod_V3Prime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Spectral projectors for the reused Hodge matrix give an explicit linear equivalence, and commutation with every A5 action makes it equivariant.

**Theorem 1.7 (The full exterior-square decomposition theorem).**

$$\Lambda^{2} V_4 \equiv V_3 \times V_3',\\dim = 3, irreducible, GaloisConjugate$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Icosahedral/ExteriorSquareThreePlusThree.exteriorSquareV4_three_plus_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This assembles the equivariant split, both dimension statements, both irreducibility results, and the typed Q(sqrt 5) conjugacy witness. The identity action and zero vector are checked as degenerate probes; the degree is fixed at two, so no empty-index or degree-zero input remains.

## References

- Truth anchor: `D5/S3/Factorization/Icosahedral/ExteriorSquareThreePlusThree.V3Prime_finrank`
- Truth anchor: `D5/S3/Factorization/Icosahedral/ExteriorSquareThreePlusThree.V3Prime_irreducible`
- Truth anchor: `D5/S3/Factorization/Icosahedral/ExteriorSquareThreePlusThree.V3_V3Prime_galois_conjugate`
- Truth anchor: `D5/S3/Factorization/Icosahedral/ExteriorSquareThreePlusThree.V3_finrank`
- Truth anchor: `D5/S3/Factorization/Icosahedral/ExteriorSquareThreePlusThree.V3_irreducible`
- Truth anchor: `D5/S3/Factorization/Icosahedral/ExteriorSquareThreePlusThree.exteriorSquareV4_equiv_V3_prod_V3Prime`
- Truth anchor: `D5/S3/Factorization/Icosahedral/ExteriorSquareThreePlusThree.exteriorSquareV4_three_plus_three`
- Dependency: [D5/S3/Factorization/Icosahedral/ExteriorSquareRepresentations](ExteriorSquareRepresentations.md)
