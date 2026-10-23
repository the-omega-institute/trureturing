# The finite SL2(F5) central-square certificate

## Abstract

Finite SL2 over F5 has only the two square roots of identity, with the explicit transport matrices.

Work over the five-element field ZMod(5) and write M(a,b,c,d) for the two-by-two matrix with those four entries. The first clause enumerates all determinant-one matrices and checks the square-root alternatives I and -I. The remaining clauses check the explicit matrices used in the low and high return words.

This is a finite certificate for the central-involution obstruction in the SL2(F5) example. It does not formalize the general face-transport theorem, the projective quotient PSL2(F5), or the geometric realization of the resulting twelve-degree and nine-degree edges.

**Theorem 1.1 (Finite central-square and return-word certificate).**

$$\left(\forall a \in ZMod\left(5\right),\; \forall b \in ZMod\left(5\right),\; \forall c \in ZMod\left(5\right),\; \forall d \in ZMod\left(5\right),\; a \cdot d - b \cdot c = 1 \Rightarrow \left(M\left(a, b, c, d\right) \cdot M\left(a, b, c, d\right) = I \Rightarrow \left(M\left(a, b, c, d\right) = I \lor M\left(a, b, c, d\right) = - I\right)\right)\right) \land \left(- I \ne I \land \left(det\left(u\right) = 1 \land \left(det\left(v\right) = 1 \land \left(det\left(vInverse\right) = 1 \land \left(vInverse \cdot v = I \land \left(v \cdot vInverse = I \land \left(ell = M\left(0, 1, 4, 0\right) \land \left(h = M\left(3, 3, 4, 1\right) \land \left(ell^{2} = - I \land \left(h^{3} = I \land \left(u^{3} = - I \land v^{5} = I\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/SL2F5CentralSquareCertificate.sl2f5_central_square_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The universal clause is a bounded kernel computation over all four entries in ZMod(5). The explicit determinant, inverse, matrix, and power identities are checked in the same computation.

## References

- Truth anchor: `D5/S3/FiniteGroups/SL2F5CentralSquareCertificate.sl2f5_central_square_certificate`
