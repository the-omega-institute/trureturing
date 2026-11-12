# Heisenberg triples

## Abstract

Heisenberg triples over a ring have explicit cardinality, powers and derived subgroup.

**Theorem 1.1 (The cardinality of triples).**

$$\forall R \in \operatorname{Type}\left(\right),\; \operatorname{NatCard}\left(\operatorname{HeisenbergGroup}\left(R\right)\right) = \operatorname{NatCard}\left(R\right)^{3}$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Heisenberg/Basic.card_eq` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *The Heisenberg group over a ring*. URL: <https://github.com/TauCetiProject/TauCeti/blob/29b9cc14af71b7c058316535d555c9bbf64b2df7/TauCeti/GroupTheory/SpecificGroups/Heisenberg.lean>.

*Commentary.*

HeisenbergGroup R consists of all triples (x,y,z) of ring elements. The underlying type is equivalent to R times R times R, so its natural cardinality is the cube of the coefficient cardinality. The type-level statement also covers infinite carriers under Nat.card. Multiplication is (x,y,z)(X,Y,Z)=(x+X,y+Y,z+Z+xY), identity is (0,0,0), and the inverse is (−x,−y,−z+xy).

**Theorem 1.2 (Powers without division by two).**

$$\forall R \in \operatorname{Type}\left(\right),\; [\operatorname{Ring}\left(R\right)] \forall a \in \operatorname{HeisenbergGroup}\left(R\right),\; \forall n \in \mathbb{N},\; a^{n} = \operatorname{triple}\left(\operatorname{nsmul}\left(n, \operatorname{x}\left(a\right)\right), \operatorname{nsmul}\left(n, \operatorname{y}\left(a\right)\right), \operatorname{add}\left(\operatorname{nsmul}\left(n, \operatorname{z}\left(a\right)\right), \operatorname{nsmul}\left(\operatorname{choose}\left(n, 2\right), \operatorname{mul}\left(\operatorname{x}\left(a\right), \operatorname{y}\left(a\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Heisenberg/Basic.pow_eq` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *The Heisenberg group over a ring*. URL: <https://github.com/TauCetiProject/TauCeti/blob/29b9cc14af71b7c058316535d555c9bbf64b2df7/TauCeti/GroupTheory/SpecificGroups/Heisenberg.lean>.

*Commentary.*

For every ring, every triple a and every natural n, the first coordinates of a to the n are n times x and n times y. Its third coordinate is n times z plus n choose two times xy. Here nsmul is repeated addition and choose is the natural binomial coefficient. This form requires no inverse of two and applies in characteristic two. Induction uses the group multiplication and Pascal's binomial identity.

**Theorem 1.3 (The derived subgroup is the central axis).**

$$\forall R \in \operatorname{Type}\left(\right),\; [\operatorname{Ring}\left(R\right)] \operatorname{commutator}\left(\operatorname{HeisenbergGroup}\left(R\right)\right) = \operatorname{zAxis}\left(R\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Heisenberg/Basic.commutator_eq_zAxis` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *The Heisenberg group over a ring*. URL: <https://github.com/TauCetiProject/TauCeti/blob/29b9cc14af71b7c058316535d555c9bbf64b2df7/TauCeti/GroupTheory/SpecificGroups/Heisenberg.lean>.

*Commentary.*

The native commutator a*b*a inverse*b inverse is (0,0,xY−Xy). Thus every commutator belongs to the z-axis, the subgroup defined by x=y=0. Conversely (0,0,c) is the commutator of (c,0,0) and (0,1,0), so the generated subgroup is the entire axis. The generic group, cardinality, power and axis results are due to The Tau Ceti contributors, in the cited immutable source. Their Apache-2.0 copyright and license are retained with the Lean source. The source-commutator convention is connected separately by inversion of both generators.

## References

- Truth anchor: `D5/S3/FiniteGroups/Heisenberg/Basic.card_eq`
- Truth anchor: `D5/S3/FiniteGroups/Heisenberg/Basic.commutator_eq_zAxis`
- Truth anchor: `D5/S3/FiniteGroups/Heisenberg/Basic.pow_eq`
