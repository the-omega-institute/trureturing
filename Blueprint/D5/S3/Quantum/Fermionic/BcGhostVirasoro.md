# The actual bc ghost Virasoro representation

## Abstract

The normal ordered bc modes on the actual algebraic ghost Fock space satisfy the full integer Virasoro relation with central charge minus twenty-six.

The carrier is the complex vector space of finitely supported functions on finite subsets of the natural numbers. The b and c operators are exactly the CountableOccupationFock operators with the BcGhostFock vacuum cuts. The construction is the classical algebraic bc system of weights two and minus one; no novelty is claimed. The anomaly is calculated in this representation, using its proved CAR and scalar commutant.

**Definition 1.1 (normal).**

$$\forall p \in Int,\; \forall q \in Int,\; \operatorname{normal}\left(p, q\right) = \operatorname{ite}\left(p \le -2, \operatorname{b}\left(p\right) \cdot \operatorname{c}\left(q\right), -\left(\operatorname{c}\left(q\right) \cdot \operatorname{b}\left(p\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostVirasoro.normal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The b creator is placed on the left. In the other branch the reversed odd product carries a minus sign. This prescription precedes the summation.

**Definition 1.2 (summand).**

$$\forall m \in Int,\; \forall q \in Int,\; \operatorname{summand}\left(m, q\right) = \operatorname{smul}\left(\operatorname{Int}.\operatorname{cast}\left(m + q\right), \operatorname{normal}\left(m - q, q\right)\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostVirasoro.summand` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient m plus q implements the ghost conformal weights.

**Theorem 1.3 (summand finite).**

$$\forall m \in Int,\; \forall v \in Fock,\; \operatorname{Function}.\operatorname{HasFiniteSupport}\left((q\mapsto\operatorname{summand}\left(m, q, v\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostVirasoro.summand_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a basis occupation S, an index outside the interval with radius the absolute value of m plus the largest occupied site plus three forces a rightmost annihilator at an absent site. Finite linear combinations preserve this finite support. The assertion is pointwise in v and does not say that the endomorphism family has finite support.

**Definition 1.4 (L).**

$$\forall m \in Int,\; \forall v \in Fock,\; \operatorname{L}\left(m, v\right) = \sum_{q\in Int}^{fin}\operatorname{summand}\left(m, q, v\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostVirasoro.L` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every vector is acted on by the genuine pointwise finite sum. Additivity and complex linearity follow from the proved finite supports.

**Theorem 1.5 (ward b).**

$$\forall m \in Int,\; \forall r \in Int,\; \operatorname{L}\left(m\right) \cdot \operatorname{b}\left(r\right) - \operatorname{b}\left(r\right) \cdot \operatorname{L}\left(m\right) = \operatorname{smul}\left(\operatorname{Int}.\operatorname{cast}\left(m - r\right), \operatorname{b}\left(m + r\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostVirasoro.ward_b` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

CAR contracts each individual normal product at q equal to minus r. Passing through the sum uses the actual supports on both v and b r v. This is the weight two Ward identity.

**Theorem 1.6 (ward c).**

$$\forall m \in Int,\; \forall r \in Int,\; \operatorname{L}\left(m\right) \cdot \operatorname{c}\left(r\right) - \operatorname{c}\left(r\right) \cdot \operatorname{L}\left(m\right) = \operatorname{smul}\left(\operatorname{Int}.\operatorname{cast}\left(-2 \cdot m - r\right), \operatorname{c}\left(m + r\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostVirasoro.ward_c` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The contraction is at q equal to m plus r. The finite supports on v and c r v justify the exchange. This is the weight minus one Ward identity.

**Definition 1.7 (centralDefect).**

$$\forall m \in Int,\; \forall n \in Int,\; \operatorname{centralDefect}\left(m, n\right) = \operatorname{L}\left(m\right) \cdot \operatorname{L}\left(n\right) - \operatorname{L}\left(n\right) \cdot \operatorname{L}\left(m\right) - \operatorname{smul}\left(\operatorname{Int}.\operatorname{cast}\left(m - n\right), \operatorname{L}\left(m + n\right)\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostVirasoro.centralDefect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two Ward identities and Jacobi imply that this defect commutes with every actual b and c mode. The existing scalar commutant therefore makes it a scalar operator.

**Definition 1.8 (epsilon).**

$$\forall v \in Fock,\; \operatorname{epsilon}\left(v\right) = \operatorname{v}\left(\operatorname{Finset}.\operatorname{empty}\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostVirasoro.epsilon` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This linear functional extracts the empty occupation coefficient.

**Theorem 1.9 (virasoro).**

$$\forall m \in Int,\; \forall n \in Int,\; \operatorname{L}\left(m\right) \cdot \operatorname{L}\left(n\right) - \operatorname{L}\left(n\right) \cdot \operatorname{L}\left(m\right) = \operatorname{smul}\left(\operatorname{Int}.\operatorname{cast}\left(m - n\right), \operatorname{L}\left(m + n\right)\right) + \operatorname{smul}\left(\operatorname{ite}\left(m + n = 0, \operatorname{div}\left(-26, 12\right) \cdot \left(\operatorname{Int}.\operatorname{cast}\left(m\right)^{3} - \operatorname{Int}.\operatorname{cast}\left(m\right)\right), 0\right), (1:\operatorname{Module}.\operatorname{End}\left(Complex, Fock\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostVirasoro.virasoro` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The vacuum action is the finite sum over q from n plus two through one. A leftmost b creator has zero empty coefficient, so the pair Ward calculation kills the off-diagonal scalar. On m equal to a nonnegative integer a and n equal to minus a, q equal to one minus r turns the remaining coefficient into the sum of (1-a-r)(2a+1-r) for r from zero through a minus one. Its value is minus thirteen sixths times a cubed minus a. Antisymmetry supplies the negative integers with the opposite sign. The result holds on every finite-excitation vector, without an abstract Virasoro premise or a cutoff.

This theorem establishes the algebraic ghost anomaly. It does not establish a BRST charge, its nilpotence or cohomology, a no-ghost theorem, a sewn conformal field theory, complete string dynamics or an AdS/CFT correspondence.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostVirasoro.L`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostVirasoro.centralDefect`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostVirasoro.epsilon`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostVirasoro.normal`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostVirasoro.summand`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostVirasoro.summand_finite`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostVirasoro.virasoro`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostVirasoro.ward_b`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostVirasoro.ward_c`
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostFock](BcGhostFock.md)
