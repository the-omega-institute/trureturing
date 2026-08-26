# Quadratic Observation Bound

## Abstract

Binary group observers see no more than the square quotient.

**Theorem 1.1 (Every binary observer kills the square subgroup).**

$$G^{2} \leq \operatorname{JointKernel}(G).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/QuadraticObservationBound.square_subgroup_le_quadratic_joint_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A quadratic observer is any group homomorphism to the multiplicative form of ZMod 2; surjectivity is not assumed.

The named squareSubgroup is the normal closure of all squares. Every observer sends each square to one, so this subgroup lies in the intersection of all observer kernels.

**Theorem 1.2 (The square quotient is an elementary abelian two-quotient).**

$$\operatorname{exponent}(\operatorname{Quotient}(G, G^{2})) \mid 2 \land \operatorname{Commutative}(\operatorname{Quotient}(G, G^{2})).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/QuadraticObservationBound.square_quotient_exponent_divides_two_and_commutative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every element of the quotient squares to one. Mathlib's exponent interface gives exponent dividing two, and its order-two commutation lemma makes the quotient commutative. No finiteness or commutativity hypothesis on the original group is used.

**Theorem 1.3 (A nontrivial square subgroup forces a joint-readout collision).**

$$G^{2} \neq \{1\} \Rightarrow\\{}\exists x, y\in G, x \neq y \land \operatorname{Readout}(x) = \operatorname{Readout}(y).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/QuadraticObservationBound.quadratic_readout_has_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose a nonidentity element of the square subgroup. The upper-bound theorem puts it in every observer kernel, so it and the identity have the same complete binary readout.

**Lemma 1.4 (The strictness hypothesis is necessary on C2).**

$$C_{2}^{2} = \{1\} \land \operatorname{Injective}(\operatorname{Readout}(C_{2})).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/QuadraticObservationBound.nontrivial_square_subgroup_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For C2 every square is one, while the identity observer belongs to the full observer family and separates both elements. This is the concrete counterexample obtained by deleting the nontrivial square-subgroup hypothesis.

**Lemma 1.5 (C4 is a named cyclic two-group strict example).**

$$\operatorname{Commutative}(C_{4}) \land C_{4}^{2} \neq \{1\} \land \neg\operatorname{Injective}(\operatorname{Readout}(C_{4})).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/QuadraticObservationBound.zmod_four_strictness_example` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The multiplicative form of ZMod 4 is commutative, and the square of one is the nonidentity element two. Hence its square subgroup is nontrivial and the joint readout has a collision.

The remaining Lean audits cover an empty carrier, the trivial group, the constant observer, and a noncommutative S3 example. There is no finite-cardinality assumption or numeric depth.

## References

- Truth anchor: `D5/S3/Factorization/Galois/QuadraticObservationBound.nontrivial_square_subgroup_is_necessary`
- Truth anchor: `D5/S3/Factorization/Galois/QuadraticObservationBound.quadratic_readout_has_collision`
- Truth anchor: `D5/S3/Factorization/Galois/QuadraticObservationBound.square_quotient_exponent_divides_two_and_commutative`
- Truth anchor: `D5/S3/Factorization/Galois/QuadraticObservationBound.square_subgroup_le_quadratic_joint_kernel`
- Truth anchor: `D5/S3/Factorization/Galois/QuadraticObservationBound.zmod_four_strictness_example`
