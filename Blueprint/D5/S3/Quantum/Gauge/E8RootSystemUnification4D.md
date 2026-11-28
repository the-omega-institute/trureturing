# E8 roots and the exceptional family branching

## Abstract

E8 roots and the exceptional family branching.

All root vectors use the same eight real coordinates as the existing E6 subsystem. The doubled integral model makes parity, Weyl reflections and simple-root coefficients exact. The branching records the adjoint root sets and their weights with respect to E6 and the orthogonal family A2.

**Theorem 1.1 (The 240 exceptional roots).**

Lean statement: `D5/S3/Quantum/Gauge/E8RootSystemUnification4D.e8Roots_card`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E8RootSystemUnification4D.e8Roots_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. S. Viazovska (2017). *The sphere packing problem in dimension 8*. DOI: [10.4007/annals.2017.185.3.7](https://doi.org/10.4007/annals.2017.185.3.7). URL: <https://arxiv.org/abs/1603.04246>.

*Commentary.*

The doubled integral construction has 112 two-coordinate roots with entries of magnitude two and 128 sign vectors with even minus parity. Their disjoint union has cardinality 240.

**Theorem 1.2 (Adjoint dimension count).**

Lean statement: `D5/S3/Quantum/Gauge/E8RootSystemUnification4D.e8_lie_algebra_dimension`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E8RootSystemUnification4D.e8_lie_algebra_dimension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. S. Viazovska (2017). *The sphere packing problem in dimension 8*. DOI: [10.4007/annals.2017.185.3.7](https://doi.org/10.4007/annals.2017.185.3.7). URL: <https://arxiv.org/abs/1603.04246>.

*Commentary.*

The rank-eight Cartan contribution and the 240 roots give dimension 248.

**Theorem 1.3 (Root square length).**

Lean statement: `D5/S3/Quantum/Gauge/E8RootSystemUnification4D.e8Roots_simply_laced`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E8RootSystemUnification4D.e8Roots_simply_laced` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. S. Viazovska (2017). *The sphere packing problem in dimension 8*. DOI: [10.4007/annals.2017.185.3.7](https://doi.org/10.4007/annals.2017.185.3.7). URL: <https://arxiv.org/abs/1603.04246>.

*Commentary.*

Every root has Euclidean square length two after dividing the integral coordinates by two.

**Theorem 1.4 (Crystallographic inner products).**

Lean statement: `D5/S3/Quantum/Gauge/E8RootSystemUnification4D.e8Roots_crystallographic_inner_products`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E8RootSystemUnification4D.e8Roots_crystallographic_inner_products` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. S. Viazovska (2017). *The sphere packing problem in dimension 8*. DOI: [10.4007/annals.2017.185.3.7](https://doi.org/10.4007/annals.2017.185.3.7). URL: <https://arxiv.org/abs/1603.04246>.

*Commentary.*

Two roots have inner product in the set consisting of minus two, minus one, zero, one and two. The upper endpoint characterizes equal roots and the lower endpoint characterizes opposite roots.

**Theorem 1.5 (Weyl reflections and negation).**

Lean statement: `D5/S3/Quantum/Gauge/E8RootSystemUnification4D.e8Roots_weyl_reflection_closed`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E8RootSystemUnification4D.e8Roots_weyl_reflection_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. S. Viazovska (2017). *The sphere packing problem in dimension 8*. DOI: [10.4007/annals.2017.185.3.7](https://doi.org/10.4007/annals.2017.185.3.7). URL: <https://arxiv.org/abs/1603.04246>.

*Commentary.*

For roots alpha and beta, subtracting the inner product of alpha and beta times alpha from beta gives a root. The negative of alpha is also a root.

**Theorem 1.6 (Unimodular simple system).**

Lean statement: `D5/S3/Quantum/Gauge/E8RootSystemUnification4D.e8_dynkin_simple_roots`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E8RootSystemUnification4D.e8_dynkin_simple_roots` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. S. Viazovska (2017). *The sphere packing problem in dimension 8*. DOI: [10.4007/annals.2017.185.3.7](https://doi.org/10.4007/annals.2017.185.3.7). URL: <https://arxiv.org/abs/1603.04246>.

*Commentary.*

The eight explicit simple roots belong to the root set and extend the six simple roots of E6. Their Gram matrix is the integral Cartan matrix and has determinant one. They are linearly independent, and every root has integral coordinates in this basis with all coefficients nonnegative or all nonpositive.

**Theorem 1.7 (Orthogonal exceptional and family subsystems).**

Lean statement: `D5/S3/Quantum/Gauge/E8RootSystemUnification4D.e6_and_a2_subsystems_in_e8`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E8RootSystemUnification4D.e6_and_a2_subsystems_in_e8` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. S. Viazovska (2017). *The sphere packing problem in dimension 8*. DOI: [10.4007/annals.2017.185.3.7](https://doi.org/10.4007/annals.2017.185.3.7). URL: <https://arxiv.org/abs/1603.04246>.

*Commentary.*

The E6 and A2 root sets lie in E8. The A2 roots are exactly the six E8 roots orthogonal to the E6 subspace. Its two simple roots span that orthogonal complement and have Gram matrix with diagonal two, off-diagonal minus one and determinant three. Every E6 root is orthogonal to every A2 root.

**Theorem 1.8 (Four branches of the adjoint root set).**

Lean statement: `D5/S3/Quantum/Gauge/E8RootSystemUnification4D.e8_e6_x_su3_branching_248`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E8RootSystemUnification4D.e8_e6_x_su3_branching_248` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. S. Viazovska (2017). *The sphere packing problem in dimension 8*. DOI: [10.4007/annals.2017.185.3.7](https://doi.org/10.4007/annals.2017.185.3.7). URL: <https://arxiv.org/abs/1603.04246>.

*Commentary.*

The four pairwise disjoint branches cover the E8 roots and have sizes 72, 6, 81 and 81. The first two branches contribute six and two Cartan directions respectively, giving the adjoint dimension count 78 plus 8 plus 81 plus 81.

**Theorem 1.9 (Fundamental and conjugate weight fibers).**

Lean statement: `D5/S3/Quantum/Gauge/E8RootSystemUnification4D.e8_family_weight_fibers`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E8RootSystemUnification4D.e8_family_weight_fibers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. S. Viazovska (2017). *The sphere packing problem in dimension 8*. DOI: [10.4007/annals.2017.185.3.7](https://doi.org/10.4007/annals.2017.185.3.7). URL: <https://arxiv.org/abs/1603.04246>.

*Commentary.*

The three fundamental weights are (1, 0), (-1, 1) and (0, -1) in simple-root inner product coordinates. The conjugate weights are their negatives. The fibers consist precisely of the E8 roots with the specified weight, and each fiber has 27 elements. The three fibers partition each 81-root branch.

**Theorem 1.10 (SO(10) and abelian charges in each fiber).**

Lean statement: `D5/S3/Quantum/Gauge/E8RootSystemUnification4D.e8_e6_generation_weights`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E8RootSystemUnification4D.e8_e6_generation_weights` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. S. Viazovska (2017). *The sphere packing problem in dimension 8*. DOI: [10.4007/annals.2017.185.3.7](https://doi.org/10.4007/annals.2017.185.3.7). URL: <https://arxiv.org/abs/1603.04246>.

*Commentary.*

Each fundamental fiber is in bijection with the E6 basis of 27 states. The bijection preserves the five-coordinate SO(10) Cartan evaluation and the abelian charge. The charge sectors at 1, minus 2 and 4 have sizes 16, 10 and 1 respectively.

**Theorem 1.11 (Lowering between the three family weights).**

Lean statement: `D5/S3/Quantum/Gauge/E8RootSystemUnification4D.e8_family_root_steps`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E8RootSystemUnification4D.e8_family_root_steps` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. S. Viazovska (2017). *The sphere packing problem in dimension 8*. DOI: [10.4007/annals.2017.185.3.7](https://doi.org/10.4007/annals.2017.185.3.7). URL: <https://arxiv.org/abs/1603.04246>.

*Commentary.*

For each of the 27 states, subtracting the first A2 simple root reaches the second fiber. Subtracting the second A2 simple root from there reaches the third fiber.

## References

- Truth anchor: `D5/S3/Quantum/Gauge/E8RootSystemUnification4D.e6_and_a2_subsystems_in_e8`
- Truth anchor: `D5/S3/Quantum/Gauge/E8RootSystemUnification4D.e8Roots_card`
- Truth anchor: `D5/S3/Quantum/Gauge/E8RootSystemUnification4D.e8Roots_crystallographic_inner_products`
- Truth anchor: `D5/S3/Quantum/Gauge/E8RootSystemUnification4D.e8Roots_simply_laced`
- Truth anchor: `D5/S3/Quantum/Gauge/E8RootSystemUnification4D.e8Roots_weyl_reflection_closed`
- Truth anchor: `D5/S3/Quantum/Gauge/E8RootSystemUnification4D.e8_dynkin_simple_roots`
- Truth anchor: `D5/S3/Quantum/Gauge/E8RootSystemUnification4D.e8_e6_generation_weights`
- Truth anchor: `D5/S3/Quantum/Gauge/E8RootSystemUnification4D.e8_e6_x_su3_branching_248`
- Truth anchor: `D5/S3/Quantum/Gauge/E8RootSystemUnification4D.e8_family_root_steps`
- Truth anchor: `D5/S3/Quantum/Gauge/E8RootSystemUnification4D.e8_family_weight_fibers`
- Truth anchor: `D5/S3/Quantum/Gauge/E8RootSystemUnification4D.e8_lie_algebra_dimension`
- Dependency: [D5/S3/Quantum/Gauge/E6TrinificationUnification4D](E6TrinificationUnification4D.md)
