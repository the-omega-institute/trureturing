# The ordered Cech-singular double complex

## Abstract

The ordered Cech-singular double complex.

**Definition 1.1 (Ordered intersections in each simplicial degree).**

Lean statement: `D5/S3/Topology/TauCeti/AlgebraicTopology/Singular/OrderedCech.bicomplex`

*Formalization.* `D5/S3/Topology/TauCeti/AlgebraicTopology/Singular/OrderedCech.bicomplex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a simplicial set A covered by a linearly ordered family P of subcomplexes, the ordered intersection complexes in each simplicial degree form rows. Alternating singular face maps define a commuting bicomplex with coefficients in an object R of an abelian category with the required coproducts.

**Definition 1.2 (The specified augmentation).**

Lean statement: `D5/S3/Topology/TauCeti/AlgebraicTopology/Singular/OrderedCech.horizontalAugmentation`

*Formalization.* `D5/S3/Topology/TauCeti/AlgebraicTopology/Singular/OrderedCech.horizontalAugmentation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In each singular degree the horizontal augmentation is the ordered-cover augmentation on the same simplex generators. It sends each singleton-indexed simplex to that simplex and is zero in positive ordered degree.

**Theorem 1.3 (The finite-degree total comparison).**

Lean statement: `D5/S3/Topology/TauCeti/AlgebraicTopology/Singular/OrderedCech.horizontal_total_comparison`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/TauCeti/AlgebraicTopology/Singular/OrderedCech.horizontal_total_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In an abelian category with the required coproducts, if P covers in every simplicial degree, the actual horizontal total map induces homology isomorphisms in degrees zero and one and an epimorphism in degree two. The ordered-cover chain contraction and finite-degree bicomplex comparison apply to this specified map.

**Theorem 1.4 (Contractible singular columns).**

Lean statement: `D5/S3/Topology/TauCeti/AlgebraicTopology/Singular/OrderedCech.isIso_coefficientAugmentation_of_contractible`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/TauCeti/AlgebraicTopology/Singular/OrderedCech.isIso_coefficientAugmentation_of_contractible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any coefficient object R in an abelian category with the required coproducts, any contractible topological space X, and every natural degree q, its actual singular coefficient-sum augmentation induces a degree-q homology isomorphism. In degree zero this is the singular H0 augmentation. Positive degrees use reduced singular homology and contractibility; the target complex is concentrated at zero.

## References

- Truth anchor: `D5/S3/Topology/TauCeti/AlgebraicTopology/Singular/OrderedCech.bicomplex`
- Truth anchor: `D5/S3/Topology/TauCeti/AlgebraicTopology/Singular/OrderedCech.horizontalAugmentation`
- Truth anchor: `D5/S3/Topology/TauCeti/AlgebraicTopology/Singular/OrderedCech.horizontal_total_comparison`
- Truth anchor: `D5/S3/Topology/TauCeti/AlgebraicTopology/Singular/OrderedCech.isIso_coefficientAugmentation_of_contractible`
- Dependency: [D5/S3/Topology/TauCeti/Algebra/Homology/FiniteDegreeComparison](../../Algebra/Homology/FiniteDegreeComparison.md)
- Dependency: [D5/S3/Topology/TauCeti/Algebra/Homology/OrderedCechCover](../../Algebra/Homology/OrderedCechCover.md)
