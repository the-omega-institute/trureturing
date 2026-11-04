# TrivialMotions

## Abstract

Translations and skew rotations give a kernel lower bound at affinely spanning placements.

**Definition 1.1 (Translations).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.translationMotion`

*Formalization.* `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.translationMotion` (`✓ std3`).

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For any V,d and real d-dimensional vector t, translationMotion t is the constant vertex velocity t.

**Theorem 1.2 (Translations preserve all edge constraints).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.translationMotion_mem_ker`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.translationMotion_mem_ker` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every simple graph G, real placement p and translation vector t, the constant motion lies in the rigidity kernel. The difference of its endpoint velocities is zero.

**Definition 1.3 (Linear rotation motions).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.infinitesimalRotation`

*Formalization.* `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.infinitesimalRotation` (`✓ std3`).

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every real linear endomorphism A of the d-dimensional Euclidean space and placement p, infinitesimalRotation A p sends v to A(p(v)).

**Theorem 1.4 (Skew rotations preserve edge constraints).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.infinitesimalRotation_mem_ker`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.infinitesimalRotation_mem_ker` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every graph G and placement p, if the real linear map A satisfies inner(x,A(x))=0 for every x, then infinitesimalRotation A p lies in the rigidity kernel. Linearity replaces the difference of endpoint images by the image of their difference.

**Definition 1.5 (The trivial-motion subspace).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.trivialMotions`

*Formalization.* `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.trivialMotions` (`✓ std3`).

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For any placement p, trivialMotions p is the real linear span of all translations together with all rotations from linear maps A satisfying inner(x,A(x))=0 for every x.

**Theorem 1.6 (Translation generators).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.translationMotion_mem_trivialMotions`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.translationMotion_mem_trivialMotions` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

Every translation belongs to the trivial-motion span for every placement.

**Theorem 1.7 (Rotation generators).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.infinitesimalRotation_mem_trivialMotions`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.infinitesimalRotation_mem_trivialMotions` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every placement, each linear rotation satisfying inner(x,A(x))=0 for all x belongs to its trivial-motion span.

**Theorem 1.8 (All trivial motions are kernel motions).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.trivialMotions_le_ker`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.trivialMotions_le_ker` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every graph and placement, the trivial-motion subspace is contained in the rigidity kernel, because its translation and rotation generators are.

**Definition 1.9 (Elementary skew maps).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.elemSkewMap`

*Formalization.* `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.elemSkewMap` (`✓ std3`).

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every natural d and i,j in Fin d, the elementary skew map sends x to x(j) times the i coordinate vector minus x(i) times the j coordinate vector.

**Theorem 1.10 (Coordinate formula).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.elemSkewMap_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.elemSkewMap_apply` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every i,j,k and x, coordinate k of elemSkewMap i j x is x(j) if k=i, minus x(i) if k=j, with the other terms zero. Equal i,j give the zero map.

**Theorem 1.11 (Skew orthogonality).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.inner_elemSkewMap_self`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.inner_elemSkewMap_self` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every real Euclidean vector x and coordinate pair i,j, inner(x,elemSkewMap i j x)=0. The two possible cross terms cancel.

**Theorem 1.12 (Ordered-pair coefficient extraction).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.elemSkewMap_ofLp_inr_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.elemSkewMap_ofLp_inr_apply` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For i in Fin d, j in Fin i.val, and every ordered-pair index s, evaluate its elementary skew map on coordinate vector j and read coordinate i. The result is one exactly when s=(i,j), and zero otherwise. The strict inequality in each index prevents a reversed cross term.

**Definition 1.13 (The translation and rotation family).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.trivialMotionFamily`

*Formalization.* `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.trivialMotionFamily` (`✓ std3`).

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

At any placement in dimension d, the family indexed by Fin d plus the dependent sum over i in Fin d of Fin i.val consists of d coordinate translations and one skew rotation per ordered pair j<i.

**Theorem 1.14 (Membership of the whole family).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.trivialMotionFamily_mem_trivialMotions`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.trivialMotionFamily_mem_trivialMotions` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

Every member of the translation and rotation family belongs to the trivial-motion subspace of its placement.

**Theorem 1.15 (Joint independence from affine spanning).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.trivialMotionFamily_linearIndependent`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.trivialMotionFamily_linearIndependent` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For any placement p in any dimension, if the affine span of its image is the whole Euclidean space, the complete translation and ordered-pair rotation family is linearly independent. A vanishing combination is t+A(p(v))=0 at every vertex. Affine spanning forces A=0; coefficient extraction then kills every rotation coefficient and every translation coefficient.

**Theorem 1.16 (Number of generators).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.fintype_card_trivialMotionFamilyIndex`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.fintype_card_trivialMotionFamilyIndex` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every natural dimension d, the family index has cardinality d(d+1)/2: d translations plus the sum of i over i<d rotations.

**Theorem 1.17 (Dimension of the trivial-motion span).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.trivialMotions_finrank_ge_of_affinelySpanning`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.trivialMotions_finrank_ge_of_affinelySpanning` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For finite V and a placement p whose image affinely spans the d-dimensional Euclidean space, the real dimension of trivialMotions p is at least d(d+1)/2. Lift the independent family into that subspace.

**Theorem 1.18 (The kernel lower bound).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.rigidityMap_ker_finrank_ge_of_affinelySpanning`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.rigidityMap_ker_finrank_ge_of_affinelySpanning` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every finite V, simple graph G, and affinely spanning real placement p in dimension d, the rigidity kernel has dimension at least d(d+1)/2. In dimension two this supplies three independent motions on every affinely spanning restriction.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.elemSkewMap`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.elemSkewMap_apply`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.elemSkewMap_ofLp_inr_apply`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.fintype_card_trivialMotionFamilyIndex`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.infinitesimalRotation`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.infinitesimalRotation_mem_ker`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.infinitesimalRotation_mem_trivialMotions`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.inner_elemSkewMap_self`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.rigidityMap_ker_finrank_ge_of_affinelySpanning`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.translationMotion`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.translationMotion_mem_ker`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.translationMotion_mem_trivialMotions`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.trivialMotionFamily`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.trivialMotionFamily_linearIndependent`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.trivialMotionFamily_mem_trivialMotions`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.trivialMotions`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.trivialMotions_finrank_ge_of_affinelySpanning`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/TrivialMotions.trivialMotions_le_ker`
- Dependency: [D5/S3/Combinatorics/Graph/Laman/Framework](Framework.md)
