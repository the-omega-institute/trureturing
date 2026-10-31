# Extreme points of finite matroid intersection

## Abstract

The actual nonnegative rank-inequality intersection of two finite matroids has only zero-one extreme points.

**Theorem 1.1 (The rank-inequality intersection has zero-one extreme points).**

$$\forall (E: Type_{u}), [\operatorname{Finite}\left(E\right)], \forall (M: \operatorname{Matroid}\left(E\right)), \forall (N: \operatorname{Matroid}\left(E\right)), (\operatorname{ground}\left(M\right) = univ) \Rightarrow ((\operatorname{ground}\left(N\right) = univ) \Rightarrow (\forall (v: E \to \mathbb{R}), (v \in \operatorname{extremePoints}\left(\mathbb{R}, \left\{x: E \to \mathbb{R} \mid (\forall (a: E), 0 \le x\left(a\right)) \land (\forall (U: \operatorname{Set}\left(E\right)), (\sum_{a \in U} x\left(a\right) \le \operatorname{toNat}\left(\operatorname{eRk}\left(M, U\right)\right)) \land (\sum_{a \in U} x\left(a\right) \le \operatorname{toNat}\left(\operatorname{eRk}\left(N, U\right)\right)))\right\}\right)) \Rightarrow (\forall (a: E), (v\left(a\right) = 0) \lor (v\left(a\right) = 1))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/FiniteIntersectionPolytope.extreme_point_zero_one` (`✓ std3`). ∎

*Citation.* Michel X. Goemans (2015). *Lecture notes on matroid intersection*. URL: <https://math.mit.edu/~goemans/18433S15/matroid-intersect-notes.pdf>.

*Commentary.*

Let E be any finite type in an arbitrary universe, and let M and N be native matroids on E with both grounds equal to all of E. For every subset U of E, write r(M,U) for the natural number ENat.toNat of Matroid.eRk M U, regarded as a real number in inequalities. All these extended ranks are finite. Define P to consist of actual real vectors x on E whose coordinates are nonnegative and whose sum on every U is at most both r(M,U) and r(N,U). The theorem says that every real extreme point of this P has each coordinate equal to zero or one.

The displayed P is the inequality region itself. The theorem assumes neither a convex-hull identity nor an integral dual. Empty E, loops, rank-zero matroids, unequal ranks and nonrepresentable matroids are included. There is no common-basis, nonempty-ground, positive-rank, loopless, supplied-chain or unique-equation hypothesis. The use of finite-set sums does not select an enumeration of E.

Fix an extreme point v. In each rank family, submodularity and the modular identity for finite sums show that the v-tight subsets are closed under union and intersection. Choose a maximal inclusion chain from that actual tight family. For a chain member A, its predecessor is the union of the strictly smaller chain members, and its layer is A minus that predecessor. The predecessor is tight, so its layer sum at v is the integer rank difference r(M,A) minus r(M,pred A).

Every tight subset contains each chain layer wholly or misses it. Indeed, the union of the predecessor with the intersection of that subset and A is tight and comparable with the chain. Maximality permits no proper intermediate layer cut. The layers are disjoint, cover the union of all tight subsets, and therefore recover every tight subset sum. The chain top is this tight union; it need not equal E. This construction gives the compression of actual equations rather than assuming an incidence span.

Apply the existing active-constraint kernel theorem to the complete actual finite inequality family: negative coordinate projections and subset-sum forms from both matroids. A direction killed by all zero-coordinate equations and both layer families is killed by every tight rank form, and hence is zero. Thus the layer equations and actual zero-coordinate equations determine v among all real vectors, without requiring an alternative vector to be feasible. No full-dimensionality assumption or externally supplied positive-slack bound is required.

Use the disjoint layers as rows, with the second family negated. Every coordinate has at most one endpoint in each family; give an uncovered side a dummy endpoint and delete the dummy rows. This identifies the layer matrix directly with a submatrix of an integer signed-incidence matrix. The existing signed-incidence theorem gives total unimodularity, and the existing unit-row extension adds exactly the zero-coordinate equations. No assertion is made that the complete subset-rank matrix is totally unimodular, or that arbitrary row operations preserve total unimodularity.

The resulting integer matrix A and integer right-hand side b satisfy A over the reals times v equals b. The existing integer inner-inverse theorem gives an integer B with ABA equal to A, including empty or rank-deficient matrices. Therefore the real cast of the integer vector B times b solves the same equations. Their proved uniqueness identifies it with v. Nonnegativity and the singleton rank bound, which holds also at loops, put each integer coordinate between zero and one.

Goemans's matroid-intersection notes, Theorem 6.6, give the classical vertex argument; Lemma 5.5 and Theorem 5.6 of the matroid-optimization notes supply tight-set closure and chain compression. The latter is the result referred to by the stale Theorem 4.6 cross-reference in the intersection notes. The two-family incidence context also appears as Claim 3 in the 2009 lecture notes. This formalization carries no originality or open-problem claim. Weighted optimization and fractional decomposition are prospective applications and are not conclusions of this theorem.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/FiniteIntersectionPolytope.extreme_point_zero_one`
- Dependency: [D5/S3/Combinatorics/Matroids/FiniteIntersection](FiniteIntersection.md)
- Dependency: [D5/S3/Fourier/CharacterSelection/SignedIncidenceTotalUnimodularity](../../Fourier/CharacterSelection/SignedIncidenceTotalUnimodularity.md)
- Dependency: [D5/S3/HomologicalAlgebra/IntegerMatrixInnerInverse](../../HomologicalAlgebra/IntegerMatrixInnerInverse.md)
- Dependency: [D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion/RowCertificates](../../Observer/Separation/FixedSkeletonWeightedInclusion/RowCertificates.md)
