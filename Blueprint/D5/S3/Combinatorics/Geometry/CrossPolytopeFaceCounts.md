# Faces of Minkowski sums of cross polytopes

## Abstract

Nonnegative weighted sums of coordinate cross polytopes have a signed acyclic formula for every face dimension.

Let n and m be arbitrary natural numbers. Coordinates are indexed by Fin n and summands by Fin m. Each support I(i) is a nonempty finite set of coordinates and each weight w(i) is a nonnegative real number. Equation (3) of Dai, Hou, Liu, Thawinrak and Wang defines the corresponding Minkowski sum. Problem 5.4 asks for its f-vector and, in the simple case, its ordinary h-vector. The formula below supplies the nonempty face counts for this whole family, with real weights in place of integer weights.

**Definition 1.1 (Real coordinate space).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.Ambient`

*Formalization.* `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.Ambient` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ziyi Dai, Qilin Hou, Zhiyuan Liu, Warut Thawinrak and Hongyu Wang (2026). *Counting Lattice Points in Minkowski Sums of Cross Polytopes*. URL: <https://arxiv.org/abs/2608.16037v2>.

*Commentary.*

Ambient(n) is the real vector space Fin n to R, including the zero-dimensional space when n is zero.

**Definition 1.2 (Unsigned data).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.RawData`

*Formalization.* `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.RawData` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ziyi Dai, Qilin Hou, Zhiyuan Liu, Warut Thawinrak and Hongyu Wang (2026). *Counting Lattice Points in Minkowski Sums of Cross Polytopes*. URL: <https://arxiv.org/abs/2608.16037v2>.

*Commentary.*

RawData(n,m) consists of a finite set J of summand indices and a function S assigning a finite coordinate set S(i) to every summand index. No validity or realizability condition is built into this type.

**Definition 1.3 (Coordinate cross polytope).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.crossHull`

*Formalization.* `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.crossHull` (`✓ std3`).

*Citation.* Ziyi Dai, Qilin Hou, Zhiyuan Liu, Warut Thawinrak and Hongyu Wang (2026). *Counting Lattice Points in Minkowski Sums of Cross Polytopes*. URL: <https://arxiv.org/abs/2608.16037v2>.

*Commentary.*

For every finite coordinate set I, crossHull(I) is the real convex hull of all e(j) and -e(j) with j in I. Here e(j) is the coordinate vector with entry one at j and zero elsewhere. An empty I gives the empty convex hull; the theorem requires each summand support to be nonempty.

**Definition 1.4 (Actual Minkowski sum).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.actualQ`

*Formalization.* `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.actualQ` (`✓ std3`).

*Citation.* Ziyi Dai, Qilin Hou, Zhiyuan Liu, Warut Thawinrak and Hongyu Wang (2026). *Counting Lattice Points in Minkowski Sums of Cross Polytopes*. URL: <https://arxiv.org/abs/2608.16037v2>.

*Commentary.*

For arbitrary supports and real weights, actualQ(I,w) is the sum over all i in Fin m of w(i) times crossHull(I(i)), using set addition and scalar multiplication. The empty sum is the singleton containing zero. A zero weight on a nonempty summand also gives that singleton. This is the actual convex set whose faces are counted.

**Definition 1.5 (Positive-weight summands).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.active`

*Formalization.* `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.active` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ziyi Dai, Qilin Hou, Zhiyuan Liu, Warut Thawinrak and Hongyu Wang (2026). *Counting Lattice Points in Minkowski Sums of Cross Polytopes*. URL: <https://arxiv.org/abs/2608.16037v2>.

*Commentary.*

For every real weight function w, active(w) is A = {i : w(i) > 0}. In the theorem all other weights are zero, so they contribute no directions or face choices.

**Definition 1.6 (Union of coordinate supports).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.support`

*Formalization.* `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.support` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ziyi Dai, Qilin Hou, Zhiyuan Liu, Warut Thawinrak and Hongyu Wang (2026). *Counting Lattice Points in Minkowski Sums of Cross Polytopes*. URL: <https://arxiv.org/abs/2608.16037v2>.

*Commentary.*

For any set A of summand indices, support(I,A) is the union of I(i) over i in A. In the counting formula U = support(I,active(w)) and d is the cardinality of U.

**Definition 1.7 (Zero coordinates).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.zeroSet`

*Formalization.* `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.zeroSet` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ziyi Dai, Qilin Hou, Zhiyuan Liu, Warut Thawinrak and Hongyu Wang (2026). *Counting Lattice Points in Minkowski Sums of Cross Polytopes*. URL: <https://arxiv.org/abs/2608.16037v2>.

*Commentary.*

For q = (J,S), zeroSet(I,q) is Z = support(I,J). Every support in J will have zero support value under a realizing normal, and all coordinates of Z vanish under that normal.

**Definition 1.8 (Remaining summands).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.remaining`

*Formalization.* `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.remaining` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ziyi Dai, Qilin Hou, Zhiyuan Liu, Warut Thawinrak and Hongyu Wang (2026). *Counting Lattice Points in Minkowski Sums of Cross Polytopes*. URL: <https://arxiv.org/abs/2608.16037v2>.

*Commentary.*

For A and q = (J,S), remaining(A,q) is A minus J. It contains exactly the positive-weight summands with positive support value in feasible data.

**Definition 1.9 (All remaining coordinates).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.vertexSet`

*Formalization.* `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.vertexSet` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ziyi Dai, Qilin Hou, Zhiyuan Liu, Warut Thawinrak and Hongyu Wang (2026). *Counting Lattice Points in Minkowski Sums of Cross Polytopes*. URL: <https://arxiv.org/abs/2608.16037v2>.

*Commentary.*

For I, A and q, vertexSet(I,A,q) is V = support(I,A) minus zeroSet(I,q). Every coordinate of V is retained, whether or not it occurs in a selected set S(i).

**Definition 1.10 (Coordinates carrying signs).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.selected`

*Formalization.* `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.selected` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ziyi Dai, Qilin Hou, Zhiyuan Liu, Warut Thawinrak and Hongyu Wang (2026). *Counting Lattice Points in Minkowski Sums of Cross Polytopes*. URL: <https://arxiv.org/abs/2608.16037v2>.

*Commentary.*

For A and q, selected(A,q) is T, the union of S(i) over i in remaining(A,q). A sign is chosen once per coordinate of T and is shared by every summand using that coordinate.

**Definition 1.11 (The full vertex type).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.Vertex`

*Formalization.* `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.Vertex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ziyi Dai, Qilin Hou, Zhiyuan Liu, Warut Thawinrak and Hongyu Wang (2026). *Counting Lattice Points in Minkowski Sums of Cross Polytopes*. URL: <https://arxiv.org/abs/2608.16037v2>.

*Commentary.*

Vertex(I,A,q) is the subtype of Fin n consisting of the members of V. Its elements include unselected coordinates and isolated vertices.

**Definition 1.12 (Equality graph).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.equalityGraph`

*Formalization.* `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.equalityGraph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ziyi Dai, Qilin Hou, Zhiyuan Liu, Warut Thawinrak and Hongyu Wang (2026). *Counting Lattice Points in Minkowski Sums of Cross Polytopes*. URL: <https://arxiv.org/abs/2608.16037v2>.

*Commentary.*

On Vertex(I,A,q), two distinct vertices are adjacent exactly when there is an i in remaining(A,q) for which both coordinates belong to S(i). The graph is undirected and has no graph loops.

**Definition 1.13 (Equality components).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.Component`

*Formalization.* `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.Component` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ziyi Dai, Qilin Hou, Zhiyuan Liu, Warut Thawinrak and Hongyu Wang (2026). *Counting Lattice Points in Minkowski Sums of Cross Polytopes*. URL: <https://arxiv.org/abs/2608.16037v2>.

*Commentary.*

Component(I,A,q) is the set of connected components of the equality graph. Its cardinality c counts every isolated vertex, including those outside T. When V is empty, c is zero.

**Definition 1.14 (Strict relation on components).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.strictRel`

*Formalization.* `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.strictRel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ziyi Dai, Qilin Hou, Zhiyuan Liu, Warut Thawinrak and Hongyu Wang (2026). *Counting Lattice Points in Minkowski Sums of Cross Polytopes*. URL: <https://arxiv.org/abs/2608.16037v2>.

*Commentary.*

For components C and D, strictRel(I,A,q,C,D) holds exactly when some remaining summand i has coordinates a and b in V with a in I(i) but outside S(i), b in S(i), and components C and D respectively. Thus the absolute value at a must be smaller than that at b. This relation may have a self-loop even though the equality graph does not.

**Definition 1.15 (Valid unsigned choices).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.validChoice`

*Formalization.* `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.validChoice` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ziyi Dai, Qilin Hou, Zhiyuan Liu, Warut Thawinrak and Hongyu Wang (2026). *Counting Lattice Points in Minkowski Sums of Cross Polytopes*. URL: <https://arxiv.org/abs/2608.16037v2>.

*Commentary.*

validChoice(I,A,q) requires J to be a subset of A; S(i) to be empty for every i outside A minus J; and, for each i in A minus J, S(i) to be nonempty and a subset of I(i) minus Z. The empty selections outside the remaining indices make the data representation unique.

**Definition 1.16 (Acyclic choices).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.feasible`

*Formalization.* `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.feasible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ziyi Dai, Qilin Hou, Zhiyuan Liu, Warut Thawinrak and Hongyu Wang (2026). *Counting Lattice Points in Minkowski Sums of Cross Polytopes*. URL: <https://arxiv.org/abs/2608.16037v2>.

*Commentary.*

feasible(I,A,q) is validChoice together with the requirement that no component C is related to itself by a nonempty finite path of strictRel. In particular, a single strict self-loop is a forbidden cycle. Acyclicity refers to this strict relation on components, rather than to the undirected equality graph.

**Definition 1.17 (Faces counted by actual dimension).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.geometricFaceCount`

*Formalization.* `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.geometricFaceCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ziyi Dai, Qilin Hou, Zhiyuan Liu, Warut Thawinrak and Hongyu Wang (2026). *Counting Lattice Points in Minkowski Sums of Cross Polytopes*. URL: <https://arxiv.org/abs/2608.16037v2>.

*Commentary.*

For arbitrary I, w and natural r, geometricFaceCount(I,w,r) is the natural cardinality of the sets F in Ambient(n) satisfying all three conditions: F is nonempty; F is an exposed subset of actualQ(I,w); and the real finrank of the direction of the affine span of F is r. The zero functional exposes the whole polytope, so it is included. The empty face is excluded and can be assigned its usual separate count one.

**Definition 1.18 (The finite signed sum).**

$$\forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall I \in \operatorname{Fin}\left(m\right) \to \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \forall w \in \operatorname{Fin}\left(m\right) \to \mathbb{R},\; \forall r \in \mathbb{N},\; \operatorname{combinatorialSum}\left(I, w, r\right) = \sum_{q \in \operatorname{RawData}\left(n, m\right)} \operatorname{ite}\left((\operatorname{feasible}\left(I, \operatorname{active}\left(w\right), q\right)) \land (\operatorname{card}\left(\operatorname{support}\left(I, \operatorname{active}\left(w\right)\right)\right) - \operatorname{NatCard}\left(\operatorname{Component}\left(I, \operatorname{active}\left(w\right), q\right)\right) = r), 2^{\operatorname{card}\left(\operatorname{selected}\left(\operatorname{active}\left(w\right), q\right)\right)}, 0\right)$$

*Formalization.* `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.combinatorialSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ziyi Dai, Qilin Hou, Zhiyuan Liu, Warut Thawinrak and Hongyu Wang (2026). *Counting Lattice Points in Minkowski Sums of Cross Polytopes*. URL: <https://arxiv.org/abs/2608.16037v2>.

*Commentary.*

The sum ranges over every q in RawData(n,m). In this formula A = active(w), U = support(I,A), c(q) is the cardinality of Component(I,A,q), and T(q) = selected(A,q). The term is 2 raised to the cardinality of T(q) precisely when q is feasible and d minus c(q) equals r, and is zero otherwise. Subtraction is natural-number subtraction. Each factor two counts the two signs of one selected coordinate. No geometric face or existential normal occurs in the summation criterion.

**Definition 1.19 (Signed component hulls).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.chosenHull`

*Formalization.* `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.chosenHull` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ziyi Dai, Qilin Hou, Zhiyuan Liu, Warut Thawinrak and Hongyu Wang (2026). *Counting Lattice Points in Minkowski Sums of Cross Polytopes*. URL: <https://arxiv.org/abs/2608.16037v2>.

*Commentary.*

For supports I, data q, any real sign function s on Fin n and a summand i, chosenHull(I,q,s,i) equals crossHull(I(i)) if i is in J. Otherwise it is the convex hull of s(j) times e(j) for j in S(i). Realizing faces require s(j) to be either one or minus one only on T; values outside T are irrelevant.

**Definition 1.20 (The signed Minkowski face).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.signedFace`

*Formalization.* `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.signedFace` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ziyi Dai, Qilin Hou, Zhiyuan Liu, Warut Thawinrak and Hongyu Wang (2026). *Counting Lattice Points in Minkowski Sums of Cross Polytopes*. URL: <https://arxiv.org/abs/2608.16037v2>.

*Commentary.*

For I, w, q and s, signedFace(I,w,q,s) is the sum over i in active(w) of w(i) times chosenHull(I,q,s,i). It is a set in the same ambient space as actualQ. For feasible q and signs in {1,-1} on T, the proof produces one common linear functional exposing exactly these component hulls and their actual weighted sum.

**Theorem 1.21 (Complete face-count formula).**

$$\forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall I \in \operatorname{Fin}\left(m\right) \to \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \forall w \in \operatorname{Fin}\left(m\right) \to \mathbb{R},\; \forall r \in \mathbb{N},\; (\forall i \in \operatorname{Fin}\left(m\right),\; \operatorname{Nonempty}\left(\operatorname{I}\left(i\right)\right)) \Rightarrow \left((\forall i \in \operatorname{Fin}\left(m\right),\; 0 \le \operatorname{w}\left(i\right)) \Rightarrow \left((r \le \operatorname{card}\left(\operatorname{support}\left(I, \operatorname{active}\left(w\right)\right)\right)) \Rightarrow \operatorname{geometricFaceCount}\left(I, w, r\right) = \operatorname{combinatorialSum}\left(I, w, r\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.full_cross_polytope_face_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ziyi Dai, Qilin Hou, Zhiyuan Liu, Warut Thawinrak and Hongyu Wang (2026). *Counting Lattice Points in Minkowski Sums of Cross Polytopes*. URL: <https://arxiv.org/abs/2608.16037v2>.

*Commentary.*

For every n and m, every support function I with nonempty I(i), every nonnegative real weight function w, and every natural r at most the cardinality of support(I,active(w)), the actual geometric face count equals the finite signed acyclic-data sum. There is no requirement that weights be strictly positive or distinct, supports be distinct, the incidence graph be connected, or the sum be full-dimensional. Zero-dimensional ambient spaces and empty active sets remain in scope.

A linear functional selects, in each positive-weight summand, either its whole cross polytope at zero support value or the signed coordinate vertices at its positive maximum absolute value. Equal maxima give the equality graph; strictly smaller coordinates give the strict component relation. Conversely, a linear extension of acyclic reachability assigns strictly increasing positive heights to components, and global coordinate signs turn these heights into one common exposing functional. Positivity of the active weights makes equality of the resulting sum faces recover every component face, hence the zero block, selected sets and signs on T.

The direction of the actual affine span has an annihilator consisting of functionals zero on Z whose signed coefficients agree along each equality edge. Its dimension is n minus d plus c: the coordinates outside U are free, and the remaining coefficients form the kernel of the equality graph's real Laplacian. The dual dimension identity gives face dimension d minus c. The resulting dimension-preserving correspondence has exactly 2 raised to the cardinality of T sign choices above each feasible unsigned datum, yielding the sum.

When no weight is positive, the only feasible datum has empty J, empty selections, no vertices and no components; both sides count the unique point face in dimension zero. The datum J = A gives the whole polytope. The usual f-vector adds the empty-face entry one. For a relatively d-dimensional simple polytope, its ordinary h-polynomial follows from the standard transform h(z) = sum over r of f(r) z raised to d-r times (1-z) raised to r. This is the ordinary simple-polytope h-vector, not the Ehrhart h-star polynomial. No simplicity criterion or formula for arbitrary type B generalized permutohedra is asserted.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.Ambient`
- Truth anchor: `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.Component`
- Truth anchor: `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.RawData`
- Truth anchor: `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.Vertex`
- Truth anchor: `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.active`
- Truth anchor: `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.actualQ`
- Truth anchor: `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.chosenHull`
- Truth anchor: `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.combinatorialSum`
- Truth anchor: `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.crossHull`
- Truth anchor: `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.equalityGraph`
- Truth anchor: `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.feasible`
- Truth anchor: `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.full_cross_polytope_face_count`
- Truth anchor: `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.geometricFaceCount`
- Truth anchor: `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.remaining`
- Truth anchor: `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.selected`
- Truth anchor: `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.signedFace`
- Truth anchor: `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.strictRel`
- Truth anchor: `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.support`
- Truth anchor: `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.validChoice`
- Truth anchor: `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.vertexSet`
- Truth anchor: `D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.zeroSet`
- Dependency: [D5/S3/ConceptDynamics/DependencyTopology/DependencyReachabilityOrder](../../ConceptDynamics/DependencyTopology/DependencyReachabilityOrder.md)
