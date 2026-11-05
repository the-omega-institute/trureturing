# Point-group orbits on face centered cubic shells

## Abstract

The signed coordinate permutation orbits on every contact shell of the face centered cubic lattice have generating function (1−X⁵)/((1−X)(1−X²)²(1−X³)).

**Definition 1.1 (The even-sum lattice).**

$$L = \{x: (\operatorname{Fin}\left(3\right)) \to \mathbb{Z} \mid \operatorname{mod}\left(x\left(0\right) + x\left(1\right) + x\left(2\right), 2\right) = 0\}$$

*Formalization.* `D5/S3/StatisticalMechanics/FccPointGroupShells.L` (`✓ std3`).

*Citation.* J. H. Conway, N. J. A. Sloane (1997). *Low-Dimensional Lattices VII: Coordination Sequences*. DOI: [10.1098/rspa.1997.0126](https://doi.org/10.1098/rspa.1997.0126). URL: <https://doi.org/10.1098/rspa.1997.0126>.

*Commentary.*

Coordinates are indexed by Fin 3, namely zero, one and two. The coordinate sum is even. Here mod denotes integer % (Int.emod), with nonnegative remainder; modulo two the remainder is zero or one. This is the integer realization of the face centered cubic lattice D3.

**Definition 1.2 (The twelve contact steps).**

$$\forall x: L, (\forall y: L, ((\operatorname{SimpleGraph.Adj}\left(contactGraph, x, y\right)) \iff (((\operatorname{abs}\left(\operatorname{val}\left(y\right)\left(0\right) - \operatorname{val}\left(x\right)\left(0\right)\right) = 1) \land ((\operatorname{abs}\left(\operatorname{val}\left(y\right)\left(1\right) - \operatorname{val}\left(x\right)\left(1\right)\right) = 1) \land (\operatorname{val}\left(y\right)\left(2\right) = \operatorname{val}\left(x\right)\left(2\right)))) \lor (((\operatorname{abs}\left(\operatorname{val}\left(y\right)\left(0\right) - \operatorname{val}\left(x\right)\left(0\right)\right) = 1) \land ((\operatorname{val}\left(y\right)\left(1\right) = \operatorname{val}\left(x\right)\left(1\right)) \land (\operatorname{abs}\left(\operatorname{val}\left(y\right)\left(2\right) - \operatorname{val}\left(x\right)\left(2\right)\right) = 1))) \lor ((\operatorname{val}\left(y\right)\left(0\right) = \operatorname{val}\left(x\right)\left(0\right)) \land ((\operatorname{abs}\left(\operatorname{val}\left(y\right)\left(1\right) - \operatorname{val}\left(x\right)\left(1\right)\right) = 1) \land (\operatorname{abs}\left(\operatorname{val}\left(y\right)\left(2\right) - \operatorname{val}\left(x\right)\left(2\right)\right) = 1)))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/FccPointGroupShells.contactGraph` (`✓ std3`).

*Citation.* J. H. Conway, N. J. A. Sloane (1997). *Low-Dimensional Lattices VII: Coordination Sequences*. DOI: [10.1098/rspa.1997.0126](https://doi.org/10.1098/rspa.1997.0126). URL: <https://doi.org/10.1098/rspa.1997.0126>.

*Commentary.*

An edge changes exactly two distinct coordinates by one in absolute value and fixes the third. Each of the three choices of a coordinate pair has four sign choices. Both endpoints belong to the lattice.

**Definition 1.3 (The specified center).**

$$\forall i: \operatorname{Fin}\left(3\right), (\operatorname{val}\left(origin\right)\left(i\right) = 0)$$

*Formalization.* `D5/S3/StatisticalMechanics/FccPointGroupShells.origin` (`✓ std3`).

*Citation.* J. H. Conway, N. J. A. Sloane (1997). *Low-Dimensional Lattices VII: Coordination Sequences*. DOI: [10.1098/rspa.1997.0126](https://doi.org/10.1098/rspa.1997.0126). URL: <https://doi.org/10.1098/rspa.1997.0126>.

*Commentary.*

The center has all three coordinates zero.

**Definition 1.4 (Shortest-walk distance).**

$$\forall x: L, (\operatorname{d}\left(x\right) = \operatorname{SimpleGraph.dist}\left(contactGraph, origin, x\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/FccPointGroupShells.d` (`✓ std3`).

*Citation.* J. H. Conway, N. J. A. Sloane (1997). *Low-Dimensional Lattices VII: Coordination Sequences*. DOI: [10.1098/rspa.1997.0126](https://doi.org/10.1098/rspa.1997.0126). URL: <https://doi.org/10.1098/rspa.1997.0126>.

*Commentary.*

Distance is SimpleGraph.dist in the stated contact graph, the minimum walk length. The construction of paths below shows every vertex is reachable from the origin.

**Definition 1.5 (All signed coordinate permutations).**

$$\forall w: \operatorname{Perm}\left((\operatorname{Fin}\left(3\right)) \to \mathbb{Z}\right), ((w \in W) \iff (\exists p: \operatorname{Perm}\left(\operatorname{Fin}\left(3\right)\right), (\exists s: (\operatorname{Fin}\left(3\right)) \to \mathbb{Z}, ((\forall i: \operatorname{Fin}\left(3\right), ((s\left(i\right) = 1) \lor (s\left(i\right) = 0 - 1))) \land (\forall x: (\operatorname{Fin}\left(3\right)) \to \mathbb{Z}, (\forall i: \operatorname{Fin}\left(3\right), (w\left(x\right)\left(i\right) = s\left(i\right) \cdot x\left(p\left(i\right)\right))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/FccPointGroupShells.W` (`✓ std3`).

*Citation.* J. H. Conway, N. J. A. Sloane (1997). *Low-Dimensional Lattices VII: Coordination Sequences*. DOI: [10.1098/rspa.1997.0126](https://doi.org/10.1098/rspa.1997.0126). URL: <https://doi.org/10.1098/rspa.1997.0126>.

*Commentary.*

The group consists of all signed coordinate permutations, acting on integer triples by the displayed formula. The lattice is invariant: changing a sign preserves a coordinate modulo two, and permuting coordinates preserves their sum. The restricted action is literal evaluation of the same signed permutation. All reflections are included.

**Definition 1.6 (The restricted signed-permutation action).**

$$\forall w: W, (\forall x: L, (\operatorname{val}\left(\operatorname{smul}\left(w, x\right)\right) = \operatorname{val}\left(w\right)\left(\operatorname{val}\left(x\right)\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/FccPointGroupShells.latticeAction` (`✓ std3`).

*Citation.* J. H. Conway, N. J. A. Sloane (1997). *Low-Dimensional Lattices VII: Coordination Sequences*. DOI: [10.1098/rspa.1997.0126](https://doi.org/10.1098/rspa.1997.0126). URL: <https://doi.org/10.1098/rspa.1997.0126>.

*Commentary.*

Here smul(w,x) denotes w acting on x, and val is the underlying value of a subtype. The displayed equation defines the action by evaluating the underlying permutation on the underlying integer triple. Its value lies in L because signed permutations preserve the parity of the coordinate sum.

**Definition 1.7 (A shell at any natural radius).**

$$\forall n: \mathbb{N}, (\operatorname{Shell}\left(n\right) = \{x: L \mid \operatorname{d}\left(x\right) = n\})$$

*Formalization.* `D5/S3/StatisticalMechanics/FccPointGroupShells.Shell` (`✓ std3`).

*Citation.* J. H. Conway, N. J. A. Sloane (1997). *Low-Dimensional Lattices VII: Coordination Sequences*. DOI: [10.1098/rspa.1997.0126](https://doi.org/10.1098/rspa.1997.0126). URL: <https://doi.org/10.1098/rspa.1997.0126>.

*Commentary.*

The radius is any natural number, including zero.

**Definition 1.8 (The number of orbits on a shell).**

$$\forall n: \mathbb{N}, (\operatorname{A}\left(n\right) = \operatorname{Nat.card}\left(\operatorname{Quotient}\left(\operatorname{Setoid.comap}\left((\operatorname{Subtype.val}: (\operatorname{Shell}\left(n\right)) \to L), \operatorname{MulAction.orbitRel}\left(W, L\right)\right)\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/FccPointGroupShells.A` (`✓ std3`).

*Citation.* J. H. Conway, N. J. A. Sloane (1997). *Low-Dimensional Lattices VII: Coordination Sequences*. DOI: [10.1098/rspa.1997.0126](https://doi.org/10.1098/rspa.1997.0126). URL: <https://doi.org/10.1098/rspa.1997.0126>.

*Commentary.*

Restrict the orbit equivalence relation of the action on L to Shell n, and take the natural cardinality of its quotient. The distance formula shows the shells are invariant and finite. Sorting absolute coordinates is a theorem about this quotient and supplies no part of its definition.

**Theorem 1.9 (The formal generating-function identity).**

$$(1 - \operatorname{PowerSeries.X}) \cdot (1 - \operatorname{PowerSeries.X}^{2})^{2} \cdot (1 - \operatorname{PowerSeries.X}^{3}) \cdot \operatorname{PowerSeries.mk}\left(\lambda n \mapsto (\operatorname{A}\left(n\right): \mathbb{Z})\right) = 1 - \operatorname{PowerSeries.X}^{5}$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/FccPointGroupShells.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. H. Conway, N. J. A. Sloane (1997). *Low-Dimensional Lattices VII: Coordination Sequences*. DOI: [10.1098/rspa.1997.0126](https://doi.org/10.1098/rspa.1997.0126). URL: <https://doi.org/10.1098/rspa.1997.0126>.

*Commentary.*

Let the absolute coordinates be sorted as c ≤ b ≤ a. Signed permutations preserve this sorted tuple, and any two integer triples with the same tuple are related by one signed permutation. Every orbit therefore has precisely one nonnegative sorted representative with even coordinate sum.

Define a potential as the maximum of the largest absolute coordinate and half the sum of the three absolute coordinates, with natural floor division. Each contact step changes the largest absolute coordinate by at most one and the sum by at most two. The potential consequently gives a lower bound for walk length from zero.

For a nonnegative sorted representative, decrease the two largest coordinates by one when the middle coordinate is positive. Otherwise the smallest and middle coordinates are zero. If the potential is positive, the largest coordinate is at least two and even; decrease it by one and increase the middle coordinate to one. These steps decrease the potential by exactly one. Transport them by signed permutations and use strong induction to obtain a walk whose length equals the potential. Thus the graph distance is max(a,(a+b+c)/2).

If a ≥ b+c, put u=b−c and t=(a−b−c)/2. This gives a unique triple of natural numbers with (a,b,c)=(2c+u+2t,c+u,c) and distance 2c+u+2t. If a<b+c, put p=(b+c−a)/2, q=(a+c−b)/2 and r=(a+b−c)/2. The even sum and triangle inequality give 1≤p≤q≤r. Write p=1+i, q=p+j and r=q+k. The distance is 3+3i+2j+k. The two cases are disjoint and exhaust all representatives.

Counting fibers of a sum of two weights corresponds to multiplying their formal series: separate the fiber by the two weights, whose sum is the required coefficient index. A natural variable with weight w contributes the geometric series in X to the power w. The first region has weights 2,1,2; the second has weights 3,2,1 and an initial shift of three. Clearing the common denominator leaves (1−X³)+X³(1−X²)=1−X⁵. The coefficients and the identity are over the integers, with no convergence condition. At radius zero the first region contributes its zero triple.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/FccPointGroupShells.A`
- Truth anchor: `D5/S3/StatisticalMechanics/FccPointGroupShells.L`
- Truth anchor: `D5/S3/StatisticalMechanics/FccPointGroupShells.Shell`
- Truth anchor: `D5/S3/StatisticalMechanics/FccPointGroupShells.W`
- Truth anchor: `D5/S3/StatisticalMechanics/FccPointGroupShells.contactGraph`
- Truth anchor: `D5/S3/StatisticalMechanics/FccPointGroupShells.d`
- Truth anchor: `D5/S3/StatisticalMechanics/FccPointGroupShells.latticeAction`
- Truth anchor: `D5/S3/StatisticalMechanics/FccPointGroupShells.origin`
- Truth anchor: `D5/S3/StatisticalMechanics/FccPointGroupShells.result`
- Dependency: [D5/S3/Combinatorics/PositionSets/VertexPositionRatioRefutation](../Combinatorics/PositionSets/VertexPositionRatioRefutation.md)
