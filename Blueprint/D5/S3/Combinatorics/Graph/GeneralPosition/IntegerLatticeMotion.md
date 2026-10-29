# Integer lattice geometry and serialized translations

## Abstract

Signed-unit integer lattice distances and one common serialized covering trace for scaled finite general-position configurations.

The declarations are in D5.S3.Combinatorics.Graph.GeneralPosition.IntegerLatticeMotion. In the formulas, OnGeodesic denotes CylinderSevenTen.OnGeodesic; Connected, Adj and dist are the SimpleGraph operations; image, univ, card and Nonempty are Finset operations; range is Set.range and natAbs is Int.natAbs. The vertex set consists of integer-valued functions on Fin k. An edge changes one coordinate by one in either direction and leaves every other coordinate fixed. Distances are graph distances in this concrete graph.

**Definition 1.1 (Integer lattice vertices).**

$$\forall k \in \mathrm{Nat},\; \mathrm{Vertex}\left(k\right) = \left(\mathrm{Fin}\left(k\right) \to \mathrm{Int}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeMotion.Vertex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A vertex records all k integer coordinates.

**Definition 1.2 (Exactly one signed unit coordinate change).**

$$\forall k \in \mathrm{Nat},\; \forall x \in \mathrm{Vertex}\left(k\right),\; \forall y \in \mathrm{Vertex}\left(k\right),\; \mathrm{Adj}\left(\mathrm{lattice}\left(k\right), x, y\right) \Leftrightarrow \left(\exists j \in \mathrm{Fin}\left(k\right),\; \left(y\left(j\right) = x\left(j\right) + 1 \lor y\left(j\right) = x\left(j\right) - 1\right) \land \left(\forall i \in \mathrm{Fin}\left(k\right),\; i \ne j \Rightarrow y\left(i\right) = x\left(i\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeMotion.lattice` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The changed coordinate is specified by an existential index. The signed difference is one, and every other coordinate agrees.

**Definition 1.3 (The sum of coordinate distances).**

$$\forall k \in \mathrm{Nat},\; \forall x \in \mathrm{Vertex}\left(k\right),\; \forall y \in \mathrm{Vertex}\left(k\right),\; \mathrm{l1}\left(x, y\right) = \sum_{j : \mathrm{Fin}\left(k\right)} (\mathrm{natAbs}\left(x\left(j\right) - y\left(j\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeMotion.l1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The metric is the sum of integer absolute differences. It is independent of the sup metric supplied by the usual function-space metric instance.

**Theorem 1.4 (Connectivity and exact graph distance).**

$$\forall k \in \mathrm{Nat},\; \mathrm{Connected}\left(\mathrm{lattice}\left(k\right)\right) \land \left(\forall x \in \mathrm{Vertex}\left(k\right),\; \forall y \in \mathrm{Vertex}\left(k\right),\; \mathrm{dist}\left(\mathrm{lattice}\left(k\right), x, y\right) = \mathrm{l1}\left(x, y\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeMotion.lattice_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The distance certificate from WellCoveredPowerCliqueProduct is applied directly. Each edge changes the sum of distances to a target by at most one. A vertex different from the target has a coordinate that can move one unit toward the target and reduce the sum by exactly one. This constructs walks of precisely the claimed length and proves the reverse lower bound.

**Definition 1.5 (Coordinatewise betweenness).**

$$\forall k \in \mathrm{Nat},\; \forall x \in \mathrm{Vertex}\left(k\right),\; \forall y \in \mathrm{Vertex}\left(k\right),\; \forall z \in \mathrm{Vertex}\left(k\right),\; \mathrm{Between}\left(x, y, z\right) \Leftrightarrow \left(\forall j \in \mathrm{Fin}\left(k\right),\; \left(x\left(j\right) \le y\left(j\right) \land y\left(j\right) \le z\left(j\right)\right) \lor \left(z\left(j\right) \le y\left(j\right) \land y\left(j\right) \le x\left(j\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeMotion.Between` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coordinate orientations can differ. In each coordinate the middle value lies between the endpoint values, allowing equality.

**Theorem 1.6 (The coordinate and graph conditions coincide).**

$$\forall k \in \mathrm{Nat},\; \forall x \in \mathrm{Vertex}\left(k\right),\; \forall y \in \mathrm{Vertex}\left(k\right),\; \forall z \in \mathrm{Vertex}\left(k\right),\; \mathrm{Between}\left(x, y, z\right) \Leftrightarrow \mathrm{OnGeodesic}\left(\mathrm{lattice}\left(k\right), x, y, z\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeMotion.between_iff_geodesic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is a consumed bind-only bridge on the live path from scaled_finset_trace through perturb_no_geodesic and mixed_no_geodesic to between_iff_geodesic; it is not independent content. Equality in the sum triangle inequality holds exactly when it holds in every coordinate. The integer absolute-value equality in each coordinate is equivalent to either of the two order orientations.

**Definition 1.7 (One scaled labelled covering trace).**

$$\forall k \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; \forall s \in \mathrm{Fin}\left(m\right) \to \mathrm{Vertex}\left(k\right),\; \forall p \in \mathrm{Nat} \to \left(\mathrm{Fin}\left(m\right) \to \mathrm{Vertex}\left(k\right)\right),\; \mathrm{ScaledCoveringTrace}\left(s, p\right) \Leftrightarrow \left(\left(\forall i \in \mathrm{Fin}\left(m\right),\; p\left(0, i\right) = \operatorname{fun} (j : \mathrm{Fin}\left(k\right)) \mapsto 4 \cdot s\left(i, j\right)\right) \land \left(\left(\forall t \in \mathrm{Nat},\; \mathrm{Injective}\left(p\left(t\right)\right)\right) \land \left(\left(\forall t \in \mathrm{Nat},\; \forall a \in \mathrm{Fin}\left(m\right),\; \forall b \in \mathrm{Fin}\left(m\right),\; \forall c \in \mathrm{Fin}\left(m\right),\; a \ne b \Rightarrow \left(b \ne c \Rightarrow \left(a \ne c \Rightarrow \neg (\mathrm{OnGeodesic}\left(\mathrm{lattice}\left(k\right), p\left(t, a\right), p\left(t, b\right), p\left(t, c\right)\right))\right)\right)\right) \land \left(\left(\forall t \in \mathrm{Nat},\; \exists i \in \mathrm{Fin}\left(m\right),\; \mathrm{Adj}\left(\mathrm{lattice}\left(k\right), p\left(t, i\right), p\left(t + 1, i\right)\right) \land \left(\left(\forall a \in \mathrm{Fin}\left(m\right),\; a \ne i \Rightarrow p\left(t, a\right) = p\left(t + 1, a\right)\right) \land \neg (p\left(t + 1, i\right) \in \mathrm{range}\left(p\left(t\right)\right))\right)\right) \land \left(\forall i \in \mathrm{Fin}\left(m\right),\; \forall x \in \mathrm{Vertex}\left(k\right),\; \exists t \in \mathrm{Nat},\; p\left(t, i\right) = x\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeMotion.ScaledCoveringTrace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The initial positions are four times the original labelled vertices. Positions remain injective and no triple of distinct labels lies on a graph geodesic. At every natural time a single specified label moves along a graph edge into a vertex outside the previous range, and every other label stays fixed. Each fixed label eventually visits every vertex. The same trace serves all targets.

**Theorem 1.8 (A trace for every nonempty finite coordinate general-position set).**

$$\forall k \in \mathrm{Nat},\; 1 \le k \Rightarrow \left(\forall S \in \mathrm{Finset}\left(\mathrm{Vertex}\left(k\right)\right),\; \mathrm{Nonempty}\left(S\right) \Rightarrow \left(\left(\forall a \in \mathrm{Vertex}\left(k\right),\; a \in S \Rightarrow \left(\forall b \in \mathrm{Vertex}\left(k\right),\; b \in S \Rightarrow \left(\forall c \in \mathrm{Vertex}\left(k\right),\; c \in S \Rightarrow \left(a \ne b \Rightarrow \left(b \ne c \Rightarrow \left(a \ne c \Rightarrow \neg (\mathrm{Between}\left(a, b, c\right))\right)\right)\right)\right)\right)\right) \Rightarrow \left(\exists s \in \mathrm{Fin}\left(\mathrm{card}\left(S\right)\right) \to \mathrm{Vertex}\left(k\right),\; \exists p \in \mathrm{Nat} \to \left(\mathrm{Fin}\left(\mathrm{card}\left(S\right)\right) \to \mathrm{Vertex}\left(k\right)\right),\; \mathrm{Injective}\left(s\right) \land \left(\mathrm{image}\left(s, \mathrm{univ}\right) = S \land \mathrm{ScaledCoveringTrace}\left(s, p\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeMotion.scaled_finset_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive dimension, the finite labels enumerate exactly the given nonempty finite set. The one common trace starts at the scaled set 4S, not at the original S. Scaling by four allows each robot an individual coordinate perturbation between minus one and one: any order relation between perturbed coordinates reflects an order relation before perturbation, so coordinate betweenness cannot be created. For each unit translation the robots move one at a time in label order. At time m q plus r, the first r labels have moved from translation q to translation q plus one. The last move of a block moves only the last label. A countable enumeration of lattice vertices is followed by finite distance descent toward successive targets; after reaching a target, a forced positive coordinate edge advances to the next target. Thus repeated enumeration values never introduce a stationary step. At block boundaries all labels have completed the same translation, and surjectivity of the common translation walk makes every fixed robot cover the entire lattice.

The result supplies the complete labelled trace and the exact finite-set enumeration. It does not state the static maximum cardinality or an attained mobile general-position number. Finite occupied sets are obtained as the images of the labels at each time; conversion to the existing CylinderSevenTen.LegalMove relation is a separate finite-configuration obligation.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeMotion.Between`
- Truth anchor: `D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeMotion.ScaledCoveringTrace`
- Truth anchor: `D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeMotion.Vertex`
- Truth anchor: `D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeMotion.between_iff_geodesic`
- Truth anchor: `D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeMotion.l1`
- Truth anchor: `D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeMotion.lattice`
- Truth anchor: `D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeMotion.lattice_distance`
- Truth anchor: `D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeMotion.scaled_finset_trace`
- Dependency: [D5/S3/Combinatorics/Graph/GeneralPosition/CylinderSevenTen](CylinderSevenTen.md)
- Dependency: [D5/S3/Combinatorics/Graph/WellCoveredPowerCliqueProduct](../WellCoveredPowerCliqueProduct.md)
