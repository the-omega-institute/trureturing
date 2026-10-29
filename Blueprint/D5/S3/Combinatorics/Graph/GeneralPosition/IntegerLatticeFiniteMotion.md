# Finite configurations and infinite mobility

## Abstract

Finite occupied configurations on the infinite integer lattice, with one common infinite legal covering trajectory after scaling by four.

The signed-unit lattice has vertices Fin k to Int. Its edges change exactly one coordinate by one in either direction. General position and legal moves use CylinderSevenTen.IsGeneralPosition and CylinderSevenTen.LegalMove in this actual graph.

**Definition 1.1 (One common infinite trajectory).**

$$\forall V \in \mathrm{Type},\; [\mathrm{DecidableEq}\left(V\right)] \forall G \in \mathrm{SimpleGraph}\left(V\right),\; \forall S \in \mathrm{Finset}\left(V\right),\; \mathrm{IsInfinitelyMobile}\left(G, S\right) \Leftrightarrow \left(\operatorname{CylinderSevenTen.IsGeneralPosition}\left(G, S\right) \land \left(\exists c \in \mathrm{Nat} \to \mathrm{Finset}\left(V\right),\; c\left(0\right) = S \land \left(\left(\forall t \in \mathrm{Nat},\; \operatorname{CylinderSevenTen.LegalMove}\left(G, c\left(t\right), c\left(t + 1\right)\right)\right) \land \left(\left(\forall t \in \mathrm{Nat},\; \operatorname{CylinderSevenTen.IsGeneralPosition}\left(G, c\left(t\right)\right)\right) \land \left(\left(\forall x \in V,\; \exists t \in \mathrm{Nat},\; x \in c\left(t\right)\right) \land \left(\forall t \in \mathrm{Nat},\; \operatorname{Finset.card}\left(c\left(t\right)\right) = \operatorname{Finset.card}\left(S\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeFiniteMotion.IsInfinitelyMobile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite configuration is initially in graph general position. There is one function c from natural times to finite configurations, starting at that configuration, with a legal move at every step. Every c(t) is in graph general position, every vertex belongs to some c(t) at a finite time, and every c(t) has the initial cardinality. The existential quantifier for c precedes the universal quantifier over target vertices. No finiteness assumption is imposed on the graph's vertex type.

**Theorem 1.2 (Scaled coordinate general position gives finite-configuration mobility).**

$$\forall k \in \mathrm{Nat},\; 1 \le k \Rightarrow \left(\forall S \in \mathrm{Finset}\left(\operatorname{IntegerLatticeMotion.Vertex}\left(k\right)\right),\; \operatorname{Finset.Nonempty}\left(S\right) \Rightarrow \left(\left(\forall a \in \operatorname{IntegerLatticeMotion.Vertex}\left(k\right),\; a \in S \Rightarrow \left(\forall b \in \operatorname{IntegerLatticeMotion.Vertex}\left(k\right),\; b \in S \Rightarrow \left(\forall c \in \operatorname{IntegerLatticeMotion.Vertex}\left(k\right),\; c \in S \Rightarrow \left(a \ne b \Rightarrow \left(b \ne c \Rightarrow \left(a \ne c \Rightarrow \neg (\operatorname{IntegerLatticeMotion.Between}\left(a, b, c\right))\right)\right)\right)\right)\right)\right) \Rightarrow \left(\mathrm{IsInfinitelyMobile}\left(\operatorname{IntegerLatticeMotion.lattice}\left(k\right), \operatorname{Finset.image}\left(\operatorname{fun} (x : \operatorname{IntegerLatticeMotion.Vertex}\left(k\right)) \mapsto \operatorname{fun} (j : \mathrm{Fin}\left(k\right)) \mapsto 4 \cdot x\left(j\right), S\right)\right) \land \operatorname{Finset.card}\left(\operatorname{Finset.image}\left(\operatorname{fun} (x : \operatorname{IntegerLatticeMotion.Vertex}\left(k\right)) \mapsto \operatorname{fun} (j : \mathrm{Fin}\left(k\right)) \mapsto 4 \cdot x\left(j\right), S\right)\right) = \operatorname{Finset.card}\left(S\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeFiniteMotion.scaled_finset_mobile` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive dimension and every nonempty finite coordinate general-position set S, its image under multiplication of every coordinate by four is infinitely mobile. The scaled image has exactly S.card vertices, so the common trajectory also has exactly S.card occupied vertices at every time.

Take the single labelled trace supplied by IntegerLatticeMotion.scaled_finset_trace and let c(t) be the image of all labels at time t. Its initial image is exactly the fourfold image of S. Apply the original CylinderSevenTen.labelled_gp to obtain graph general position and CylinderSevenTen.labelled_move to obtain the exact one-robot legal transition. The injectivity and unchanged-label clauses ensure that the moved robot enters an unoccupied vertex. Apply CylinderSevenTen.configuration_card to preserve the exact number of occupied vertices. Nonemptiness supplies a fixed label, whose coverage of every vertex proves coverage by this same finite-configuration trajectory.

The trajectory starts at the scaled image. No trajectory from S to that image is asserted. The statement has no static cardinality optimum as a hypothesis or conclusion, and uses neither a finite box nor a finite traversal duration.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeFiniteMotion.IsInfinitelyMobile`
- Truth anchor: `D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeFiniteMotion.scaled_finset_mobile`
- Dependency: [D5/S3/Combinatorics/Graph/GeneralPosition/CylinderSevenTen](CylinderSevenTen.md)
- Dependency: [D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeMotion](IntegerLatticeMotion.md)
