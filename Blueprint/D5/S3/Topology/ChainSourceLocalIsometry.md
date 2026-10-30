# Local source sheets of an original chain quotient

## Abstract

The original chain quotient preserves every pairwise source distance on a small ball away from the gluing faces.

Let I and J be types in independent universes and X an I-indexed family of extended metric spaces. Write A(X) for their original topological disjoint union. The datum G is the existing FiniteOrbitChainMetric.Datum: its source and target indices, closed gluing domains and ranges, and their partial isometries define the original finite chains and their cost infimum delta(G,a,b). A forward or inverse gluing step costs zero; a move within a piece costs its original extended distance.

Let Y be an extended metric space and q:A(X) to Y realize exactly delta on every pair of representatives. No surjectivity is required. For a in A(X), let i=first(a) and let center(a) be its point in X(i). Write OnBall(q,a,r) for the map from the original source ball eball(center(a),r) to Y which sends x to q(i,x). The radius r below is a nonnegative real, hence finite as an extended real.

**Theorem 1.1 (All pairwise distances on a small source ball).**

$$\forall I \in Types,\; \forall J \in Types,\; \forall X \in I \to Types,\; [\forall i \in I,\; EMetricSpace\left(X\left(i\right)\right)] \forall G \in Datum\left(I, J, X\right),\; \forall Y \in Types,\; [EMetricSpace\left(Y\right)] \forall q \in A\left(X\right) \to Y,\; \forall U \in Set\left(A\left(X\right)\right),\; \forall a \in A\left(X\right),\; \left(\left(\forall a \in A\left(X\right),\; \forall b \in A\left(X\right),\; edist\left(q\left(a\right), q\left(b\right)\right) = delta\left(G, a, b\right)\right) \land \left(IsOpen\left(U\right) \land \left(\left(\forall j \in J,\; \forall y \in dom\left(G, j\right),\; \neg Member\left(Point\left(src\left(G, j\right), y\right), U\right)\right) \land \left(\left(\forall j \in J,\; \forall y \in ran\left(G, j\right),\; \neg Member\left(Point\left(dst\left(G, j\right), y\right), U\right)\right) \land Member\left(a, U\right)\right)\right)\right)\right) \Rightarrow \left(\exists r \in NNReal,\; 0 < r \land Isometry\left(OnBall\left(q, a, r\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/ChainSourceLocalIsometry.original_chain_local_source_isometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

U is open in the original disjoint union. The two exclusions range over every generator j and every point of its actual domain or range. Thus U avoids both endpoints of every permitted gluing step, including inverse steps and self-gluings. The conclusion needs no finiteness of I, J or the full equivalence classes, no compactness, and no finite-diameter condition.

Pull U back to the selected source piece and choose a positive finite R whose ball lies in that pullback. Set r=R/4. A chain starting within r of the center and having cost less than 2r remains within 3r of that center. Prove this by induction on the actual chain: a paid move stays in the original piece and adds at most its cost, while a first forward or inverse gluing would have its current endpoint in U and in a forbidden domain or range. Such a step is impossible.

For two points of the r-ball, their source distance is less than 2r. Any chain cheaper than that distance would satisfy the preceding confinement bound and would have cost at least the same source distance, a contradiction. This bounds the infimum over all original chains from below. The single paid source move bounds it from above, giving equality of every pairwise distance. No minimizing chain or bound on chain length is assumed.

For the literal original quotient furnished by FiniteOrbitChainMetric.Datum.chain_metric_on_original_quotient, take its original projection as q and the metric supplied there. Whenever a source region satisfies these two generator exclusions, the theorem gives its small metric sheet in that same quotient, with the original quotient topology. This application adds no second quotient.

The result concerns source points away from every gluing domain and range. A point on a paired face or an edge does not satisfy this entrance. Such points require compatible charts across the participating pieces and their actual face transports. No global isometric embedding of a whole piece, edge-star cone chart, angle-sum assertion or hyperbolic manifold realization follows from this local statement alone.

## References

- Truth anchor: `D5/S3/Topology/ChainSourceLocalIsometry.original_chain_local_source_isometry`
- Dependency: [D5/S3/Topology/FiniteOrbitChainMetric](FiniteOrbitChainMetric.md)
