# Cuts and midpoints in original chain quotients

## Abstract

Original finite-cost gluing chains admit prescribed-cost cuts, and compact original chain quotients have exact midpoints at finite distance.

Let I and J be types in independent universes, X an I-indexed family of extended metric spaces, and A(X) its topological disjoint union. A datum G supplies closed partial isometries indexed by J, with exactly the original generating relation Step(G), equivalence closure Rel(G), finite chains Chain(G,a,b,c) and chain distance delta(G,a,b). A paid move adds the extended distance inside one piece; a forward or inverse gluing move adds zero. All these notions are those of FiniteOrbitChainMetric.

Write Split(X) for the following property, with no compactness or finiteness assumption: for every i, x,y in X(i), and s in ENNReal, if edist(x,y) is finite and s is at most edist(x,y), there exists z in X(i) with edist(x,z) at most s and edist(z,y) at most edist(x,y)-s. ENNReal denotes the nonnegative reals together with infinity. A geodesic piece satisfies this property, but the property itself is the hypothesis used below.

**Theorem 1.1 (A cut at any finite cumulative cost).**

$$\forall I \in Types,\; \forall J \in Types,\; \forall X \in I \to Types,\; [\forall i \in I,\; EMetricSpace\left(X\left(i\right)\right)] \forall G \in Datum\left(I, J, X\right),\; \forall Y \in Types,\; [EMetricSpace\left(Y\right)] \forall q \in A\left(X\right) \to Y,\; \left(\left(\forall a \in A\left(X\right),\; \forall b \in A\left(X\right),\; edist\left(q\left(a\right), q\left(b\right)\right) = delta\left(G, a, b\right)\right) \land Split\left(X\right)\right) \Rightarrow \left(\forall a \in A\left(X\right),\; \forall b \in A\left(X\right),\; \forall c \in ENNReal,\; \left(Chain\left(G, a, b, c\right) \land c < \infty\right) \Rightarrow \left(\forall s \in ENNReal,\; s \le c \Rightarrow \left(\exists z \in Y,\; edist\left(q\left(a\right), z\right) \le s \land edist\left(z, q\left(b\right)\right) \le c - s\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/FiniteOrbitChainMidpoint.original_chain_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Y is any extended metric space and q:A(X) to Y realizes exactly the original chain distance on representatives. No surjectivity of q is required. The result concerns an actual finite-cost original chain, so c is its paid cost rather than its endpoint distance or an attained infimum.

Induct on the chain. If the prescribed cost s is before the last paid move, keep the point supplied by the prefix and bound the remaining tail by the triangle inequality. Otherwise split that final move at s minus the prefix cost, using Split(X). A zero-cost forward or inverse gluing has equal q-images, so the same cut point works. The empty chain forces s=0. This construction places the cut point in the given target Y throughout.

**Theorem 1.2 (Exact midpoints in the compact original quotient).**

$$\forall I \in Types,\; \forall J \in Types,\; \forall X \in I \to Types,\; [\forall i \in I,\; EMetricSpace\left(X\left(i\right)\right)] [Fintype\left(I\right)] [Fintype\left(J\right)] \forall G \in Datum\left(I, J, X\right),\; \left(\left(\forall i \in I,\; CompactSpace\left(X\left(i\right)\right)\right) \land \left(\left(\forall a \in A\left(X\right),\; Finite\left(Orbit\left(G, a\right)\right)\right) \land Split\left(X\right)\right)\right) \Rightarrow \left(\exists m \in EMetricSpace\left(Q\left(G\right)\right),\; Topology\left(m\right) = quotientTopology\left(G\right) \land \left(\left(\forall a \in A\left(X\right),\; \forall b \in A\left(X\right),\; edist\left(m, q\left(G, a\right), q\left(G, b\right)\right) = delta\left(G, a, b\right)\right) \land \left(\forall a \in Q\left(G\right),\; \forall b \in Q\left(G\right),\; edist\left(m, a, b\right) < \infty \Rightarrow \left(\exists z \in Q\left(G\right),\; edist\left(m, a, z\right) = \frac{edist\left(m, a, b\right)}{2} \land edist\left(m, z, b\right) = \frac{edist\left(m, a, b\right)}{2}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/FiniteOrbitChainMidpoint.compact_original_quotient_midpoints` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here I and J are finite, every X(i) is compact, every full actual Rel(G)-class is finite, and Split(X) holds. Q(G) is the literal Quotient(EqvGen.setoid(Step(G))). Its displayed quotient topology is the original topology of this quotient before the extended metric m is installed. The representative map q(G,a) is the original quotient map. The conclusion supplies one m for the topology equality, chain-distance formula and midpoint assertion simultaneously.

The finite-orbit chain metric gives m with the original topology, so compactness of the original finite disjoint union descends to this same metric quotient. For each positive epsilon and a pair at finite distance, the chain infimum supplies a chain of finite cost below that distance plus epsilon. Cutting the chain halfway gives a point whose two distances are at most half the endpoint distance plus epsilon. There is no assumption of a minimizing chain or a bound on the number of seam crossings.

Minimize z to max(edist(a,z),edist(z,b)) over the compact quotient. Extended distances and their maximum are continuous, including at infinity. The approximate midpoint bounds force this minimum to be at most half the finite endpoint distance. The triangle inequality forces both individual distances to equal that half. The construction only needs a point a after a pair a,b has been selected, so it also covers an empty quotient.

Infinite distances between distinct components are retained. The midpoint assertion only quantifies over pairs with finite distance; it imposes no finite diameter, connectedness or global finite-valued metric. Empty pieces, empty gluing domains, self-gluings, inverse moves and a zero endpoint distance remain included.

The classical complete-midpoint criterion is stated in Bridson and Haefliger, Metric Spaces of Non-Positive Curvature (1999), I.1.4(1); the original disjoint-union chain quotient is described in I.5.18-5.19. The statements here give the prescribed-cost chain cut and exact midpoint stage in the extended metric setting. They do not construct a coherent dyadic family or an isometric real interval, and no novelty claim is made.

For a specified geometric realization one must still identify its original pieces, actual closed partial isometries and full finite equivalence classes with these data, and prove Split(X) for those pieces. The result supplies no identification with a specified marked manifold, no isometric embedding of a whole original piece, and no cone, angle-sum or curvature statement.

## References

- Truth anchor: `D5/S3/Topology/FiniteOrbitChainMidpoint.compact_original_quotient_midpoints`
- Truth anchor: `D5/S3/Topology/FiniteOrbitChainMidpoint.original_chain_cut`
- Dependency: [D5/S3/Topology/FiniteOrbitChainMetric](FiniteOrbitChainMetric.md)
