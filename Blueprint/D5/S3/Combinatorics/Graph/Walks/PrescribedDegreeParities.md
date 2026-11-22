# Prescribed degree parities

## Abstract

Vertex degree parity prescriptions on finite connected graphs.

**Theorem 1.1 (A prescribed odd-degree set has even cardinality).**

$$\forall V \in \operatorname{FiniteVertexType}\left(\right),\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \operatorname{Connected}\left(G\right) \Rightarrow \left(\forall d \in \operatorname{VertexLabelling}\left(V, \operatorname{ZMod}\left(2\right)\right),\; \left(\exists H \in \operatorname{SimpleGraph}\left(V\right),\; \operatorname{Subgraph}\left(H, G\right) \land \left(\forall v \in V,\; \operatorname{DegreeModTwo}\left(H, v\right) = \operatorname{d}\left(v\right)\right)\right) \Leftrightarrow \operatorname{Total}\left(d\right) = 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/PrescribedDegreeParities.exact_parity_subgraph` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

V is a finite vertex type and G is a connected simple graph. VertexLabelling assigns an element of ZMod(2) to each vertex, Total sums these labels, and DegreeModTwo casts the cardinality of the neighbour set to ZMod(2). Subgraph is the edge inclusion relation on simple graphs with the same vertex type.

The handshaking identity gives the zero-sum condition. For the converse, the two endpoints of a walk are the boundary of the sum of its edges over ZMod(2), since internal incidences cancel in pairs. Taking walks to one root with coefficients given by the prescription cancels the root term because the total is zero. Select the edges with coefficient one. Their incidence vector is the prescribed degree parity.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/PrescribedDegreeParities.exact_parity_subgraph`
