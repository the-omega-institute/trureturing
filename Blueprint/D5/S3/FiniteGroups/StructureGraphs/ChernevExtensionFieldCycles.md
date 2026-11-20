# Directed structure-graph cycles over finite extension fields

## Abstract

A finite field of order p to the n with p prime, n greater than one and order different from four has a nontrivial directed structure-graph cycle.

**Definition 1.1 (The sum-and-product successor).**

$$\forall R \in Type*,\; [\operatorname{Ring}\left(R\right)], \forall a \in R,\; \forall b \in R,\; \operatorname{phi}\left((a, b)\right) = (a+b, a \cdot b)$$

*Formalization.* `D5/S3/FiniteGroups/StructureGraphs/ChernevExtensionFieldCycles.phi` (`✓ std3`).

*Citation.* Andrey M. Chernev, Nikolay A. Chernev (2026). *On the Connected Components of Structure Graphs of Associative Rings*. DOI: [10.48550/arXiv.2611.07521](https://doi.org/10.48550/arXiv.2611.07521). URL: <https://arxiv.org/abs/2611.07521v1>.

*Commentary.*

Definition 3.1 directs an edge from (a, b) to (a + b, ab). The multiplication keeps the order of the two inputs.

**Definition 1.2 (The directed structure graph).**

$$\forall R \in Type*,\; [\operatorname{Ring}\left(R\right)], \forall v \in R \times R,\; \forall w \in R \times R,\; \operatorname{Adj}\left(\operatorname{structureGraph}\left(R\right), v, w\right) \Leftrightarrow \operatorname{phi}\left(v\right) = w$$

*Formalization.* `D5/S3/FiniteGroups/StructureGraphs/ChernevExtensionFieldCycles.structureGraph` (`✓ std3`).

*Citation.* Andrey M. Chernev, Nikolay A. Chernev (2026). *On the Connected Components of Structure Graphs of Associative Rings*. DOI: [10.48550/arXiv.2611.07521](https://doi.org/10.48550/arXiv.2611.07521). URL: <https://arxiv.org/abs/2611.07521v1>.

*Commentary.*

Definition 3.1 uses ordered pairs as vertices. The adjacency relation permits self-loops.

**Definition 1.3 (A closed directed cycle).**

$$\forall V \in Type*,\; \forall G \in \operatorname{Digraph}\left(V\right),\; \forall r \in \mathbb{N},\; \forall v \in (\operatorname{Fin}\left(r\right) \to V),\; \operatorname{IsDirectedCycle}\left(G, r, v\right) \Leftrightarrow (0 < r \land \operatorname{Injective}\left(v\right) \land (\forall i \in \operatorname{Fin}\left(r\right),\; \forall j \in \operatorname{Fin}\left(r\right),\; \operatorname{val}\left(j\right) = \operatorname{mod}\left(\operatorname{val}\left(i\right)+1, r\right) \Rightarrow \operatorname{Adj}\left(G, v\left(i\right), v\left(j\right)\right)))$$

*Formalization.* `D5/S3/FiniteGroups/StructureGraphs/ChernevExtensionFieldCycles.IsDirectedCycle` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrey M. Chernev, Nikolay A. Chernev (2026). *On the Connected Components of Structure Graphs of Associative Rings*. DOI: [10.48550/arXiv.2611.07521](https://doi.org/10.48550/arXiv.2611.07521). URL: <https://arxiv.org/abs/2611.07521v1>.

*Commentary.*

The indices range from zero to r − 1. Injectivity makes the vertices distinct, and reducing the successor modulo r includes the edge from the last vertex to the first.

**Definition 1.4 (Chernev–Chernev Hypothesis 6.1).**

$$\forall K \in Type,\; [\operatorname{Field}\left(K\right)], [\operatorname{Fintype}\left(K\right)], \forall p \in \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{Prime}\left(p\right) \Rightarrow 1 < n \Rightarrow \operatorname{card}\left(K\right) = p^{n} \Rightarrow \operatorname{card}\left(K\right) \ne 4 \Rightarrow \exists r \in \mathbb{N},\; \exists v \in (\operatorname{Fin}\left(r\right) \to K \times K),\; 1 < r \land \operatorname{IsDirectedCycle}\left(\operatorname{structureGraph}\left(K\right), r, v\right)$$

*Formalization.* `D5/S3/FiniteGroups/StructureGraphs/ChernevExtensionFieldCycles.claim` (`✓ std3`).

*Citation.* Andrey M. Chernev, Nikolay A. Chernev (2026). *On the Connected Components of Structure Graphs of Associative Rings*. DOI: [10.48550/arXiv.2611.07521](https://doi.org/10.48550/arXiv.2611.07521). URL: <https://arxiv.org/abs/2611.07521v1>.

*Commentary.*

Hypothesis 6.1, p. 8, reads “The structure graph of a Galois field of extension degree > 1 different from GF (4) contains a cycle of length > 1.” The field K is arbitrary. Its cardinality is p to the n, where p is prime and n is the degree over the prime field.

**Theorem 1.5 (The universal cycle-existence theorem).**

$$\forall K \in Type,\; [\operatorname{Field}\left(K\right)], [\operatorname{Fintype}\left(K\right)], \forall p \in \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{Prime}\left(p\right) \Rightarrow 1 < n \Rightarrow \operatorname{card}\left(K\right) = p^{n} \Rightarrow \operatorname{card}\left(K\right) \ne 4 \Rightarrow \exists r \in \mathbb{N},\; \exists v \in (\operatorname{Fin}\left(r\right) \to K \times K),\; 1 < r \land \operatorname{IsDirectedCycle}\left(\operatorname{structureGraph}\left(K\right), r, v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/StructureGraphs/ChernevExtensionFieldCycles.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrey M. Chernev, Nikolay A. Chernev (2026). *On the Connected Components of Structure Graphs of Associative Rings*. DOI: [10.48550/arXiv.2611.07521](https://doi.org/10.48550/arXiv.2611.07521). URL: <https://arxiv.org/abs/2611.07521v1>.

*Commentary.*

Two steps from (−1, x) give (−1, x − x²) in every characteristic. A nonzero periodic point of x ↦ x − x² gives a nonfixed periodic vertex. Listing its orbit through one minimal period yields distinct vertices and the closing edge. In an odd-degree extension, a point whose image lies in the prime field has minimal polynomial of degree at most two. Its degree divides the extension degree and hence is one. The complement of the prime field is therefore invariant, finite and nonempty. In odd characteristic and even degree the quadratic subfield contains a square root of −1, which gives a four-cycle. In characteristic two the degree is greater than two. An odd prime divisor of the degree gives an odd-degree subfield, and divisibility by four gives a subfield of order sixteen. In that subfield a root of X⁴ + X + 1 supplies polynomial coordinates for an explicit eight-cycle. Field embeddings preserve the successor and distinctness. The finite-field isomorphism given by equality of cardinalities transports the cycle to K.

## References

- Truth anchor: `D5/S3/FiniteGroups/StructureGraphs/ChernevExtensionFieldCycles.IsDirectedCycle`
- Truth anchor: `D5/S3/FiniteGroups/StructureGraphs/ChernevExtensionFieldCycles.claim`
- Truth anchor: `D5/S3/FiniteGroups/StructureGraphs/ChernevExtensionFieldCycles.phi`
- Truth anchor: `D5/S3/FiniteGroups/StructureGraphs/ChernevExtensionFieldCycles.result`
- Truth anchor: `D5/S3/FiniteGroups/StructureGraphs/ChernevExtensionFieldCycles.structureGraph`
- Dependency: [D5/S3/ObserverMemory/Prediction/FiniteOrbitPeriodBound](../../ObserverMemory/Prediction/FiniteOrbitPeriodBound.md)
