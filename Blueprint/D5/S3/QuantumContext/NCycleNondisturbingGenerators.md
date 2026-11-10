# Generating binary nondisturbing cycle probabilities

## Abstract

Binary nondisturbing cycle tables are convex combinations of deterministic and parity tables.

**Definition 1.1 (Deterministic and parity tables).**

$$\forall \left(n: \mathbb{N}\right), \left(\left(\operatorname{D5.S3.QuantumContext.NCycleNondisturbingGenerators.allGenerators}\left(n\right): \operatorname{Set}\left(\left(\operatorname{Fin}\left(n\right)\right) \to \left(\left(\operatorname{Bool}\right) \to \left(\left(\operatorname{Bool}\right) \to \left(\mathbb{R}\right)\right)\right)\right)\right) = \operatorname{Set.union}\left(\operatorname{Set.range}\left(\lambda \left(s: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Bool}\right)\right) \mapsto \left(\lambda \left(i: \operatorname{Fin}\left(n\right)\right) \mapsto \left(\lambda \left(b: \operatorname{Bool}\right) \mapsto \left(\lambda \left(c: \operatorname{Bool}\right) \mapsto \left(\operatorname{ite}\left(\left(s\left(i\right) = b\right) \land \left(s\left(\operatorname{Equiv.toFun}\left(\operatorname{finRotate}\left(n\right)\right)\left(i\right)\right) = c\right), \left(1: \mathbb{R}\right), \left(0: \mathbb{R}\right)\right)\right)\right)\right)\right)\right), \operatorname{Set.range}\left(\lambda \left(\gamma: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Bool}\right)\right) \mapsto \left(\lambda \left(i: \operatorname{Fin}\left(n\right)\right) \mapsto \left(\lambda \left(b: \operatorname{Bool}\right) \mapsto \left(\lambda \left(c: \operatorname{Bool}\right) \mapsto \left(\operatorname{ite}\left(\operatorname{Bool.xor}\left(b, c\right) = \gamma\left(i\right), \frac{\left(\left(1: \mathbb{R}\right)\right)}{\left(\left(2: \mathbb{R}\right)\right)}, \left(0: \mathbb{R}\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumContext/NCycleNondisturbingGenerators.allGenerators` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each global assignment s, include the table concentrated on s(i) and s(finRotate n i) in context i. For each Boolean edge pattern γ, include the table with probability one half on each outcome pair satisfying b xor c = γ(i), and zero elsewhere. All edge patterns are included, without a parity restriction. This union is a generating set; the definition does not assert that every included table is an extreme point.

**Theorem 1.2 (Every nondisturbing probability table is generated).**

$$\forall \left(n: \mathbb{N}\right), \left(\left(\left(0: \mathbb{N}\right) < n\right) \Rightarrow \left(\forall \left(r: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\left(\operatorname{Bool}\right) \to \left(\left(\operatorname{Bool}\right) \to \left(\mathbb{R}\right)\right)\right)\right), \left(\left(\forall \left(i: \operatorname{Fin}\left(n\right)\right), \left(\forall \left(b: \operatorname{Bool}\right), \left(\forall \left(c: \operatorname{Bool}\right), \left(\left(0: \mathbb{R}\right) \le r\left(i, b, c\right)\right)\right)\right)\right) \Rightarrow \left(\left(\forall \left(i: \operatorname{Fin}\left(n\right)\right), \left(\operatorname{Finset.sum}\left(\left(\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Bool}\right)\right), \lambda \left(b: \operatorname{Bool}\right) \mapsto \left(\operatorname{Finset.sum}\left(\left(\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Bool}\right)\right), \lambda \left(c: \operatorname{Bool}\right) \mapsto \left(r\left(i, b, c\right)\right)\right)\right)\right) = \left(1: \mathbb{R}\right)\right)\right) \Rightarrow \left(\left(\forall \left(i: \operatorname{Fin}\left(n\right)\right), \left(\forall \left(c: \operatorname{Bool}\right), \left(\operatorname{Finset.sum}\left(\left(\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Bool}\right)\right), \lambda \left(b: \operatorname{Bool}\right) \mapsto \left(r\left(i, b, c\right)\right)\right) = \operatorname{Finset.sum}\left(\left(\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Bool}\right)\right), \lambda \left(d: \operatorname{Bool}\right) \mapsto \left(r\left(\operatorname{Equiv.toFun}\left(\operatorname{finRotate}\left(n\right)\right)\left(i\right), c, d\right)\right)\right)\right)\right)\right) \Rightarrow \left(r \in \operatorname{convexHull}\left(\mathbb{R}, \operatorname{D5.S3.QuantumContext.NCycleNondisturbingGenerators.allGenerators}\left(n\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumContext/NCycleNondisturbingGenerators.decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the directed graph with vertices (i,b) and edges (i,b,c) from (i,b) to (finRotate n i,c). Give each forward edge coefficient r(i,b,c)/n and each reverse edge coefficient zero. Nonnegativity of r gives nonnegative coefficients. Each layer has total mass one, so the sum of all coefficients is one. Nondisturbance says precisely that the incoming and outgoing masses agree at every vertex. These coefficients therefore form a normalized circulation.

Decompose this circulation into a finite convex combination of normalized simple closed walks. For a positive-weight term, every reverse-edge multiplicity is zero by the positive_coefficient_forward theorem in LayeredFlow and the edge-multiplicity membership criterion: the original reverse coefficient is zero and every edge of a positive-weight circuit has forward orientation.

A simple closed walk has at most one departure from each vertex. To see this, count departures by counting occurrences of the vertex along the walk, with the terminal occurrence removed, using the outgoingMultiplicity_edgeMultiplicity_concat theorem in SupplierGraph. The list before the terminal edge has no repeated vertex; a repetition would give a forbidden proper positive closed subwalk. Thus each row of the two-by-two edge-count table has sum at most one.

For a walk with no reverse edges, balance at (finRotate n i,c) equates the incoming column sum from layer i to the outgoing row sum in the next layer. The total edge multiplicity per layer is consequently constant, say m, and the walk length is n m. The supplier theorem IsSimpleCycle.length_le_card bounds this length by 2n; together with positive length, this implies that m is either one or two.

When m = 1, exactly one outcome s(i) has a departure in each layer. The next layer's row sums fix the current layer's column sums, so the unique edge in layer i joins s(i) to s(finRotate n i). Multiplying the normalized walk coefficients by n gives the deterministic table of s. When m = 2, both row sums and both column sums are one. Each layer's two-by-two count table is therefore one of the two permutation matrices. Set γ(i) according to whether its false-to-true edge has count one. After division by the walk length 2n and multiplication by n, its table has entries one half exactly when b xor c = γ(i). It is a parity table.

Assign to each positive-weight walk the generating table just obtained. For a zero-weight walk use the deterministic table of the constant false assignment. Every chosen table belongs to allGenerators n. The original weights are nonnegative and sum to one. At each coordinate their weighted sum is n times the forward-edge coefficient r(i,b,c)/n, hence equals r(i,b,c). This gives the required membership in the real convex hull for every n > 0.

## References

- Truth anchor: `D5/S3/QuantumContext/NCycleNondisturbingGenerators.allGenerators`
- Truth anchor: `D5/S3/QuantumContext/NCycleNondisturbingGenerators.decomposition`
- Dependency: [D5/S3/Combinatorics/Circle/Orbit/ZeroIncidence](../Combinatorics/Circle/Orbit/ZeroIncidence.md)
- Dependency: [D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow](../Combinatorics/Graph/LayeredCirculation/LayeredFlow.md)
- Dependency: [D5/S3/Estimation/DecisionRisk/DescentDefectBounds](../Estimation/DecisionRisk/DescentDefectBounds.md)
- Dependency: [D5/S3/Quantum/Entanglement/BinaryDetectionThresholdRefutation](../Quantum/Entanglement/BinaryDetectionThresholdRefutation.md)
