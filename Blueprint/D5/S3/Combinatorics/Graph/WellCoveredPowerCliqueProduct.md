# Well-covered powers with unbounded diameter

## Abstract

Cartesian products with a sufficiently large clique preserve well-covered powers and increase the diameter by one. Starting from the seven-cycle gives arbitrary diameters at least three.

**Definition 1.1 (Graph powers).**

$$\forall V \in \mathrm{Type},\; [\operatorname{Fintype}\left(V\right)], [\operatorname{DecidableEq}\left(V\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall d \in \mathrm{Nat},\; \forall u \in V,\; \forall v \in V,\; \operatorname{Adj}\left(\operatorname{power}\left(G, d\right), u, v\right) \Leftrightarrow \left(u \ne v \land \operatorname{dist}\left(G, u, v\right) \le d\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/WellCoveredPowerCliqueProduct.power` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The d-th power joins distinct vertices whose graph distance is at most d. Only connected finite graphs are used.

**Definition 1.2 (Maximal independent finite sets).**

$$\forall V \in \mathrm{Type},\; [\operatorname{Fintype}\left(V\right)], [\operatorname{DecidableEq}\left(V\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall I \in \operatorname{Finset}\left(V\right),\; \operatorname{IsMaximalIndep}\left(G, I\right) \Leftrightarrow \left(\left(\forall u \in V,\; \operatorname{mem}\left(u, I\right) \Rightarrow \left(\forall v \in V,\; \left(\operatorname{mem}\left(v, I\right) \land u \ne v\right) \Rightarrow \left(\neg \operatorname{Adj}\left(G, u, v\right)\right)\right)\right) \land \left(\forall v \in V,\; \left(\neg \operatorname{mem}\left(v, I\right)\right) \Rightarrow \left(\exists u \in V,\; \operatorname{mem}\left(u, I\right) \land \operatorname{Adj}\left(G, v, u\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/WellCoveredPowerCliqueProduct.IsMaximalIndep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The set is independent and every vertex outside it has a neighbor inside it. This is precisely maximality under inclusion.

**Definition 1.3 (Well-covered graphs).**

$$\forall V \in \mathrm{Type},\; [\operatorname{Fintype}\left(V\right)], [\operatorname{DecidableEq}\left(V\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \operatorname{WellCovered}\left(G\right) \Leftrightarrow \left(\forall I \in \operatorname{Finset}\left(V\right),\; \forall J \in \operatorname{Finset}\left(V\right),\; \left(\operatorname{IsMaximalIndep}\left(G, I\right) \land \operatorname{IsMaximalIndep}\left(G, J\right)\right) \Rightarrow \operatorname{card}\left(I\right) = \operatorname{card}\left(J\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/WellCoveredPowerCliqueProduct.WellCovered` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Any two maximal independent finite sets have equal cardinalities, equivalently all minimal vertex covers have the same cardinality.

**Definition 1.4 (Connected graphs with well-covered powers).**

$$\forall V \in \mathrm{Type},\; [\operatorname{Fintype}\left(V\right)], [\operatorname{DecidableEq}\left(V\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \operatorname{WCP}\left(G\right) \Leftrightarrow \left(\operatorname{Connected}\left(G\right) \land \left(\forall d \in \mathrm{Nat},\; 1 \le d \Rightarrow \operatorname{WellCovered}\left(\operatorname{power}\left(G, d\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/WellCoveredPowerCliqueProduct.WCP` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The graph is connected and its d-th power is well-covered for every positive integer d.

**Theorem 1.5 (Distance in a clique product).**

$$\forall V \in \mathrm{Type},\; [\operatorname{Fintype}\left(V\right)], [\operatorname{DecidableEq}\left(V\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall t \in \mathrm{Nat},\; \operatorname{Connected}\left(G\right) \Rightarrow \left(\forall x \in \operatorname{Prod}\left(V, \operatorname{Fin}\left(t\right)\right),\; \forall y \in \operatorname{Prod}\left(V, \operatorname{Fin}\left(t\right)\right),\; \operatorname{dist}\left(\operatorname{boxProd}\left(G, \operatorname{completeGraph}\left(\operatorname{Fin}\left(t\right)\right)\right), x, y\right) = \operatorname{dist}\left(G, \operatorname{fst}\left(x\right), \operatorname{fst}\left(y\right)\right) + \operatorname{if}\left(\operatorname{snd}\left(x\right) = \operatorname{snd}\left(y\right), 0, 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/WellCoveredPowerCliqueProduct.distance_cliqueProduct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In G □ K_t the distance from (u,a) to (v,b) is dist_G(u,v) plus zero when a=b and one otherwise.

**Theorem 1.6 (Maximality survives projection).**

$$\forall V \in \mathrm{Type},\; [\operatorname{Fintype}\left(V\right)], [\operatorname{DecidableEq}\left(V\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall t \in \mathrm{Nat},\; \forall d \in \mathrm{Nat},\; \forall I \in \operatorname{Finset}\left(\operatorname{Prod}\left(V, \operatorname{Fin}\left(t\right)\right)\right),\; \left(\operatorname{Connected}\left(G\right) \land \left(\operatorname{LT}\left(\operatorname{FintypeCard}\left(V\right), t\right) \land \left(1 \le d \land \operatorname{IsMaximalIndep}\left(\operatorname{power}\left(\operatorname{boxProd}\left(G, \operatorname{completeGraph}\left(\operatorname{Fin}\left(t\right)\right)\right), d\right), I\right)\right)\right)\right) \Rightarrow \operatorname{IsMaximalIndep}\left(\operatorname{power}\left(G, d - 1\right), \operatorname{imageFst}\left(I\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/WellCoveredPowerCliqueProduct.projection_maximal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For d at least one and t greater than the number of vertices of G, a maximal independent set of (G □ K_t)^d projects to a maximal independent set of G^(d-1). If an omitted base vertex could be added, choose a clique label absent from the original set. Its distance to every selected point is then greater than d, contradicting maximality.

**Theorem 1.7 (Clique products preserve well-covered powers).**

$$\forall V \in \mathrm{Type},\; [\operatorname{Fintype}\left(V\right)], [\operatorname{DecidableEq}\left(V\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall t \in \mathrm{Nat},\; \left(\operatorname{WCP}\left(G\right) \land \operatorname{LT}\left(\operatorname{FintypeCard}\left(V\right), t\right)\right) \Rightarrow \operatorname{WCP}\left(\operatorname{boxProd}\left(G, \operatorname{completeGraph}\left(\operatorname{Fin}\left(t\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/WellCoveredPowerCliqueProduct.wcp_cliqueProduct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G be a finite connected graph all of whose positive powers are well-covered. If t exceeds its order, then G □ K_t also has this property. Projection is injective on each independent set and preserves cardinality. The zero-th power is edgeless and has a single maximal independent set.

**Theorem 1.8 (Clique products increase diameter).**

$$\forall V \in \mathrm{Type},\; [\operatorname{Fintype}\left(V\right)], [\operatorname{DecidableEq}\left(V\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall t \in \mathrm{Nat},\; \left(\operatorname{Connected}\left(G\right) \land 2 \le t\right) \Rightarrow \operatorname{diam}\left(\operatorname{boxProd}\left(G, \operatorname{completeGraph}\left(\operatorname{Fin}\left(t\right)\right)\right)\right) = \operatorname{diam}\left(G\right) + 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/WellCoveredPowerCliqueProduct.diam_cliqueProduct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If t is at least two, the diameter of G □ K_t is diam(G)+1. A pair attaining diam(G), equipped with two different clique labels, attains this bound.

**Theorem 1.9 (The seven-cycle has well-covered powers).**

$$\operatorname{WCP}\left(\operatorname{cycle}\left(7\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/WellCoveredPowerCliqueProduct.cycle_seven_wcp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cyclic distance on Fin 7 is min(|u-v|,7-|u-v|). It gives the seven-cycle. The maximal independent sets of its first, second and third powers have cardinalities three, two and one. All higher powers equal the third.

**Theorem 1.10 (Every diameter at least three occurs).**

$$\forall D \in \mathrm{Nat},\; 3 \le D \Rightarrow \left(\exists V \in \mathrm{Type},\; \exists [\operatorname{Fintype}\left(V\right)], \exists [\operatorname{DecidableEq}\left(V\right)], \exists G \in \operatorname{SimpleGraph}\left(V\right),\; \operatorname{WCP}\left(G\right) \land \operatorname{diam}\left(G\right) = D\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/WellCoveredPowerCliqueProduct.exists_wcp_diameter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural number D at least three there exists a finite connected graph with well-covered positive powers and diameter D. The initial graph is the seven-cycle. At each step take the Cartesian product with the clique of order one greater than the current graph's order.

**Definition 1.11 (The proposed diameter bound).**

$$claim \Leftrightarrow \left(\forall V \in \mathrm{Type},\; [\operatorname{Fintype}\left(V\right)], [\operatorname{DecidableEq}\left(V\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)], \operatorname{WCP}\left(G\right) \Rightarrow \operatorname{diam}\left(G\right) \le 3\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/WellCoveredPowerCliqueProduct.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Question 3.9 asks: Let G be a simple connected graph such that G^d is well-covered for all d at least one. Is it true that diam(G) is at most three? The quantified statement ranges over every finite vertex type and every simple graph on it.

**Theorem 1.12 (The diameter bound is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/WellCoveredPowerCliqueProduct.result` (`✓ std3`). ∎

*Resolves.* `Problems/pham-vu-2026-well-covered-powers-diameter` (refuted) by `D5/S3/Combinatorics/Graph/WellCoveredPowerCliqueProduct.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"pham-vu-2026-well-covered-powers-diameter","declaration_gid":"D5/S3/Combinatorics/Graph/WellCoveredPowerCliqueProduct.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

The seven-cycle □ K_8 has 56 vertices, well-covered positive powers and diameter four. It refutes the proposed bound.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/WellCoveredPowerCliqueProduct.IsMaximalIndep`
- Truth anchor: `D5/S3/Combinatorics/Graph/WellCoveredPowerCliqueProduct.WCP`
- Truth anchor: `D5/S3/Combinatorics/Graph/WellCoveredPowerCliqueProduct.WellCovered`
- Truth anchor: `D5/S3/Combinatorics/Graph/WellCoveredPowerCliqueProduct.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/WellCoveredPowerCliqueProduct.cycle_seven_wcp`
- Truth anchor: `D5/S3/Combinatorics/Graph/WellCoveredPowerCliqueProduct.diam_cliqueProduct`
- Truth anchor: `D5/S3/Combinatorics/Graph/WellCoveredPowerCliqueProduct.distance_cliqueProduct`
- Truth anchor: `D5/S3/Combinatorics/Graph/WellCoveredPowerCliqueProduct.exists_wcp_diameter`
- Truth anchor: `D5/S3/Combinatorics/Graph/WellCoveredPowerCliqueProduct.power`
- Truth anchor: `D5/S3/Combinatorics/Graph/WellCoveredPowerCliqueProduct.projection_maximal`
- Truth anchor: `D5/S3/Combinatorics/Graph/WellCoveredPowerCliqueProduct.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/WellCoveredPowerCliqueProduct.wcp_cliqueProduct`
