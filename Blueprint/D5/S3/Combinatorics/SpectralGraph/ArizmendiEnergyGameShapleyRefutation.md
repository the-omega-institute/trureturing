# The graph energy game and an unbalanced bipartite obstruction

## Abstract

Complete bipartite graphs refute Shapley core membership for graph energy games.

**Definition 1.1 (Energy of an induced coalition).**

$$\forall V \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall S \in \operatorname{Finset}\left(V\right),\; \operatorname{worth}\left(G, S\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{Graph}.\operatorname{SubgroupGenerating}.\operatorname{CyclicExtensionRefutation}.\operatorname{graphEnergy}\left(\operatorname{SimpleGraph}.\operatorname{induce}\left(G, (S: \operatorname{Set}\left(V\right))\right), \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{Graph}.\operatorname{SubgroupGenerating}.\operatorname{CyclicExtensionRefutation}.\operatorname{MatrixKind}.\operatorname{adjacency}\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/ArizmendiEnergyGameShapleyRefutation.worth` (`✓ std3`).

*Citation.* Gerardo Arizmendi and Octavio Arizmendi (2020). *The graph energy game*. DOI: [10.1016/j.dam.2023.01.030](https://doi.org/10.1016/j.dam.2023.01.030). URL: <https://arxiv.org/abs/2012.14114v2>.

*Commentary.*

Definition 3.1, page 5: “Let G = (V, E) be a simple undirected graph. For each subset S ⊂ V let w(S) := 𝓔(I(S)) where I(S) is the graph induced by S. We denote (V, w), the energy game on G.” Here the coalition is a Finset and its induced vertex type is (S : Set V). The existing graphEnergy with MatrixKind.adjacency sums the absolute real adjacency eigenvalues with multiplicity and center zero. This includes the empty coalition.

**Definition 1.2 (Coalition rationality and efficiency).**

$$\forall V \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] \forall w \in \operatorname{Finset}\left(V\right) \to \operatorname{Real},\; \operatorname{core}\left(w\right) = \{x: V \to \operatorname{Real} \mid (\left(\forall S \in \operatorname{Finset}\left(V\right),\; \sum_{i \in S} (x\left(i\right)) \ge w\left(S\right)\right) \land \sum_{i \in \operatorname{Finset}.\operatorname{univ}} (x\left(i\right)) = w\left(\operatorname{Finset}.\operatorname{univ}\right))\}$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/ArizmendiEnergyGameShapleyRefutation.core` (`✓ std3`).

*Citation.* Gerardo Arizmendi and Octavio Arizmendi (2020). *The graph energy game*. DOI: [10.1016/j.dam.2023.01.030](https://doi.org/10.1016/j.dam.2023.01.030). URL: <https://arxiv.org/abs/2012.14114v2>.

*Commentary.*

Definition 2.7, page 4: “The core of a game (N, w), denoted by C(w) is the set of imputations that are group rational. That is,” followed by “C(w) = {x| x(S) ≥ w(S) for each S ⊂ N and x(N) = w(N)}”. The same page states: “For a payoff distribution x and a coalition S, we use the notation x(S) = ∑_{i∈S} xᵢ.” The finite sums range over all coalitions, including the empty set and the full set. The variable x has type V → Real.

**Definition 1.3 (Factorial formula for the Shapley allocation).**

$$\forall V \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall w \in \operatorname{Finset}\left(V\right) \to \operatorname{Real},\; \forall i \in V,\; \operatorname{shapley}\left(w, i\right) = \sum_{S \in \operatorname{Finset}.\operatorname{powerset}\left(\operatorname{Finset}.\operatorname{erase}\left(\operatorname{Finset}.\operatorname{univ}, i\right)\right)} (\frac{(\operatorname{Nat}.\operatorname{factorial}\left(\operatorname{Finset}.\operatorname{card}\left(S\right)\right): \operatorname{Real}) \cdot (\operatorname{Nat}.\operatorname{factorial}\left(\operatorname{Fintype}.\operatorname{card}\left(V\right) - \operatorname{Finset}.\operatorname{card}\left(S\right) - 1\right): \operatorname{Real})}{(\operatorname{Nat}.\operatorname{factorial}\left(\operatorname{Fintype}.\operatorname{card}\left(V\right)\right): \operatorname{Real})} \cdot (w\left(\operatorname{Finset}.\operatorname{insert}\left(i, S\right)\right) - w\left(S\right)))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/ArizmendiEnergyGameShapleyRefutation.shapley` (`✓ std3`).

*Citation.* Gerardo Arizmendi and Octavio Arizmendi (2020). *The graph energy game*. DOI: [10.1016/j.dam.2023.01.030](https://doi.org/10.1016/j.dam.2023.01.030). URL: <https://arxiv.org/abs/2012.14114v2>.

*Commentary.*

Section 2.4, page 4: “The Shapley value is the only value that satisfies the axioms of efficiency, symmetry, additivity and null player, it is well known that actually the Shapley value is given by” followed by “φᵢ(w) = ∑_{S⊂N∖{i}} |S|!(n − |S| − 1)!(w(S ∪ {i}) − w(S))/n!” The index S ranges over the powerset of all vertices except i. The three factorials are computed in Nat and then coerced to Real; the displayed division is real division. Natural subtraction is truncated subtraction, agreeing with ordinary subtraction on this powerset because S.card ≤ Fintype.card V − 1.

**Definition 1.4 (Conjecture 3.10).**

$$\operatorname{claim} = (\forall n \in \operatorname{Nat},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{shapley}\left(\operatorname{worth}\left(G\right)\right) \in \operatorname{core}\left(\operatorname{worth}\left(G\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/ArizmendiEnergyGameShapleyRefutation.claim` (`✓ std3`).

*Citation.* Gerardo Arizmendi and Octavio Arizmendi (2020). *The graph energy game*. DOI: [10.1016/j.dam.2023.01.030](https://doi.org/10.1016/j.dam.2023.01.030). URL: <https://arxiv.org/abs/2012.14114v2>.

*Commentary.*

Conjecture 3.10, page 8: “For the energy game, the Shapley value is in the core.” The universal size n includes zero, and SimpleGraph (Fin n) supplies a finite simple undirected graph without a connectedness or degree restriction. Core membership includes every coalition inequality and efficiency.

**Theorem 1.5 (Refutation by K₂,₅₀).**

$$\neg (\forall n \in \operatorname{Nat},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{shapley}\left(\operatorname{worth}\left(G\right)\right) \in \operatorname{core}\left(\operatorname{worth}\left(G\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/ArizmendiEnergyGameShapleyRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gerardo Arizmendi and Octavio Arizmendi (2020). *The graph energy game*. DOI: [10.1016/j.dam.2023.01.030](https://doi.org/10.1016/j.dam.2023.01.030). URL: <https://arxiv.org/abs/2012.14114v2>.

*Commentary.*

For every m ≥ 50, the graph with two scarce-side vertices a and b and m other vertices, with exactly the cross edges, has coalition energy 2√(rk) when the coalition contains r scarce-side vertices and k other vertices. Its scarce-side Shapley payoff is 2((m + √2)∑ₖ₌₀ᵐ√k + (√2 − 2)∑ₖ₌₀ᵐk√k)/((m + 1)(m + 2)). Summing the one-step inequalities gives ∑ₖ₌₀ᵐ√k ≥ (2/3)m√m and ∑ₖ₌₀ᵐk√k ≤ (2/5)m²√m + m√m. With the negative coefficient √2 − 2 treated in its correct direction, these bounds put the payoff above 2(√2 − 1)√m. If the allocation were in the core, its efficiency equality would make the coalition excluding a violate its lower payoff bound 2√m. Taking m = 50 and vertices 0 and 1 in Fin 52 disproves the universal proposition. No optimal threshold, asymptotic limit, or classification of trees or regular graphs is asserted.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/ArizmendiEnergyGameShapleyRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/ArizmendiEnergyGameShapleyRefutation.core`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/ArizmendiEnergyGameShapleyRefutation.result`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/ArizmendiEnergyGameShapleyRefutation.shapley`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/ArizmendiEnergyGameShapleyRefutation.worth`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Drift/OneStep](../../Arith/Lattices/Klartag/Drift/OneStep.md)
- Dependency: [D5/S3/Combinatorics/Graph/SubgroupGenerating/CyclicExtensionRefutation](../Graph/SubgroupGenerating/CyclicExtensionRefutation.md)
