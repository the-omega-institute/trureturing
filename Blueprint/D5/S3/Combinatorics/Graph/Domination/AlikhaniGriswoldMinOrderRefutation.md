# The order-33 integer domination-root minimality claim

## Abstract

A connected 21-vertex ordinary-domination witness at minus four refutes the complete order-33 minimality claim.

Alikhani and Griswold, arXiv:2608.00109v1, Section 4 item 2 asks whether n=33 is the minimal order of a finite simple connected graph whose ordinary domination polynomial vanishes at -4. The formal claim retains both attainment at order 33 and nonvanishing at every positive order below 33.

**Definition 1.1 (The complete order-33 minimality claim).**

$$(claim: Prop) = ((\exists (G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(33\right)\right)), (\operatorname{Connected}\left(G\right)) \land (\sum {S \in \operatorname{domSets}\left(G\right)} (-4)^{\operatorname{card}\left(S\right)} = 0)) \land (\forall (n: \mathrm{Nat}), (1 \le n) \Rightarrow ((n < 33) \Rightarrow (\forall (G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), (\operatorname{Connected}\left(G\right)) \Rightarrow (\sum {S \in \operatorname{domSets}\left(G\right)} (-4)^{\operatorname{card}\left(S\right)} \ne 0)))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/AlikhaniGriswoldMinOrderRefutation.claim` (`✓ std3`).

*Citation.* Saeid Alikhani; Max Griswold (2026). *On the Integer Domination Root Conjecture*. DOI: [10.48550/arXiv.2608.00109](https://doi.org/10.48550/arXiv.2608.00109). URL: <https://arxiv.org/abs/2608.00109v1>.

*Commentary.*

The first conjunct asserts an order-33 connected graph with ordinary domination evaluation zero at -4. The second conjunct asserts that every positive n below 33 and every connected graph on Fin n has nonzero ordinary domination evaluation. Dominating subsets are counted once and need not be connected.

**Theorem 1.2 (A 21-vertex counterexample refutes minimality).**

$$\neg ((\exists (G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(33\right)\right)), (\operatorname{Connected}\left(G\right)) \land (\sum {S \in \operatorname{domSets}\left(G\right)} (-4)^{\operatorname{card}\left(S\right)} = 0)) \land (\forall (n: \mathrm{Nat}), (1 \le n) \Rightarrow ((n < 33) \Rightarrow (\forall (G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), (\operatorname{Connected}\left(G\right)) \Rightarrow (\sum {S \in \operatorname{domSets}\left(G\right)} (-4)^{\operatorname{card}\left(S\right)} \ne 0)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/AlikhaniGriswoldMinOrderRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/alikhani-griswold-2026-minus-four-minimum-order` (refuted) by `D5/S3/Combinatorics/Graph/Domination/AlikhaniGriswoldMinOrderRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"alikhani-griswold-2026-minus-four-minimum-order","declaration_gid":"D5/S3/Combinatorics/Graph/Domination/AlikhaniGriswoldMinOrderRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Saeid Alikhani; Max Griswold (2026). *On the Integer Domination Root Conjecture*. DOI: [10.48550/arXiv.2608.00109](https://doi.org/10.48550/arXiv.2608.00109). URL: <https://arxiv.org/abs/2608.00109v1>.

*Commentary.*

The explicit 21-vertex graph has the 25 listed undirected edges. Its core is induced on 0 through 6, with branches 7 through 12 and 13 through 20 rooted at 7 and 13 and incident on core sets {0} and {0,3,4}. The accepted ordinary decomposition gives message pairs (-1024,972) and (-3328,6912); the same supplied decomposition and exact table cancellation yield evaluation zero at -4. The graph is connected by the displayed paths from vertex 0. Since 1 <= 21 < 33, this contradicts the lower-bound conjunct and answers the source question negatively. No claim that 21 is minimal is made.

The result is a literal refutation of the complete source claim; it does not assert that 21 is the least counterexample order.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/AlikhaniGriswoldMinOrderRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/AlikhaniGriswoldMinOrderRefutation.result`
- Dependency: [D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly](MinusFourReassembly.md)
