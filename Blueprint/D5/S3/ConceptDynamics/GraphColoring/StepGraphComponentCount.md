# Fixed-step graph components

## Abstract

A positive fixed step partitions an integer interval into its occurring residue classes.

**Definition 1.1 (The interval graph).**

$$\operatorname{G}\left(d, m\right) = \operatorname{fromRel}\left(\lambda i j, i+m=j\right)$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/StepGraphComponentCount.stepGraph` (`✓ std3`).

*Citation.* Hojin Chu, Homoon Ryu (2025). *Linear-Time Computation of the Frobenius Normal Form for Symmetric Toeplitz Matrices via Graph-Theoretic Decomposition*. URL: <https://arxiv.org/abs/2505.20811v1>.

*Commentary.*

The vertices are 0 through d-1. The undirected graph joins i and j when i+m=j or j+m=i, and removes loops. For m at least one, this is exactly the condition that the absolute difference of the labels equals m.

**Definition 1.2 (The occurring residues).**

$$\operatorname{R}\left(d, m\right) = \{\operatorname{mod}\left(i, m\right) \mid 0 \le i < d\}$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/StepGraphComponentCount.occurringResidues` (`✓ std3`).

*Citation.* Hojin Chu, Homoon Ryu (2025). *Linear-Time Computation of the Frobenius Normal Form for Symmetric Toeplitz Matrices via Graph-Theoretic Decomposition*. URL: <https://arxiv.org/abs/2505.20811v1>.

*Commentary.*

Take the image of the interval under reduction modulo m. Repeated residues are counted once, and residues not represented by any vertex are absent.

**Theorem 1.3 (Reachability is equality of residues).**

$$\operatorname{Reachable}\left(\operatorname{G}\left(d, m\right), i, j\right) \iff \operatorname{mod}\left(i, m\right) = \operatorname{mod}\left(j, m\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/StepGraphComponentCount.reachable_iff_mod_eq` (`✓ std3`). ∎

*Citation.* Hojin Chu, Homoon Ryu (2025). *Linear-Time Computation of the Frobenius Normal Form for Symmetric Toeplitz Matrices via Graph-Theoretic Decomposition*. URL: <https://arxiv.org/abs/2505.20811v1>.

*Commentary.*

Let d and m be natural numbers with m at least one, and let i and j be vertices. Every edge preserves the remainder, so every finite walk preserves it. Conversely, repeatedly subtracting m from a label at least m stays in the interval and eventually reaches its remainder. Reversing one such walk connects any two labels with the same remainder.

**Definition 1.4 (Components and occurring residues).**

$$\operatorname{ConnectedComponent}\left(\operatorname{G}\left(d, m\right)\right) \equiv \operatorname{R}\left(d, m\right)$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/StepGraphComponentCount.componentEquivResidues` (`✓ std3`).

*Citation.* Hojin Chu, Homoon Ryu (2025). *Linear-Time Computation of the Frobenius Normal Form for Symmetric Toeplitz Matrices via Graph-Theoretic Decomposition*. URL: <https://arxiv.org/abs/2505.20811v1>.

*Commentary.*

For every d and positive m, assign each component the remainder of any of its vertices. Preservation along walks makes this independent of the chosen vertex. Equal remainders give a walk, proving injectivity; each occurring remainder has a vertex, proving surjectivity.

**Theorem 1.5 (The number of components).**

$$\forall d,m \in \mathbb{N}, 1 \le m \Rightarrow \operatorname{card}\left(\operatorname{ConnectedComponent}\left(\operatorname{G}\left(d, m\right)\right)\right) = \operatorname{min}\left(m, d\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/StepGraphComponentCount.connectedComponent_card` (`✓ std3`). ∎

*Citation.* Hojin Chu, Homoon Ryu (2025). *Linear-Time Computation of the Frobenius Normal Form for Symmetric Toeplitz Matrices via Graph-Theoretic Decomposition*. URL: <https://arxiv.org/abs/2505.20811v1>.

*Commentary.*

For arbitrary natural d and m with m at least one, the occurring residues are exactly 0 through min(m,d)-1. Every remainder is below m and no larger than its original label; each label below both bounds represents itself. The component bijection therefore gives the stated cardinality. When d is zero both sets are empty. When m is at least d every vertex is isolated; when d is one there is one component. Positivity of m is necessary: at m=0 and d=1 the loopless graph has one component, whereas min(0,1)=0.

## References

- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/StepGraphComponentCount.componentEquivResidues`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/StepGraphComponentCount.connectedComponent_card`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/StepGraphComponentCount.occurringResidues`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/StepGraphComponentCount.reachable_iff_mod_eq`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/StepGraphComponentCount.stepGraph`
