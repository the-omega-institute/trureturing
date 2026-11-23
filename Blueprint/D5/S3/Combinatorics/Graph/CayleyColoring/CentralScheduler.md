# The random central coloring daemon

## Abstract

A uniform ranking gives the same legal terminal-history probabilities as sequential uniform enabled choices.

**Theorem 1.1 (Exact terminal-history law).**

$$\forall (V: Type), \forall (K: Type), [\operatorname{Fintype}\left(V\right)] [\operatorname{LinearOrder}\left(V\right)] \forall (G: \operatorname{SimpleGraph}\left(V\right)), \forall (P: \operatorname{FreePolicy}\left(K, G\right)), \forall (c: V \to K), \forall (h: \operatorname{List}\left(V\right)), (\operatorname{LegalTerminal}\left(G, P, c, h\right) \implies \operatorname{card}\left(\operatorname{RankFiber}\left(G, c, h\right)\right) \cdot \operatorname{choiceProduct}\left(\operatorname{conflict}\left(G, c\right), \operatorname{univ}\left(V\right), h\right) = \operatorname{card}\left(\operatorname{Perm}\left(V\right)\right)) \land (\neg \operatorname{LegalTerminal}\left(G, P, c, h\right) \implies \operatorname{IsEmpty}\left(\operatorname{RankFiber}\left(G, c, h\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.policy_terminal_law` (`✓ std3`). ∎

*Citation.* Élie de Panafieu, Fabien Mathieu, Maria Potop-Butucaru, and Sébastien Tixeuil (2026). *The Exact Stabilization Time of Self-Stabilizing Coloring: Mean, Variance, and Distribution*. DOI: [10.48550/arXiv.2611.17989](https://doi.org/10.48550/arXiv.2611.17989). URL: <https://arxiv.org/abs/2611.17989v1>.

*Commentary.*

A history is accepted when following the free-color policy produces a proper final coloring. Its ranking fiber consists of permutations yielding that ordered mover list. The enabled sets shrink after each actual recoloring, and permuting the ranks of currently enabled vertices preserves the prefix constraints. The product counts the successive enabled choices from the initial conflict graph. An invalid or nonterminal history has an empty fiber.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.policy_terminal_law`
- Dependency: [D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition](TreeDecomposition.md)
