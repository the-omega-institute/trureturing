# Morrie's theorem with the endpoint condition

## Abstract

Morrie's theorem on the finite Jaco graphs holds once n = R_k is added to its indegree conditions.

**Definition 1.1 (The indegree d^-(v_i)).**

$$\operatorname{indeg}\left(i\right) = i - \operatorname{b}\left(i\right)$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/JacoMorrieTheorem.indeg` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johan Kok; Paul Fisher; Bettina Wilkens; Mokhwetha Mabula; Vivian Mukungunugwa (2014). *Characteristics of Finite Jaco Graphs, J_n(1), n in N*. DOI: [10.48550/arXiv.1404.0484](https://doi.org/10.48550/arXiv.1404.0484).

*Commentary.*

indeg i is the indegree a_i=i-b_i of v_i in the infinite Jaco graph, where b_i=beattyOut i=floor((i+1)/phi) is its outdegree.

**Theorem 1.2 (Corrected Morrie's theorem).**

$$\forall n \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; (\operatorname{P}\left(n, k\right)) \Rightarrow ((((n = \operatorname{R}\left(k\right)) \land ((\operatorname{indeg}\left(k\right) = \operatorname{indeg}\left(k + 1\right)) \land (\operatorname{indeg}\left(k + 2\right) = \operatorname{indeg}\left(k + 1\right) + 1))) \Leftrightarrow ((\operatorname{jaconian}\left(n\right) = \{k\}) \land (\operatorname{jaconian}\left(n + 1\right) = \{k, k + 1, k + 2\}))) \land ((((n = \operatorname{R}\left(k\right)) \land (\operatorname{indeg}\left(k + 2\right) = \operatorname{indeg}\left(k + 1\right) + 1)) \Leftrightarrow ((\operatorname{jaconian}\left(n\right) = \{k\}) \land (\operatorname{jaconian}\left(n + 1\right) = \{k, k + 1, k + 2\}))) \land (((n = \operatorname{R}\left(k\right)) \land ((\operatorname{indeg}\left(k\right) = \operatorname{indeg}\left(k + 1\right)) \land (\operatorname{indeg}\left(k + 1\right) = \operatorname{indeg}\left(k + 2\right)))) \Leftrightarrow ((\operatorname{jaconian}\left(n\right) = \{k\}) \land (\operatorname{jaconian}\left(n + 1\right) = \{k, k + 1\})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/JacoMorrieTheorem.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johan Kok; Paul Fisher; Bettina Wilkens; Mokhwetha Mabula; Vivian Mukungunugwa (2014). *Characteristics of Finite Jaco Graphs, J_n(1), n in N*. DOI: [10.48550/arXiv.1404.0484](https://doi.org/10.48550/arXiv.1404.0484).

*Commentary.*

Write J_n for the complete set of maximum-degree labels of the finite linear Jaco graph J_n(1), R_k=jacoRight k=k+b_k, and P(n,k) for the hypothesis that n is at least 2 and k is the least element of J_n, the prime Jaconian vertex. Under P(n,k), k=Delta_n by JacoMaximumSet.result, and J_n={k} exactly when n=R_k and b_(k+1)=b_k+1, that is, when d^-(v_k)=d^-(v_(k+1)). At a singleton, J_(n+1) is [k,k+1] or [k,k+2], and by the degree formula deg(v_(k+2))=min(k+2,n+1-b_(k+2)) at order n+1=R_k+1 the label k+2 is maximum exactly when b_(k+2)=b_(k+1), that is, when d^-(v_(k+2))=d^-(v_(k+1))+1; otherwise b_(k+2)=b_(k+1)+1 and d^-(v_(k+2))=d^-(v_(k+1)). Hence (a) n=R_k, d^-(v_k)=d^-(v_(k+1)) and d^-(v_(k+2))=d^-(v_(k+1))+1 if and only if J_n={k} and J_(n+1)={k,k+1,k+2}; since the outdegrees never stay constant over two consecutive steps (2/phi>1), d^-(v_(k+2))=d^-(v_(k+1))+1 already forces d^-(v_k)=d^-(v_(k+1)), so n=R_k with d^-(v_(k+2))=d^-(v_(k+1))+1 is equivalent to the same conclusion; and (b) n=R_k and d^-(v_k)=d^-(v_(k+1))=d^-(v_(k+2)) if and only if J_n={k} and J_(n+1)={k,k+1}. Theorem 2.3 (Morrie's Theorem) of Kok, Fisher, Wilkens, Mabula and Mukungunugwa, arXiv:1404.0484v1, page 4, states (a) and (b) without the condition n=R_k, and both then fail (JacoMorrieTheoremRefutation); Corollary 4 of Ma and Zhang, Zenodo DOI 10.5281/zenodo.24369124, gives the corrected form. The maximum-set description used through JacoMaximumSet is credited there to Patel's solution of MathDB problem 369424, which was not inspected.

## References

- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoMorrieTheorem.indeg`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoMorrieTheorem.result`
- Dependency: [D5/S3/ConceptDynamics/GraphColoring/JacoDirectedPathCount](JacoDirectedPathCount.md)
- Dependency: [D5/S3/ConceptDynamics/GraphColoring/JacoMaximumDegree](JacoMaximumDegree.md)
- Dependency: [D5/S3/ConceptDynamics/GraphColoring/JacoMaximumSet](JacoMaximumSet.md)
- Dependency: [D5/S3/ConceptDynamics/GraphColoring/JacoTripleMaximizers](JacoTripleMaximizers.md)
