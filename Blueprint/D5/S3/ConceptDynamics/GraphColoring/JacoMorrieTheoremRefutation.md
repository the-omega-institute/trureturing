# Morrie's theorem as stated is false

## Abstract

Each part of Morrie's theorem on the finite Jaco graphs fails as stated: part (a) at order 6 and part (b) at order 4.

**Definition 1.1 (Morrie's theorem as stated, part (a) or part (b)).**

$$claim = \left((\forall n \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; (\operatorname{P}\left(n, k\right)) \Rightarrow (((\operatorname{indeg}\left(k\right) = \operatorname{indeg}\left(k + 1\right)) \land (\operatorname{indeg}\left(k + 2\right) = \operatorname{indeg}\left(k + 1\right) + 1)) \Leftrightarrow ((\operatorname{jaconian}\left(n\right) = \{k\}) \land (\operatorname{jaconian}\left(n + 1\right) = \{k, k + 1, k + 2\})))) \lor (\forall n \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; (\operatorname{P}\left(n, k\right)) \Rightarrow (((\operatorname{indeg}\left(k\right) = \operatorname{indeg}\left(k + 1\right)) \land (\operatorname{indeg}\left(k + 1\right) = \operatorname{indeg}\left(k + 2\right))) \Leftrightarrow ((\operatorname{jaconian}\left(n\right) = \{k\}) \land (\operatorname{jaconian}\left(n + 1\right) = \{k, k + 1\}))))\right)$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/JacoMorrieTheoremRefutation.claim` (`✓ std3`).

*Citation.* Johan Kok; Paul Fisher; Bettina Wilkens; Mokhwetha Mabula; Vivian Mukungunugwa (2014). *Characteristics of Finite Jaco Graphs, J_n(1), n in N*. DOI: [10.48550/arXiv.1404.0484](https://doi.org/10.48550/arXiv.1404.0484).

*Commentary.*

Kok, Fisher, Wilkens, Mabula and Mukungunugwa, arXiv:1404.0484v1, printed page 4, Theorem 2.3 (Morrie's Theorem): if J_n(1), n at least 2, has prime Jaconian vertex v_k (Definition 1.4: the least Jaconian vertex) then (a) d^-(v_k)=d^-(v_(k+1)) and d^-(v_(k+2))=d^-(v_(k+1))+1 if and only if J(J_n)={v_k} and J(J_(n+1)(1))={v_k,v_(k+1),v_(k+2)}, and (b) d^-(v_k)=d^-(v_(k+1))=d^-(v_(k+2)) if and only if J(J_n)={v_k} and J(J_(n+1)(1))={v_k,v_(k+1)}. Here d^-(v_i)=indeg i=i-b_i is the indegree in the infinite Jaco graph and P(n,k) says that n is at least 2 and k is the least element of J_n. The claim is the disjunction of the two parts, so refuting it refutes each part separately.

**Theorem 1.2 (Refutation of both parts).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/JacoMorrieTheoremRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johan Kok; Paul Fisher; Bettina Wilkens; Mokhwetha Mabula; Vivian Mukungunugwa (2014). *Characteristics of Finite Jaco Graphs, J_n(1), n in N*. DOI: [10.48550/arXiv.1404.0484](https://doi.org/10.48550/arXiv.1404.0484).

*Commentary.*

With 0.618<1/phi<0.619, b_2=1, b_3=2, b_4=3 and b_5=3, and JacoAdditionLaw.delta_eq_floor gives Delta_4=2 and Delta_6=3, which are the least maximum-degree labels by JacoMaximumSet.result. At n=6, k=3 the indegrees d^-(v_3)=d^-(v_4)=1 and d^-(v_5)=2 satisfy the left side of (a), but J_6 is not {3} because the singleton criterion of JacoMaximumSet.result requires 6=R_3=3+b_3=5. At n=4, k=2 the indegrees d^-(v_2)=d^-(v_3)=d^-(v_4)=1 satisfy the left side of (b), but J_4 is not {2} because R_2=3. Corollary 4 of Ma and Zhang, Zenodo DOI 10.5281/zenodo.24369124, records both counterexamples; the corrected theorem is JacoMorrieTheorem.result.

## References

- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoMorrieTheoremRefutation.claim`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoMorrieTheoremRefutation.result`
- Dependency: [D5/S3/ConceptDynamics/GraphColoring/JacoMorrieTheorem](JacoMorrieTheorem.md)
