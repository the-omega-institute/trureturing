# The original Jaco addition law is false

## Abstract

The distinct orders three and eleven refute the complete original two-branch Jaco addition assertion.

**Definition 1.1 (A unique Jaconian vertex).**

$$\forall n \in \mathrm{Nat},\; (\operatorname{UniqueJaconian}\left(n\right)) \Leftrightarrow (\exists v \in \operatorname{Vertex}\left(n\right),\; (\operatorname{degree}\left(\operatorname{jaco}\left(n\right), v\right) = \operatorname{maxDegree}\left(\operatorname{jaco}\left(n\right)\right)) \land (\forall w \in \operatorname{Vertex}\left(n\right),\; (\operatorname{degree}\left(\operatorname{jaco}\left(n\right), w\right) = \operatorname{maxDegree}\left(\operatorname{jaco}\left(n\right)\right)) \Rightarrow (w = v)))$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/JacoAdditionLawRefutation.UniqueJaconian` (`✓ std3`).

*Citation.* Johan Kok; Paul Fisher; Bettina Wilkens; Mokhwetha Mabula; Vivian Mukungunugwa (2014). *Characteristics of Finite Jaco Graphs, J_n(1), n in N*. DOI: [10.48550/arXiv.1404.0484](https://doi.org/10.48550/arXiv.1404.0484).

*Commentary.*

UniqueJaconian n means exactly one vertex of jaco n attains its ordinary maximum degree. The carrier consists precisely of positive labels 1 through n. This is uniqueness of a vertex within one graph, not uniqueness of a numerical degree across graph orders. The graph is the existing finite truncation of the recursive rule i<j<=2i-d^-(v_i), with orientation forgotten; every edge has exactly one forward arc, so simple degree counts incoming and retained outgoing arcs together.

**Definition 1.2 (The whole original Theorem 2.10).**

$$(claim) \Leftrightarrow (\forall n \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; (3 \le n) \Rightarrow ((3 \le m) \Rightarrow ((n \ne m) \Rightarrow ((((\operatorname{UniqueJaconian}\left(n\right)) \lor (\operatorname{UniqueJaconian}\left(m\right))) \Rightarrow (\operatorname{maxDegree}\left(\operatorname{jaco}\left(n + m\right)\right) = \operatorname{maxDegree}\left(\operatorname{jaco}\left(n\right)\right) + \operatorname{maxDegree}\left(\operatorname{jaco}\left(m\right)\right))) \land (((\neg \operatorname{UniqueJaconian}\left(n\right)) \land (\neg \operatorname{UniqueJaconian}\left(m\right))) \Rightarrow (\operatorname{maxDegree}\left(\operatorname{jaco}\left(n + m\right)\right) = \operatorname{maxDegree}\left(\operatorname{jaco}\left(n\right)\right) + \operatorname{maxDegree}\left(\operatorname{jaco}\left(m\right)\right) + 1))))))$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/JacoAdditionLawRefutation.claim` (`✓ std3`).

*Citation.* Johan Kok; Paul Fisher; Bettina Wilkens; Mokhwetha Mabula; Vivian Mukungunugwa (2014). *Characteristics of Finite Jaco Graphs, J_n(1), n in N*. DOI: [10.48550/arXiv.1404.0484](https://doi.org/10.48550/arXiv.1404.0484).

*Commentary.*

Kok, Fisher, Wilkens, Mabula and Mukungunugwa, arXiv:1404.0484v1, printed page 7, Theorem 2.10 (Conjectured), assert both displayed branches for every ordered pair of distinct natural orders n,m at least three. The first branch uses inclusive OR: either graph having a unique Jaconian vertex suffices. Otherwise means neither has a unique Jaconian vertex. No cutoff or additional graph hypothesis is imposed. The explicit open-problem list on printed page 11 asks to prove this theorem.

**Theorem 1.3 (Refutation of the complete addition assertion).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/JacoAdditionLawRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/kok-jaco-addition-law-refutation` (refuted) by `D5/S3/ConceptDynamics/GraphColoring/JacoAdditionLawRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kok-jaco-addition-law-refutation","declaration_gid":"D5/S3/ConceptDynamics/GraphColoring/JacoAdditionLawRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Johan Kok; Paul Fisher; Bettina Wilkens; Mokhwetha Mabula; Vivian Mukungunugwa (2014). *Characteristics of Finite Jaco Graphs, J_n(1), n in N*. DOI: [10.48550/arXiv.1404.0484](https://doi.org/10.48550/arXiv.1404.0484).

*Commentary.*

Use the original graph and the existing JacoMaximumDegree.degree_formula and JacoMaximumDegree.result. Put phi=(1+sqrt(5))/2. Exact rational bounds 8/5<phi<13/8 give the needed floors. The three degrees of J_3 are 1,2,1, so its unique maximizing vertex is v_2 and its maximum is 2. The same maximum-degree formula gives maximum 7 for J_11 and maximum 8 for J_14. At the admissible pair (3,11), the first branch therefore requires 8=2+7, a contradiction. A failure at this pair negates the whole universal two-branch claim; it asserts neither failure at every pair nor a counterexample to the otherwise branch. These numerical values also occur in Kok's prior published arXiv:2507.16500v1 Table 1; they are not new numerical data. Bounded source searches leave literature gaps and establish no worldwide priority.

## References

- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoAdditionLawRefutation.UniqueJaconian`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoAdditionLawRefutation.claim`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoAdditionLawRefutation.result`
- Dependency: [D5/S3/ConceptDynamics/GraphColoring/JacoMaximumDegree](JacoMaximumDegree.md)
