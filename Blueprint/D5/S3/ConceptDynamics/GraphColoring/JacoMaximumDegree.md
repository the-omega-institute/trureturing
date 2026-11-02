# Maximum degree and literal Fibonacci digit deletion

## Abstract

The ordinary maximum degree of every positive-order recursive linear Jaco graph is its same-index literal Zeckendorf deletion.

**Theorem 1.1 (Count both kinds of neighbors).**

$$\forall n \in \mathrm{Nat},\; \forall v \in \operatorname{Vertex}\left(n\right),\; \operatorname{degree}\left(\operatorname{jaco}\left(n\right), v\right) = \operatorname{min}\left(\operatorname{val}\left(v\right), n - \operatorname{beattyOut}\left(\operatorname{val}\left(v\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/JacoMaximumDegree.degree_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johan Kok (2025). *Integer sequences with conjectured relation with certain graph parameters of the family of linear Jaco graphs*. DOI: [10.48550/arXiv.2507.16500](https://doi.org/10.48550/arXiv.2507.16500).

*Commentary.*

For every natural n and every vertex v with label i from 1 through n, the ordinary undirected degree is min(i,n-b(i)), where b(i) is floor((i+1)/phi). The incoming labels are the interval from b(i) through i-1. The outgoing labels are i+1 through min(n,i+b(i)). These disjoint intervals count the actual neighbor set of the existing recursive graph.

**Theorem 1.2 (Every positive graph order).**

$$\forall n \in \mathrm{Nat},\; (1 \le n) \Rightarrow (\operatorname{maxDegree}\left(\operatorname{jaco}\left(n\right)\right) = \operatorname{deleteLeast}\left(n\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/JacoMaximumDegree.max_degree_eq_deletion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johan Kok (2025). *Integer sequences with conjectured relation with certain graph parameters of the family of linear Jaco graphs*. DOI: [10.48550/arXiv.2507.16500](https://doi.org/10.48550/arXiv.2507.16500).

*Commentary.*

For n at least two, let k be the deletion value. The substitution block inequalities, together with the proved endpoint law, give R_k at most n and R_(k+1) greater than n. Vertex k has degree k. Smaller labels have degree at most their labels; larger labels have degree at most n-b(k+1), which is at most k. At order one, the graph is a singleton and deleting its word 1 gives zero. This retains the actual sequence index n and introduces no graph at order zero.

**Theorem 1.3 (Both clauses of Conjecture 2.2).**

$$(\forall n \in \mathrm{Nat},\; (2 \le n) \Rightarrow ((\operatorname{maxDegree}\left(\operatorname{jaco}\left(n\right)\right) = \operatorname{natFloor}\left((2 \cdot \left(n + 2\right))/(1 + \operatorname{sqrt}\left(5\right))\right) - 1) \land (\operatorname{maxDegree}\left(\operatorname{jaco}\left(n\right)\right) = \operatorname{deleteLeast}\left(n\right)))) \land (\forall n \in \mathrm{Nat},\; (1 \le n) \Rightarrow (\operatorname{maxDegree}\left(\operatorname{jaco}\left(n\right)\right) = \operatorname{deleteLeast}\left(n\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/JacoMaximumDegree.result` (`✓ std3`). ∎

*Resolves.* `Problems/kok-linear-jaco-maximum-degree` (proved) by `D5/S3/ConceptDynamics/GraphColoring/JacoMaximumDegree.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kok-linear-jaco-maximum-degree","declaration_gid":"D5/S3/ConceptDynamics/GraphColoring/JacoMaximumDegree.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Johan Kok (2025). *Integer sequences with conjectured relation with certain graph parameters of the family of linear Jaco graphs*. DOI: [10.48550/arXiv.2507.16500](https://doi.org/10.48550/arXiv.2507.16500).

*Commentary.*

Kok's Conjecture 2.2 asserts the displayed floor formula for every order n at least two, identifies the same-index A319433 term, and retains every positive order in its p-graphical family. The sequence operation is independently defined on canonical Zeckendorf digits; it is not defined by the floor expression. Thus the fixed family J_1,J_2,... realizes every positive-index term, and restricting this identity realizes every positive finite prefix. The offset-zero sequence entry stays outside the printed graph family. The graph proof uses recursive interval counting; Bettina's prose theorem is not a formal premise.

## References

- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoMaximumDegree.degree_formula`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoMaximumDegree.max_degree_eq_deletion`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoMaximumDegree.result`
- Dependency: [D5/S1/Words/Powers/ZeckendorfDeletion](../../../S1/Words/Powers/ZeckendorfDeletion.md)
- Dependency: [D5/S3/ConceptDynamics/GraphColoring/JacoDomPathDiameterRefutation](JacoDomPathDiameterRefutation.md)
- Dependency: [D5/S3/ConceptDynamics/GraphColoring/JacoEndpointBeatty](JacoEndpointBeatty.md)
