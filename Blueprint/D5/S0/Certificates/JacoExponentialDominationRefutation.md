# The Domination Clause of Kok's Jaco Graph Conjecture

## Abstract

The A000149 vertices fail the domination clause of Kok's Conjecture 2.12.

**Definition 1.1 (Right endpoints in the infinite linear Jaco graph).**

Lean statement: `D5/S0/Certificates/JacoExponentialDominationRefutation.jacoRight`

*Formalization.* `D5/S0/Certificates/JacoExponentialDominationRefutation.jacoRight` (`✓ std3`).

*Citation.* Johan Kok (2025). *Integer sequences with conjectured relation with certain graph parameters of the family of linear Jaco graphs*. DOI: [10.48550/arXiv.2507.16500](https://doi.org/10.48550/arXiv.2507.16500).

*Commentary.*

For vertex n, the right endpoint is 2n minus the number of earlier positive vertices whose right endpoints reach n. The recursive table evaluates these endpoints from left to right.

**Theorem 1.2 (Strict growth of right endpoints).**

$$\forall n \in \mathbb{N},\; \operatorname{jacoRight}\left(n\right) + 1 \le \operatorname{jacoRight}\left(n + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/JacoExponentialDominationRefutation.jacoRight_succ_ge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johan Kok (2025). *Integer sequences with conjectured relation with certain graph parameters of the family of linear Jaco graphs*. DOI: [10.48550/arXiv.2507.16500](https://doi.org/10.48550/arXiv.2507.16500).

*Commentary.*

Every earlier endpoint counted at level n+1 is also counted at level n. Only vertex n itself can be the additional index, so the indegree count rises by at most one while the doubled vertex index rises by two. Therefore the right endpoint rises by at least one.

**Definition 1.3 (Undirected Jaco adjacency).**

Lean statement: `D5/S0/Certificates/JacoExponentialDominationRefutation.Adj`

*Formalization.* `D5/S0/Certificates/JacoExponentialDominationRefutation.Adj` (`✓ std3`).

*Citation.* Johan Kok (2025). *Integer sequences with conjectured relation with certain graph parameters of the family of linear Jaco graphs*. DOI: [10.48550/arXiv.2507.16500](https://doi.org/10.48550/arXiv.2507.16500).

*Commentary.*

For two distinct indices, the lower vertex is adjacent to the higher exactly when its right endpoint reaches the higher index.

**Definition 1.4 (The A000149 vertex indices).**

Lean statement: `D5/S0/Certificates/JacoExponentialDominationRefutation.exponentialVertices`

*Formalization.* `D5/S0/Certificates/JacoExponentialDominationRefutation.exponentialVertices` (`✓ std3`).

*Citation.* Johan Kok (2025). *Integer sequences with conjectured relation with certain graph parameters of the family of linear Jaco graphs*. DOI: [10.48550/arXiv.2507.16500](https://doi.org/10.48550/arXiv.2507.16500).

*Commentary.*

The selected indices are the natural floors of e to a natural-number power. Exponent zero supplies the artificial first term 1 used in the source statement.

**Definition 1.5 (Domination of positive vertices).**

Lean statement: `D5/S0/Certificates/JacoExponentialDominationRefutation.Dominates`

*Formalization.* `D5/S0/Certificates/JacoExponentialDominationRefutation.Dominates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A set dominates when each positive vertex either belongs to the set or is adjacent to one of its members.

**Definition 1.6 (The domination clause).**

Lean statement: `D5/S0/Certificates/JacoExponentialDominationRefutation.dominationClause`

*Formalization.* `D5/S0/Certificates/JacoExponentialDominationRefutation.dominationClause` (`✓ std3`).

*Citation.* Johan Kok (2025). *Integer sequences with conjectured relation with certain graph parameters of the family of linear Jaco graphs*. DOI: [10.48550/arXiv.2507.16500](https://doi.org/10.48550/arXiv.2507.16500).

*Commentary.*

The first clause of Conjecture 2.12 says that A000149 indexes a gamma-set of the infinite linear Jaco graph. Every gamma-set is dominating, so this definition records that necessary domination assertion. The minimum-cardinality and p-graphical assertions are not included.

**Theorem 1.7 (Vertex 88 is not dominated).**

$$\neg dominationClause$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/JacoExponentialDominationRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johan Kok (2025). *Integer sequences with conjectured relation with certain graph parameters of the family of linear Jaco graphs*. DOI: [10.48550/arXiv.2507.16500](https://doi.org/10.48550/arXiv.2507.16500).

*Commentary.*

The right endpoint at vertex 54 is 87 and the right endpoint at vertex 88 is 143. Strict endpoint growth shows that every selected index at most 54 has endpoint below 88.

Certified bounds for e put every A000149 term either at most 54 or at least 144. Thus vertex 88 is neither selected nor adjacent to a selected vertex. The domination clause is false, which refutes the gamma-set assertion. No conclusion is drawn about the separate p-graphical clause.

## References

- Truth anchor: `D5/S0/Certificates/JacoExponentialDominationRefutation.Adj`
- Truth anchor: `D5/S0/Certificates/JacoExponentialDominationRefutation.Dominates`
- Truth anchor: `D5/S0/Certificates/JacoExponentialDominationRefutation.dominationClause`
- Truth anchor: `D5/S0/Certificates/JacoExponentialDominationRefutation.exponentialVertices`
- Truth anchor: `D5/S0/Certificates/JacoExponentialDominationRefutation.jacoRight`
- Truth anchor: `D5/S0/Certificates/JacoExponentialDominationRefutation.jacoRight_succ_ge`
- Truth anchor: `D5/S0/Certificates/JacoExponentialDominationRefutation.result`
