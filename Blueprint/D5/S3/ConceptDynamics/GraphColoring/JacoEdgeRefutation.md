# The edge from v_Delta to v_n

## Abstract

The maximum-degree vertex v_Delta is joined to the last vertex exactly when Delta_n=b_n, so the edge clause of Theorem 2.15 fails at order nineteen while its bound holds.

**Theorem 1.1 (When v_Delta is joined to v_n).**

$$\forall n \in \mathrm{Nat},\; (1 \le n) \Rightarrow ((\operatorname{jacoRight}\left(\operatorname{maxDegree}\left(\operatorname{jaco}\left(n\right)\right)\right) \le n) \land (((\operatorname{Adj}\left(\operatorname{maxDegree}\left(\operatorname{jaco}\left(n\right)\right), n\right)) \Leftrightarrow (n = \operatorname{jacoRight}\left(\operatorname{maxDegree}\left(\operatorname{jaco}\left(n\right)\right)\right))) \land (((\operatorname{Adj}\left(\operatorname{maxDegree}\left(\operatorname{jaco}\left(n\right)\right), n\right)) \Leftrightarrow (\operatorname{maxDegree}\left(\operatorname{jaco}\left(n\right)\right) = \operatorname{beattyOut}\left(n\right))) \land ((\operatorname{Adj}\left(\operatorname{maxDegree}\left(\operatorname{jaco}\left(n\right)\right), n\right)) \Leftrightarrow (\operatorname{frac}\left(n\right) < \frac{1}{phi})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/JacoEdgeRefutation.edge_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johan Kok; Paul Fisher; Bettina Wilkens; Mokhwetha Mabula; Vivian Mukungunugwa (2014). *Characteristics of Finite Jaco Graphs, J_n(1), n in N*. DOI: [10.48550/arXiv.1404.0484](https://doi.org/10.48550/arXiv.1404.0484).

*Commentary.*

Write Delta=Delta_n for the maximum degree of jaco n, R_i=jacoRight i=i+b_i and b_i=beattyOut i=floor((i+1)/phi). For every n at least one: R_Delta<=n, and the edge v_Delta v_n exists exactly when n=R_Delta, exactly when Delta_n=b_n, and exactly when the fractional part of (n+2)/phi lies below 1/phi. Proof: b_(n+1)=floor((n+2)/phi)=Delta_n+1 by JacoAdditionLaw.delta_eq_floor, and b_(n+1)<=n, so Delta<n; the edge between labels Delta<n exists exactly when n<=R_Delta. The existing Beatty threshold turns n+1<=R_Delta into b_(n+1)<=Delta, which is false, so R_Delta<=n; and it turns n<=R_Delta into b_n<=Delta, which by JacoDegreeShift.result (Delta_n is b_n or b_n-1) means Delta_n=b_n, equivalently the fractional-part threshold.

**Theorem 1.2 (The bound of Theorem 2.15).**

$$\forall k \in \mathrm{Nat},\; \operatorname{maxDegree}\left(\operatorname{jaco}\left(7 + 3 \cdot k\right)\right) \le 4 + 2 \cdot k$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/JacoEdgeRefutation.bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johan Kok; Paul Fisher; Bettina Wilkens; Mokhwetha Mabula; Vivian Mukungunugwa (2014). *Characteristics of Finite Jaco Graphs, J_n(1), n in N*. DOI: [10.48550/arXiv.1404.0484](https://doi.org/10.48550/arXiv.1404.0484).

*Commentary.*

For every k, the maximum degree at order n=7+3k is at most 4+2k=n-(3+k), the bound asserted in Theorem 2.15 of Kok, Fisher, Wilkens, Mabula and Mukungunugwa, arXiv:1404.0484v1, printed page 9. It follows from delta_eq_floor because (9+3k)/phi<6+2k when phi>8/5.

**Definition 1.3 (The edge clause of Theorem 2.15).**

$$(claim) \Leftrightarrow (\forall k \in \mathrm{Nat},\; \operatorname{Adj}\left(\operatorname{maxDegree}\left(\operatorname{jaco}\left(7 + 3 \cdot k\right)\right), 7 + 3 \cdot k\right))$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/JacoEdgeRefutation.claim` (`✓ std3`).

*Citation.* Johan Kok; Paul Fisher; Bettina Wilkens; Mokhwetha Mabula; Vivian Mukungunugwa (2014). *Characteristics of Finite Jaco Graphs, J_n(1), n in N*. DOI: [10.48550/arXiv.1404.0484](https://doi.org/10.48550/arXiv.1404.0484).

*Commentary.*

Theorem 2.15 of arXiv:1404.0484v1, printed page 9, asserts for every n=7+3k with k a natural number that the edge (v_Delta, v_n) exists in J_n(1). claim is that clause for every k, with the frozen adjacency of the infinite graph on labels.

**Theorem 1.4 (The edge clause fails at order nineteen).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/JacoEdgeRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johan Kok; Paul Fisher; Bettina Wilkens; Mokhwetha Mabula; Vivian Mukungunugwa (2014). *Characteristics of Finite Jaco Graphs, J_n(1), n in N*. DOI: [10.48550/arXiv.1404.0484](https://doi.org/10.48550/arXiv.1404.0484).

*Commentary.*

Take k=4, so n=19. The existing maximum-degree formula gives Delta_19=floor(21/phi)-1=11, and R_11=18 by evaluating the recursive endpoint table. By edge_iff the edge would force 19=R_11=18, which is false. The bound part of Theorem 2.15 remains valid; only the edge clause fails.

## References

- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoEdgeRefutation.bound`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoEdgeRefutation.claim`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoEdgeRefutation.edge_iff`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoEdgeRefutation.result`
- Dependency: [D5/S3/ConceptDynamics/GraphColoring/JacoDegreeShift](JacoDegreeShift.md)
