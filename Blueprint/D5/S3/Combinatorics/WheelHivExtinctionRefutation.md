# The extinction set of the wheel W_18 contains 4

## Abstract

In the Mukwembi model of HIV infection on the wheel W_18 with replacement parameter R = 4, every admissible initial state reaches the all-healthy state by time 25, so 4 belongs to the extinction set of W_18 and Conjecture 1 of Espinosa-Garcia et al., which puts that set equal to {3} together with all R >= 17, is false.

**Definition 1.1 (The wheel W_n).**

$$\operatorname{wheelAdj}\left(n, u, v\right) \Leftrightarrow (u \ne v \land (\left(\left(\left(\left(\operatorname{val}\left(u\right) = 0 \lor \operatorname{val}\left(v\right) = 0\right) \lor \operatorname{val}\left(u\right) + 1 = \operatorname{val}\left(v\right)\right) \lor \operatorname{val}\left(v\right) + 1 = \operatorname{val}\left(u\right)\right) \lor (\operatorname{val}\left(u\right) = 1 \land \operatorname{val}\left(v\right) = n - 1)\right) \lor (\operatorname{val}\left(v\right) = 1 \land \operatorname{val}\left(u\right) = n - 1)))$$

*Formalization.* `D5/S3/Combinatorics/WheelHivExtinctionRefutation.wheelAdj` (`✓ std3`).

*Citation.* Manuel A. Espinosa-García, Ana Paulina Figueroa, Julián A. Fresán-Figueroa, Gerardo L. Maldonado, L. Ariadna Sánchez-Solís (2026). *Extinction thresholds in a graph-based model of HIV infection dynamics*. DOI: [10.48550/arXiv.2608.00340](https://doi.org/10.48550/arXiv.2608.00340). URL: <https://arxiv.org/abs/2608.00340v1>.

*Commentary.*

The wheel W_n = K_1 joined with the cycle C_(n-1) on the vertices 0, ..., n - 1: vertex 0 is the hub, adjacent to every other vertex, and the cycle runs through 1, 2, ..., n - 1 and closes from n - 1 back to 1.

**Definition 1.2 (Infected neighbours).**

$$\operatorname{infectedCount}\left(adj, f, v\right) = \operatorname{card}\left(\{u:adj\left(v, u\right) \land f\left(u\right) = 1\}\right)$$

*Formalization.* `D5/S3/Combinatorics/WheelHivExtinctionRefutation.infectedCount` (`✓ std3`).

*Citation.* Manuel A. Espinosa-García, Ana Paulina Figueroa, Julián A. Fresán-Figueroa, Gerardo L. Maldonado, L. Ariadna Sánchez-Solís (2026). *Extinction thresholds in a graph-based model of HIV infection dynamics*. DOI: [10.48550/arXiv.2608.00340](https://doi.org/10.48550/arXiv.2608.00340). URL: <https://arxiv.org/abs/2608.00340v1>.

*Commentary.*

d_(t,I)(v), the number of neighbours of v that are infected (state 1) in the state f.

**Definition 1.3 (The update rule).**

$$\operatorname{step}\left(adj, R, f\right)\left(v\right) = \operatorname{if} f\left(v\right) = 1 \operatorname{then} 2 \operatorname{else} (\operatorname{if} f\left(v\right) = 0 \operatorname{then} (\operatorname{if} \operatorname{infectedCount}\left(adj, f, v\right) = 0 \operatorname{then} 0 \operatorname{else} 1) \operatorname{else} (\operatorname{if} R \le \operatorname{infectedCount}\left(adj, f, v\right) \operatorname{then} 1 \operatorname{else} 0))$$

*Formalization.* `D5/S3/Combinatorics/WheelHivExtinctionRefutation.step` (`✓ std3`).

*Citation.* Manuel A. Espinosa-García, Ana Paulina Figueroa, Julián A. Fresán-Figueroa, Gerardo L. Maldonado, L. Ariadna Sánchez-Solís (2026). *Extinction thresholds in a graph-based model of HIV infection dynamics*. DOI: [10.48550/arXiv.2608.00340](https://doi.org/10.48550/arXiv.2608.00340). URL: <https://arxiv.org/abs/2608.00340v1>.

*Commentary.*

An infected vertex (1) dies (2). A healthy vertex (0) becomes infected when at least one neighbour is infected and stays healthy otherwise. A dead vertex (2) is replaced by an infected one when at least R neighbours are infected and by a healthy one otherwise.

**Definition 1.4 (The extinction set).**

$$R \in \operatorname{extinctionSet}\left(n, adj\right) \Leftrightarrow (0 < R \land \left(\forall f0 \in \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right),\; \exists t \in \mathbb{N},\; \left(\operatorname{step}\left(adj, R\right)^{t}\right)\left(\operatorname{castSucc}\left(f0\right)\right) = 0\right))$$

*Formalization.* `D5/S3/Combinatorics/WheelHivExtinctionRefutation.extinctionSet` (`✓ std3`).

*Citation.* Manuel A. Espinosa-García, Ana Paulina Figueroa, Julián A. Fresán-Figueroa, Gerardo L. Maldonado, L. Ariadna Sánchez-Solís (2026). *Extinction thresholds in a graph-based model of HIV infection dynamics*. DOI: [10.48550/arXiv.2608.00340](https://doi.org/10.48550/arXiv.2608.00340). URL: <https://arxiv.org/abs/2608.00340v1>.

*Commentary.*

The positive R such that every admissible initial state f0, a map from the vertices to {0, 1} read as a state through castSucc, reaches the all-healthy state 0 after some number t of steps.

**Definition 1.5 (Conjecture 1).**

$$claim \Leftrightarrow ((\forall n \in \mathbb{N},\; (\operatorname{Even}\left(n\right) \land 12 \le n) \Rightarrow (\operatorname{extinctionSet}\left(n, \operatorname{wheelAdj}\left(n\right)\right) = \{3\} \cup \{R:n - 1 \le R\})) \land (\forall n \in \mathbb{N},\; (\operatorname{Odd}\left(n\right) \land 17 \le n) \Rightarrow (\operatorname{extinctionSet}\left(n, \operatorname{wheelAdj}\left(n\right)\right) = \{4\} \cup \{R:n - 1 \le R\})))$$

*Formalization.* `D5/S3/Combinatorics/WheelHivExtinctionRefutation.claim` (`✓ std3`).

*Citation.* Manuel A. Espinosa-García, Ana Paulina Figueroa, Julián A. Fresán-Figueroa, Gerardo L. Maldonado, L. Ariadna Sánchez-Solís (2026). *Extinction thresholds in a graph-based model of HIV infection dynamics*. DOI: [10.48550/arXiv.2608.00340](https://doi.org/10.48550/arXiv.2608.00340). URL: <https://arxiv.org/abs/2608.00340v1>.

*Commentary.*

Conjecture 1 of the source: the extinction set of W_n is {3} together with all R >= n - 1 for even n >= 12, and {4} together with all R >= n - 1 for odd n >= 17.

**Theorem 1.6 (Refutation).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WheelHivExtinctionRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/espinosa-garcia-2026-hiv-wheel-extinction-refutation` (refuted) by `D5/S3/Combinatorics/WheelHivExtinctionRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"espinosa-garcia-2026-hiv-wheel-extinction-refutation","declaration_gid":"D5/S3/Combinatorics/WheelHivExtinctionRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Manuel A. Espinosa-García, Ana Paulina Figueroa, Julián A. Fresán-Figueroa, Gerardo L. Maldonado, L. Ariadna Sánchez-Solís (2026). *Extinction thresholds in a graph-based model of HIV infection dynamics*. DOI: [10.48550/arXiv.2608.00340](https://doi.org/10.48550/arXiv.2608.00340). URL: <https://arxiv.org/abs/2608.00340v1>.

*Commentary.*

All 2^18 admissible initial states of W_18 are simulated at once. For each vertex, one natural number records in its bit j whether that vertex is infected in the state reached from the j-th initial state, whose vertex v is infected exactly when bit v of j is set, and a second number records the dead vertices. One step of the rules becomes bitwise operations on these numbers; for the dead hub, whether at least 4 of its 17 neighbours are infected is decided bit by bit by counting masks. The proof shows that at every bit the masks after t steps describe the t-th state of the corresponding initial state, and the kernel evaluates the masks after 25 steps to zero. Hence every admissible initial state reaches the all-healthy state by time 25 when R = 4, so 4 lies in the extinction set of W_18, whereas 4 is neither 3 nor at least 17.

## References

- Truth anchor: `D5/S3/Combinatorics/WheelHivExtinctionRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/WheelHivExtinctionRefutation.extinctionSet`
- Truth anchor: `D5/S3/Combinatorics/WheelHivExtinctionRefutation.infectedCount`
- Truth anchor: `D5/S3/Combinatorics/WheelHivExtinctionRefutation.result`
- Truth anchor: `D5/S3/Combinatorics/WheelHivExtinctionRefutation.step`
- Truth anchor: `D5/S3/Combinatorics/WheelHivExtinctionRefutation.wheelAdj`
