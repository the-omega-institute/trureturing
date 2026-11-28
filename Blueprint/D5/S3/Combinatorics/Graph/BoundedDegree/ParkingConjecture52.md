# A subcubic counterexample to stochastic dominance in discrete parking

## Abstract

A fifteen-vertex tree of maximum degree three reverses the proposed lower-tail inequality at six parked vertices.

**Definition 1.1 (Removing the chosen vertex and its neighbors).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/ParkingConjecture52.after`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/ParkingConjecture52.after` (`✓ std3`).

*Citation.* Robinson Higuita-Diaz, Lykos López, Alejandro Roldán-Correa (2026). *Random Sequential Adsorption versus the Uniform Ensemble of Jammed Configurations: Stochastic Dominance on Graphs*. URL: <https://arxiv.org/abs/2611.14718v2>.

*Commentary.*

The available vertices after choosing v are the elements w of the current set with w distinct from v and no edge from v to w. The transition is on the original simple graph.

**Definition 1.2 (The sequential occupancy CDF).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/ParkingConjecture52.seq`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/ParkingConjecture52.seq` (`✓ std3`).

*Citation.* Robinson Higuita-Diaz, Lykos López, Alejandro Roldán-Correa (2026). *Random Sequential Adsorption versus the Uniform Ensemble of Jammed Configurations: Stochastic Dominance on Graphs*. URL: <https://arxiv.org/abs/2611.14718v2>.

*Commentary.*

With an empty available set the probability of at most k further choices is one for every natural cutoff k. A nonempty set at cutoff zero has probability zero. With a nonempty set at cutoff k+1, average the CDF at cutoff k over the available sets after each possible next choice. Expanding this recursion gives the product of inverse available-set sizes for each complete ordered history. The initial available set is the full vertex set.

**Definition 1.3 (Jammed configurations).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/ParkingConjecture52.jammed`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/ParkingConjecture52.jammed` (`✓ std3`).

*Citation.* Robinson Higuita-Diaz, Lykos López, Alejandro Roldán-Correa (2026). *Random Sequential Adsorption versus the Uniform Ensemble of Jammed Configurations: Stochastic Dominance on Graphs*. URL: <https://arxiv.org/abs/2611.14718v2>.

*Commentary.*

A finite vertex subset is jammed when its underlying set is inclusion-maximal among independent sets of the graph.

**Definition 1.4 (The static occupancy CDF).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/ParkingConjecture52.static`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/ParkingConjecture52.static` (`✓ std3`).

*Citation.* Robinson Higuita-Diaz, Lykos López, Alejandro Roldán-Correa (2026). *Random Sequential Adsorption versus the Uniform Ensemble of Jammed Configurations: Stochastic Dominance on Graphs*. URL: <https://arxiv.org/abs/2611.14718v2>.

*Commentary.*

Filter the power set of the full vertex set to the jammed sets. Divide the number of those sets with at most k vertices by the number of all jammed sets. The ratio is taken in the exact rationals.

**Definition 1.5 (Conjecture 5.2).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)] \operatorname{maxDegree}\left(G\right) \le 3 \Rightarrow \left(\forall k \in Nat,\; \operatorname{seq}\left(G, k, univ\right) \le \operatorname{static}\left(G, k\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/ParkingConjecture52.Conjecture52` (`✓ std3`).

*Citation.* Robinson Higuita-Diaz, Lykos López, Alejandro Roldán-Correa (2026). *Random Sequential Adsorption versus the Uniform Ensemble of Jammed Configurations: Stochastic Dominance on Graphs*. URL: <https://arxiv.org/abs/2611.14718v2>.

*Commentary.*

Definition 2.1 compares the probabilities of occupancy at most k for every integer k. Both occupancies are nonnegative, so natural cutoffs suffice. Conjecture 5.2 quantifies over every finite simple graph with maximum degree at most three.

**Theorem 1.6 (Refutation of Conjecture 5.2).**

$$\neg \left(\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)] \operatorname{maxDegree}\left(G\right) \le 3 \Rightarrow \left(\forall k \in Nat,\; \operatorname{seq}\left(G, k, univ\right) \le \operatorname{static}\left(G, k\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/BoundedDegree/ParkingConjecture52.not_conjecture52` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robinson Higuita-Diaz, Lykos López, Alejandro Roldán-Correa (2026). *Random Sequential Adsorption versus the Uniform Ensemble of Jammed Configurations: Stochastic Dominance on Graphs*. URL: <https://arxiv.org/abs/2611.14718v2>.

*Commentary.*

Use vertices 0 through 14 and edges (0,7), (1,8), (2,9), (3,10), (4,11), (0,12), (1,12), (5,12), (2,13), (3,13), (6,13), (4,14), (7,14) and (9,14). Maximal independent sets are counted by testing independence and coverage by closed neighborhoods. Exactly one of the 55 sets has size at most six. Conditioning on the first choice and evaluating the residual-set recurrence gives sequential CDF 64/3375. The static CDF is 1/55. The sequential CDF exceeds it by 29/37125.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/ParkingConjecture52.Conjecture52`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/ParkingConjecture52.after`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/ParkingConjecture52.jammed`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/ParkingConjecture52.not_conjecture52`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/ParkingConjecture52.seq`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/ParkingConjecture52.static`
