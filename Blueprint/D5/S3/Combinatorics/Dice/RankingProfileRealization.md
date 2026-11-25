# Realization of a complete ranking profile

## Abstract

A finite cubic criterion for the six strict ranking probabilities of three independent real variables.

**Definition 1.1 (Order of the six coordinates).**

$$\operatorname{rankOrder}\left(0\right), \operatorname{rankOrder}\left(1\right), \operatorname{rankOrder}\left(2\right), \operatorname{rankOrder}\left(3\right), \operatorname{rankOrder}\left(4\right), \operatorname{rankOrder}\left(5\right) = (0,1,2), (0,2,1), (1,0,2), (1,2,0), (2,0,1), (2,1,0)$$

*Formalization.* `D5/S3/Combinatorics/Dice/RankingProfileRealization.rankOrder` (`✓ std3`).

*Citation.* Sándor Bozóki, László Csató, József Temesi (2026). *Condorcet’s nontransitive dice: A minimal realization of a complete ranking profile*. DOI: [10.48550/arXiv.2611.23308](https://doi.org/10.48550/arXiv.2611.23308). URL: <https://arxiv.org/abs/2611.23308v1>.

*Commentary.*

Roles 0, 1 and 2 denote X, Y and Z. Each row lists the roles from largest to smallest. The six rows follow Equation (7) in the order XYZ, XZY, YXZ, YZX, ZXY, ZYX.

**Definition 1.2 (Strict ranking probabilities).**

$$\forall Omega \in \mathit{Type}, m \in \operatorname{MeasurableSpace}\left(\mathit{Omega}\right), mu \in \operatorname{Measure}\left(\mathit{Omega}\right), X \in (\operatorname{Fin}\left(3\right) \to (\mathit{Omega} \to \mathbb{R})), t \in \operatorname{Fin}\left(6\right),\; \operatorname{realRankProfile}\left(\mathit{mu}, X, t\right) = \operatorname{measureReal}\left(\mathit{mu}, \{\mathit{omega} \mid X\left(\operatorname{rankOrder}\left(t, 1\right), \mathit{omega}\right) < X\left(\operatorname{rankOrder}\left(t, 0\right), \mathit{omega}\right) \land X\left(\operatorname{rankOrder}\left(t, 2\right), \mathit{omega}\right) < X\left(\operatorname{rankOrder}\left(t, 1\right), \mathit{omega}\right)\}\right)$$

*Formalization.* `D5/S3/Combinatorics/Dice/RankingProfileRealization.realRankProfile` (`✓ std3`).

*Citation.* Sándor Bozóki, László Csató, József Temesi (2026). *Condorcet’s nontransitive dice: A minimal realization of a complete ranking profile*. DOI: [10.48550/arXiv.2611.23308](https://doi.org/10.48550/arXiv.2611.23308). URL: <https://arxiv.org/abs/2611.23308v1>.

*Commentary.*

The coordinate is the real value of the measure of the corresponding strict ordering event. The two strict inequalities exclude all ties. In the theorem the measure is a probability measure and the coordinate functions are measurable.

**Theorem 1.3 (Exact criterion for Problem 5).**

$$\forall v \in (\operatorname{Fin}\left(6\right) \to \mathbb{R}),\; \left(\left(\forall t \in \operatorname{Fin}\left(6\right),\; 0 \le v\left(t\right)\right) \land \sum_{t:\operatorname{Fin}\left(6\right)} (v\left(t\right)) = 1\right) \Rightarrow \left(\left(\forall Omega \in \mathit{Type}, m \in \operatorname{MeasurableSpace}\left(\mathit{Omega}\right), mu \in \operatorname{Measure}\left(\mathit{Omega}\right), X \in (\operatorname{Fin}\left(3\right) \to (\mathit{Omega} \to \mathbb{R})),\; \left(\operatorname{IsProbabilityMeasure}\left(\mathit{mu}\right) \land \left(\left(\left(\forall i \in \operatorname{Fin}\left(3\right),\; \operatorname{Measurable}\left(X\left(i\right)\right)\right) \land \operatorname{iIndepFun}\left(X, \mathit{mu}\right)\right) \land \operatorname{realRankProfile}\left(\mathit{mu}, X\right) = v\right)\right) \Rightarrow v \in \mathit{finiteTest15}\right) \land \left(v \in \mathit{finiteTest15} \Rightarrow \left(\exists mu \in \operatorname{Measure}\left((\operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(15\right))\right), X \in (\operatorname{Fin}\left(3\right) \to ((\operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(15\right)) \to \mathbb{R})),\; \operatorname{IsProbabilityMeasure}\left(\mathit{mu}\right) \land \left(\left(\left(\forall i \in \operatorname{Fin}\left(3\right),\; \operatorname{Measurable}\left(X\left(i\right)\right)\right) \land \operatorname{iIndepFun}\left(X, \mathit{mu}\right)\right) \land \operatorname{realRankProfile}\left(\mathit{mu}, X\right) = v\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Dice/RankingProfileRealization.problem_five` (`✓ std3`). ∎

*Resolves.* `Problems/bozoki-csato-temesi-2026-ranking-profile` (proved) by `D5/S3/Combinatorics/Dice/RankingProfileRealization.problem_five`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bozoki-csato-temesi-2026-ranking-profile","declaration_gid":"D5/S3/Combinatorics/Dice/RankingProfileRealization.problem_five","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Sándor Bozóki, László Csató, József Temesi (2026). *Condorcet’s nontransitive dice: A minimal realization of a complete ranking profile*. DOI: [10.48550/arXiv.2611.23308](https://doi.org/10.48550/arXiv.2611.23308). URL: <https://arxiv.org/abs/2611.23308v1>.

*Commentary.*

For every simplex profile, including the boundary, necessity applies on every measurable probability space. Sum one makes the three real values pairwise distinct almost surely. Separately quantize the variables with role-specific offsets. Measurability preserves independence, the offsets give disjoint finite ranges, and bounded convergence gives convergence of the six strict ranking probabilities.

For finite disjoint supports, hold two marginal laws fixed. Their two strict comparison probabilities are the sums of two complementary blocks of three coordinates as the third variable varies. Four coordinates therefore determine the other two. Carathéodory compresses the varying marginal to at most five original support values. Apply this to each role in turn and relabel the union in increasing order. The sparse marginal simplexes are finite unions of compact faces, so the continuous cubic image is closed and contains the limiting profile.

For sufficiency take the product law on triples of ordered labels. Evaluating its three coordinates as reals gives independent measurable variables, and summing the product masses of all strictly ordered triples gives exactly the six cubic sums.

## References

- Truth anchor: `D5/S3/Combinatorics/Dice/RankingProfileRealization.problem_five`
- Truth anchor: `D5/S3/Combinatorics/Dice/RankingProfileRealization.rankOrder`
- Truth anchor: `D5/S3/Combinatorics/Dice/RankingProfileRealization.realRankProfile`
- Dependency: [D5/S3/Combinatorics/Dice/RankingProfileFiniteGrid](RankingProfileFiniteGrid.md)
