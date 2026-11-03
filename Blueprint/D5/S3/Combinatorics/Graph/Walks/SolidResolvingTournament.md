# SolidResolvingTournament

## Abstract

SolidResolvingTournament

**Definition 1.1 (claim).**

$$claim = \left(\left(\forall R \in \left(\operatorname{Fin}\left(6\right)\right) \to \left(\left(\operatorname{Fin}\left(6\right)\right) \to \left(Prop\right)\right),\; \operatorname{IsTournament}\left(R\right) \Rightarrow 4 \le \operatorname{solidMetricDimension}\left(R\right)\right) \land \left(\left(\forall R \in \left(\operatorname{Fin}\left(7\right)\right) \to \left(\left(\operatorname{Fin}\left(7\right)\right) \to \left(Prop\right)\right),\; \operatorname{IsTournament}\left(R\right) \Rightarrow 5 \le \operatorname{solidMetricDimension}\left(R\right)\right) \land \left(\left(\forall R \in \left(\operatorname{Fin}\left(8\right)\right) \to \left(\left(\operatorname{Fin}\left(8\right)\right) \to \left(Prop\right)\right),\; \operatorname{IsTournament}\left(R\right) \Rightarrow 5 \le \operatorname{solidMetricDimension}\left(R\right)\right) \land \left(\left(\forall R \in \left(\operatorname{Fin}\left(9\right)\right) \to \left(\left(\operatorname{Fin}\left(9\right)\right) \to \left(Prop\right)\right),\; \operatorname{IsTournament}\left(R\right) \Rightarrow 5 \le \operatorname{solidMetricDimension}\left(R\right)\right) \land \left(\left(\forall R \in \left(\operatorname{Fin}\left(10\right)\right) \to \left(\left(\operatorname{Fin}\left(10\right)\right) \to \left(Prop\right)\right),\; \operatorname{IsTournament}\left(R\right) \Rightarrow 5 \le \operatorname{solidMetricDimension}\left(R\right)\right) \land \left(\forall R \in \left(\operatorname{Fin}\left(11\right)\right) \to \left(\left(\operatorname{Fin}\left(11\right)\right) \to \left(Prop\right)\right),\; \operatorname{IsTournament}\left(R\right) \Rightarrow 6 \le \operatorname{solidMetricDimension}\left(R\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournament.claim` (`✓ std3`).

*Citation.* Anni Hakanen and Pavan P D (2026). *Solid-Resolving Sets on Directed Graphs*. URL: <https://arxiv.org/abs/2610.35041v1>.

*Commentary.*

We have βₛ(K⃗₆) ≥ 4, βₛ(K⃗₇) ≥ 5,  βₛ(K⃗₈) ≥ 5, βₛ(K⃗₉) ≥ 5, βₛ(K⃗₁₀) ≥ 5 and βₛ(K⃗₁₁) ≥ 6. (Conjecture 3.4, page 8.) Each R ranges over all relations on Fin n; IsTournament requires no loops and exactly one arc between distinct vertices. The six orders are 6, 7, 8, 9, 10 and 11.

**Theorem 1.2 (result).**

$$\left(\forall R \in \left(\operatorname{Fin}\left(6\right)\right) \to \left(\left(\operatorname{Fin}\left(6\right)\right) \to \left(Prop\right)\right),\; \operatorname{IsTournament}\left(R\right) \Rightarrow 4 \le \operatorname{solidMetricDimension}\left(R\right)\right) \land \left(\left(\forall R \in \left(\operatorname{Fin}\left(7\right)\right) \to \left(\left(\operatorname{Fin}\left(7\right)\right) \to \left(Prop\right)\right),\; \operatorname{IsTournament}\left(R\right) \Rightarrow 5 \le \operatorname{solidMetricDimension}\left(R\right)\right) \land \left(\left(\forall R \in \left(\operatorname{Fin}\left(8\right)\right) \to \left(\left(\operatorname{Fin}\left(8\right)\right) \to \left(Prop\right)\right),\; \operatorname{IsTournament}\left(R\right) \Rightarrow 5 \le \operatorname{solidMetricDimension}\left(R\right)\right) \land \left(\left(\forall R \in \left(\operatorname{Fin}\left(9\right)\right) \to \left(\left(\operatorname{Fin}\left(9\right)\right) \to \left(Prop\right)\right),\; \operatorname{IsTournament}\left(R\right) \Rightarrow 5 \le \operatorname{solidMetricDimension}\left(R\right)\right) \land \left(\left(\forall R \in \left(\operatorname{Fin}\left(10\right)\right) \to \left(\left(\operatorname{Fin}\left(10\right)\right) \to \left(Prop\right)\right),\; \operatorname{IsTournament}\left(R\right) \Rightarrow 5 \le \operatorname{solidMetricDimension}\left(R\right)\right) \land \left(\forall R \in \left(\operatorname{Fin}\left(11\right)\right) \to \left(\left(\operatorname{Fin}\left(11\right)\right) \to \left(Prop\right)\right),\; \operatorname{IsTournament}\left(R\right) \Rightarrow 6 \le \operatorname{solidMetricDimension}\left(R\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournament.result` (`✓ std3`). ∎

*Resolves.* `Problems/solid-resolving-tournament` (proved) by `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournament.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"solid-resolving-tournament","declaration_gid":"D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournament.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Anni Hakanen and Pavan P D (2026). *Solid-Resolving Sets on Directed Graphs*. URL: <https://arxiv.org/abs/2610.35041v1>.

*Commentary.*

The six lower bounds hold for every tournament at the indicated orders. A solid set with three, four or five landmarks forces total order at most four, six or ten. Outside vertices give mutually incomparable distance profiles. Chain covers of the profiles for each induced landmark tournament bound their number; terminal components also cover infinite distances.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournament.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournament.result`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentBase](SolidResolvingTournamentBase.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles](SolidResolvingTournamentProfiles.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal](SolidResolvingTournamentTerminal.md)
- Dependency: [D5/S3/ConceptDynamics/GraphIrregularity/LinkIrregularTournamentExistence](../../../ConceptDynamics/GraphIrregularity/LinkIrregularTournamentExistence.md)
