# Four alternatives refute the deterministic √13 guarantee

## Abstract

For every deterministic rule on four labeled alternatives and twelve labeled voters, one fixed compatible election gives distortion above √13.

**Definition 1.1 (Alternative labels).**

$$Alternative = \operatorname{Fin}\left(4\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives.Alternative` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* MohammadHossein Ghasemi; Masoud Seddighin; Saeed Seddighin (2026). *Distortion in Online Voting*. DOI: [10.48550/arXiv.2611.25709](https://doi.org/10.48550/arXiv.2611.25709). URL: <https://arxiv.org/abs/2611.25709v1>.

*Commentary.*

The four alternative labels are 0, 1, 2 and 3.

**Definition 1.2 (Voter and alternative labels).**

$$\forall n \in Nat,\; \operatorname{Label}\left(n\right) = \operatorname{Sum}\left(\operatorname{Fin}\left(n\right), Alternative\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives.Label` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* MohammadHossein Ghasemi; Masoud Seddighin; Saeed Seddighin (2026). *Distortion in Online Voting*. DOI: [10.48550/arXiv.2611.25709](https://doi.org/10.48550/arXiv.2611.25709). URL: <https://arxiv.org/abs/2611.25709v1>.

*Commentary.*

The left summand tags the n voters and the right summand tags the four alternatives. Their locations in an election may coincide.

**Definition 1.3 (Full ballots).**

$$\forall n \in Nat,\; \operatorname{Profile}\left(n\right) = \left(\operatorname{Fin}\left(n\right) \to \{rank: Alternative \to Alternative \mid \operatorname{Injective}\left(rank\right)\}\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives.Profile` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* MohammadHossein Ghasemi; Masoud Seddighin; Saeed Seddighin (2026). *Distortion in Online Voting*. DOI: [10.48550/arXiv.2611.25709](https://doi.org/10.48550/arXiv.2611.25709). URL: <https://arxiv.org/abs/2611.25709v1>.

*Commentary.*

Each voter supplies an injective rank map on the four alternatives. A smaller rank means an earlier ballot position.

**Definition 1.4 (Arrival order).**

$$Arrival = \operatorname{Equiv}\left(\operatorname{Fin}\left(4\right), Alternative\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives.Arrival` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* MohammadHossein Ghasemi; Masoud Seddighin; Saeed Seddighin (2026). *Distortion in Online Voting*. DOI: [10.48550/arXiv.2611.25709](https://doi.org/10.48550/arXiv.2611.25709). URL: <https://arxiv.org/abs/2611.25709v1>.

*Commentary.*

The equivalence sends each arrival position to its alternative label.

**Definition 1.5 (Prefix observations).**

$$\forall n \in Nat,\; \operatorname{Observation}\left(n\right): Type$$

*Formalization.* `D5/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives.Observation` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* MohammadHossein Ghasemi; Masoud Seddighin; Saeed Seddighin (2026). *Distortion in Online Voting*. DOI: [10.48550/arXiv.2611.25709](https://doi.org/10.48550/arXiv.2611.25709). URL: <https://arxiv.org/abs/2611.25709v1>.

*Commentary.*

The arrived field is a list of alternatives in arrival order. The prefers field returns a Boolean for a voter in Fin n and an ordered pair of alternatives.

**Definition 1.6 (Observing a ballot profile).**

$$\forall n \in Nat,\; \forall o \in Arrival,\; \forall p \in \operatorname{Profile}\left(n\right),\; \forall q \in Nat,\; \operatorname{observe}\left(o, p, q\right): \operatorname{Observation}\left(n\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives.observe` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* MohammadHossein Ghasemi; Masoud Seddighin; Saeed Seddighin (2026). *Distortion in Online Voting*. DOI: [10.48550/arXiv.2611.25709](https://doi.org/10.48550/arXiv.2611.25709). URL: <https://arxiv.org/abs/2611.25709v1>.

*Commentary.*

The arrived field takes the first q labels in the arrival order. The prefers field is true precisely when both arrival positions are less than q and the first alternative has smaller full-ballot rank for that voter.

**Definition 1.7 (Deterministic rules).**

$$\forall n \in Nat,\; \operatorname{Rule}\left(n\right) = (\operatorname{List}\left(\operatorname{Observation}\left(n\right)\right) \to \left(\operatorname{List}\left(Bool\right) \to Bool\right))$$

*Formalization.* `D5/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives.Rule` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* MohammadHossein Ghasemi; Masoud Seddighin; Saeed Seddighin (2026). *Distortion in Online Voting*. DOI: [10.48550/arXiv.2611.25709](https://doi.org/10.48550/arXiv.2611.25709). URL: <https://arxiv.org/abs/2611.25709v1>.

*Commentary.*

A rule uses the ordered list of all observations so far and the list of its earlier decisions. True switches to the latest arrival and false keeps the incumbent.

**Definition 1.8 (Final winner).**

$$\forall n \in Nat,\; finalWinner: \operatorname{Rule}\left(n\right) \to \left(Arrival \to \left(\operatorname{Profile}\left(n\right) \to Alternative\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives.finalWinner` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* MohammadHossein Ghasemi; Masoud Seddighin; Saeed Seddighin (2026). *Distortion in Online Voting*. DOI: [10.48550/arXiv.2611.25709](https://doi.org/10.48550/arXiv.2611.25709). URL: <https://arxiv.org/abs/2611.25709v1>.

*Commentary.*

The incumbent starts at the first arrival. For q equal to 2, 3 and 4, apply the rule to observations 1 through q and the preceding decisions from rounds 2 through q − 1. Keep the incumbent on false and replace it with the q-th arrival on true. Return the incumbent at the end of round four.

**Definition 1.9 (Compatible metric elections).**

$$\forall n \in Nat,\; \operatorname{Election}\left(n\right): Type 1$$

*Formalization.* `D5/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives.Election` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* MohammadHossein Ghasemi; Masoud Seddighin; Saeed Seddighin (2026). *Distortion in Online Voting*. DOI: [10.48550/arXiv.2611.25709](https://doi.org/10.48550/arXiv.2611.25709). URL: <https://arxiv.org/abs/2611.25709v1>.

*Commentary.*

An election carries a type Space with a MetricSpace structure, a location for each Label, an Arrival and a Profile. For each voter and each pair of alternatives, a strictly smaller candidate-to-voter distance requires a strictly smaller ballot rank. Each full strict ballot orders distance ties consistently across all prefixes.

**Definition 1.10 (Social cost).**

$$\forall n \in Nat,\; \forall e \in \operatorname{Election}\left(n\right),\; \forall a \in Alternative,\; \operatorname{socialCost}\left(e, a\right) = \sum_{v: \operatorname{Fin}\left(n\right)} \operatorname{dist}\left(\operatorname{location}\left(e, \operatorname{inr}\left(a\right)\right), \operatorname{location}\left(e, \operatorname{inl}\left(v\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives.socialCost` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* MohammadHossein Ghasemi; Masoud Seddighin; Saeed Seddighin (2026). *Distortion in Online Voting*. DOI: [10.48550/arXiv.2611.25709](https://doi.org/10.48550/arXiv.2611.25709). URL: <https://arxiv.org/abs/2611.25709v1>.

*Commentary.*

The sum uses the election's metric and includes every voter. The right injection supplies the alternative label and the left injection supplies the voter label.

**Definition 1.11 (The four-alternative guarantee).**

$$claim \Leftrightarrow (\exists r \in \operatorname{Rule}\left(12\right),\; \forall e \in \operatorname{Election}\left(12\right),\; \forall a \in Alternative,\; \operatorname{socialCost}\left(e, \operatorname{finalWinner}\left(r, \operatorname{arrival}\left(e\right), \operatorname{profile}\left(e\right)\right)\right) \le \sqrt{13} \cdot \operatorname{socialCost}\left(e, a\right))$$

*Formalization.* `D5/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* MohammadHossein Ghasemi; Masoud Seddighin; Saeed Seddighin (2026). *Distortion in Online Voting*. DOI: [10.48550/arXiv.2611.25709](https://doi.org/10.48550/arXiv.2611.25709). URL: <https://arxiv.org/abs/2611.25709v1>.

*Commentary.*

Four labeled alternatives arrive in permutation order. Each of twelve labeled voters has a full strict ballot compatible with distances in a common metric. Strictly closer alternatives rank earlier, and each ballot orders ties consistently. At each arrival the rule sees all previous and current labeled prefix comparisons and arrival prefixes, along with its own earlier keep-or-switch decisions.

The first arrival initializes the incumbent. Every later decision retains it or switches to the latest arrival. The social cost is the sum of the twelve voter distances. The comparison against every alternative expresses the guarantee against the attained minimum over the full election.

**Theorem 1.12 (The deterministic guarantee fails at four alternatives).**

$$\neg (\exists r \in \operatorname{Rule}\left(12\right),\; \forall e \in \operatorname{Election}\left(12\right),\; \forall a \in Alternative,\; \operatorname{socialCost}\left(e, \operatorname{finalWinner}\left(r, \operatorname{arrival}\left(e\right), \operatorname{profile}\left(e\right)\right)\right) \le \sqrt{13} \cdot \operatorname{socialCost}\left(e, a\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* MohammadHossein Ghasemi; Masoud Seddighin; Saeed Seddighin (2026). *Distortion in Online Voting*. DOI: [10.48550/arXiv.2611.25709](https://doi.org/10.48550/arXiv.2611.25709). URL: <https://arxiv.org/abs/2611.25709v1>.

*Commentary.*

Section 6 asks, “An interesting open question is whether this guarantee can be extended to elections with more than three alternatives, or whether additional alternatives necessarily lead to higher distortion.”

The certificate uses the order 0, 1, 2, 3. The labeled six-to-six opening is shared by all leaves. Given the second decision, both fourth profiles extend the same third-round comparisons. Each fourth profile has two compatible metrics with the same full ballots, one for each fourth-round action. Computing the decisions selects one full election, whose run reproduces those decisions even when the rule uses all history and labels.

The finite tables give metric inequalities, compatible rankings and exact social costs. Each leaf has a positive offline minimum, and its squared winner cost is strictly greater than thirteen times the squared minimum. The four ratios are 5503/1503, 6503/1503, 11753/3253 and 7503/2003. The paper's §3 allows the canonical arrival order. A uniform extension to all horizons greater than three would have to cover this four-option, twelve-voter case.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives.Alternative`
- Truth anchor: `D5/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives.Arrival`
- Truth anchor: `D5/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives.Election`
- Truth anchor: `D5/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives.Label`
- Truth anchor: `D5/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives.Observation`
- Truth anchor: `D5/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives.Profile`
- Truth anchor: `D5/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives.Rule`
- Truth anchor: `D5/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives.claim`
- Truth anchor: `D5/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives.finalWinner`
- Truth anchor: `D5/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives.observe`
- Truth anchor: `D5/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives.result`
- Truth anchor: `D5/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives.socialCost`
