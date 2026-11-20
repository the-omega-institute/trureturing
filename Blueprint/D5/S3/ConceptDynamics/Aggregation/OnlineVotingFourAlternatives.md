# Four alternatives refute the deterministic √13 guarantee

## Abstract

Every deterministic rule with four labeled alternatives and twelve labeled voters can exceed distortion √13 in a single fixed compatible election.

**Definition 1.1 (The four-alternative guarantee).**

$$claim \Leftrightarrow (\exists r \in \operatorname{Rule}\left(12\right),\; \forall e \in \operatorname{Election}\left(12\right),\; \forall a \in Alternative,\; \operatorname{socialCost}\left(e, \operatorname{finalWinner}\left(r, \operatorname{arrival}\left(e\right), \operatorname{profile}\left(e\right)\right)\right) \le \sqrt{13} \cdot \operatorname{socialCost}\left(e, a\right))$$

*Formalization.* `D5/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* MohammadHossein Ghasemi; Masoud Seddighin; Saeed Seddighin (2026). *Distortion in Online Voting*. DOI: [10.48550/arXiv.2611.25709](https://doi.org/10.48550/arXiv.2611.25709). URL: <https://arxiv.org/abs/2611.25709v1>.

*Commentary.*

Four labeled alternatives arrive in permutation order. Each of twelve labeled voters has a full strict ballot compatible with distances in a common metric. Strictly closer alternatives rank earlier, and each ballot orders ties consistently. At each arrival the rule sees all previous and current labeled prefix comparisons and arrival prefixes, along with its own earlier keep-or-switch decisions.

The first arrival initializes the incumbent. Every later decision retains it or switches to the latest arrival. The social cost is the sum of the twelve voter distances. The comparison against every alternative expresses the guarantee against the attained minimum over the full election.

**Theorem 1.2 (The deterministic guarantee fails at four alternatives).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives.result` (`✓ std3`). ∎

*Resolves.* `Problems/ghasemi-seddighin-seddighin-2026-deterministic-metric-extension` (refuted) by `D5/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ghasemi-seddighin-seddighin-2026-deterministic-metric-extension","declaration_gid":"D5/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* MohammadHossein Ghasemi; Masoud Seddighin; Saeed Seddighin (2026). *Distortion in Online Voting*. DOI: [10.48550/arXiv.2611.25709](https://doi.org/10.48550/arXiv.2611.25709). URL: <https://arxiv.org/abs/2611.25709v1>.

*Commentary.*

Section 6 asks, “An interesting open question is whether this guarantee can be extended to elections with more than three alternatives, or whether additional alternatives necessarily lead to higher distortion.”

The certificate uses the order 0, 1, 2, 3. The labeled six-to-six opening is shared by all leaves. Given the second decision, both fourth profiles extend the same third-round comparisons. Each fourth profile has two compatible metrics with the same full ballots, one for each fourth-round action. Computing the decisions selects one full election, whose run reproduces those decisions even when the rule uses all history and labels.

The finite tables give metric inequalities, compatible rankings and exact social costs. Each leaf has a positive offline minimum, and its squared winner cost is strictly greater than thirteen times the squared minimum. The paper's §3 allows the canonical arrival order. A uniform extension to all horizons greater than three would have to cover this four-option, twelve-voter case.

**Theorem 1.3 (The lower bound holds at every prescribed horizon).**

$$\forall k \in Nat,\; \forall L \in Type,\; \forall o \in \operatorname{Order}\left(k, L\right),\; \forall r \in \operatorname{Rule}\left(L\right),\; \exists e \in \operatorname{Election}\left(k, L\right),\; \exists b \in L,\; \operatorname{order}\left(e\right) = o \land \left(\left(\forall a \in L,\; \operatorname{cost}\left(e, b\right) \le \operatorname{cost}\left(e, a\right)\right) \land \left(0 < \operatorname{cost}\left(e, b\right) \land \left(\frac{11753}{3253} \cdot \operatorname{cost}\left(e, b\right) \le \operatorname{cost}\left(e, \operatorname{winner}\left(r, e\right)\right) \land \sqrt{13} \cdot \operatorname{cost}\left(e, b\right) < \operatorname{cost}\left(e, \operatorname{winner}\left(r, e\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives.worst_case` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* MohammadHossein Ghasemi; Masoud Seddighin; Saeed Seddighin (2026). *Distortion in Online Voting*. DOI: [10.48550/arXiv.2611.25709](https://doi.org/10.48550/arXiv.2611.25709). URL: <https://arxiv.org/abs/2611.25709v1>.

*Commentary.*

An order is an equivalence from the first four positions and k later positions to the candidate labels. For every such order and every deterministic rule on those labels, one compatible election has that order, a positive offline minimum and the displayed winner-cost bounds.

The proof transports the same four metric leaves to the prescribed labels. Each fresh alternative is ranked after the old ones and costs 120012. Any later switch chooses a fresh alternative, and neither retaining the fourth-round winner nor switching to a fresh alternative decreases the cost. The benchmark still includes the entire extended election.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives.claim`
- Truth anchor: `D5/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives.result`
- Truth anchor: `D5/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives.worst_case`
