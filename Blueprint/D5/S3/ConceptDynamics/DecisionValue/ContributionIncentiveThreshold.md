# Contribution Incentive Threshold

## Abstract

Binary contribution is dominant exactly at the source compensation threshold.

**Theorem 1.1 (Contribution becomes dominant at the compensation threshold).**

$$n \in \mathbb{N}, 2 \leq n, b, c, \tau \in \mathbb{R},\\{}b > c > \frac{b}{n},\\{}\operatorname{payoff}(\rho, i, a) = \frac{b}{n} \sum_{j \in \operatorname{Fin}(n)} a_{j} - c a_{i} + \rho a_{i},\\{}\operatorname{Weak}(\rho) \iff \forall i \in \operatorname{Fin}(n), a: \operatorname{Fin}(n) \to \{0, 1\}, \operatorname{payoff}(\rho, i, \operatorname{update}(a, i, 0)) \leq \operatorname{payoff}(\rho, i, \operatorname{update}(a, i, 1)),\\{}\operatorname{Strict}(\rho) \iff \forall i \in \operatorname{Fin}(n), a: \operatorname{Fin}(n) \to \{0, 1\}, \operatorname{payoff}(\rho, i, \operatorname{update}(a, i, 0)) < \operatorname{payoff}(\rho, i, \operatorname{update}(a, i, 1))\\{}\Rightarrow (\operatorname{Weak}(\tau) \iff \tau \geq c - \frac{b}{n}) \land\\{}(\tau > c - \frac{b}{n} \Rightarrow \operatorname{Strict}(\tau)) \land\\{}\operatorname{IsLeast}(\{\rho \in \mathbb{R} \mid \operatorname{Weak}(\rho)\}, c - \frac{b}{n}).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DecisionValue/ContributionIncentiveThreshold.contribution_incentive_threshold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There are n at least two agents and each binary profile records whether each agent contributes. The aggregate is constructed from the selected action and the finite sum over every other agent.

The compensated utility is the common per-agent benefit b/n times total contribution, minus the contributor's cost c, plus compensation rho. The source restrictions b greater than c greater than b/n are public.

Updating one agent from non-contribution to contribution changes utility by b/n-c+rho, independently of the other actions. Hence weak dominance is equivalent to rho at least c-b/n and strict dominance follows above that threshold.

The public conclusion also states that c-b/n is the least member of the set of compensations inducing weak dominance. Funding, allocation, and fairness are identified by the source as separate normative questions and are not promoted to universal mathematical claims.

Repository and pinned Mathlib searches found no exact theorem packaging the source payoff construction and all three threshold clauses.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DecisionValue/ContributionIncentiveThreshold.contribution_incentive_threshold`
