---
bibkey: ghasemi2026onlinevoting
authors: MohammadHossein Ghasemi; Masoud Seddighin; Saeed Seddighin
year: 2026
title: Distortion in Online Voting
doi: 10.48550/arXiv.2611.25709
url: https://arxiv.org/abs/2611.25709v1
claim: Section 6 asks whether the deterministic metric distortion guarantee of √13 for three alternatives extends to elections with more than three alternatives.
strata_touched:
  - D5/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives
license: citation-only
triage: anchor
---

<!-- GID: D5/L/ConceptDynamics/ghasemi2026onlinevoting -->

# Deterministic metric distortion beyond three alternatives

Section 6, second question, immediately after discussing the tight three-alternative
bound of √13 over all electorate sizes, asks:

> An interesting open question is whether this guarantee can be extended to elections with more than three alternatives, or whether additional alternatives necessarily lead to higher distortion.

[arXiv:2611.25709v1, §6, p. 24](https://arxiv.org/html/2611.25709v1#S6.p3.1)

In §3 a fixed set of voters ranks the alternatives seen so far at each arrival.
The rule must retain its incumbent or irrevocably switch to the new alternative.
The metric setting uses one common metric space and sums voter distances.
The offline benchmark takes the minimum over the full election. The paper
explicitly permits numbering the alternatives by arrival order. The four-option
claim uses that admissible order for the counterexample and allows the rule to
depend on voter and alternative labels and all observed history.
[§3 online model](https://arxiv.org/html/2611.25709v1#S3.SS0.SSS0.Px1) ·
[§3 metric model](https://arxiv.org/html/2611.25709v1#S3)

The uniform extension includes the four-option, twelve-voter case, so a
counterexample for every rule on one order in that case excludes the uniform
guarantee. A rule may be specialized to that horizon, electorate size and order.
The preregistered pointwise strengthening concerns every fixed horizon at least
four. It is part of the same problem and supplies a lower bound, without
settling the exact higher-horizon distortion or strict increases between
successive higher horizons.
[Problem and certificate](https://github.com/the-omega-institute/trureturing/issues/32348)
