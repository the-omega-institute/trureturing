---
slug: ghasemi-seddighin-seddighin-2026-deterministic-metric-extension
bibkey: ghasemi2026onlinevoting
doi: 10.48550/arXiv.2611.25709
url: https://arxiv.org/abs/2611.25709v1
triage: theorem
motivation_gids:
  - D5/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives.result
---

# The deterministic metric guarantee beyond three alternatives

## Problem

Ghasemi, Seddighin and Seddighin, *Distortion in Online Voting*,
arXiv:2611.25709v1, §6, second question, p. 24:

> An interesting open question is whether this guarantee can be extended to elections with more than three alternatives, or whether additional alternatives necessarily lead to higher distortion.

The guarantee is √13 in the deterministic metric model, over all electorate
sizes. Section 3 permits numbering the alternatives in arrival order. Any
uniform extension to all horizons greater than three would give a rule for four
alternatives and twelve voters that works in particular on the canonical order
0, 1, 2, 3. The fixed-order refutation therefore suffices even if the rule knows
that order and may specialize to it.
[Question](https://arxiv.org/html/2611.25709v1#S6.p3.1) ·
[Online model](https://arxiv.org/html/2611.25709v1#S3.SS0.SSS0.Px1)

## Claim and counterexample

The Lean `claim : Prop` says that some deterministic rule on twelve labeled
voters and four labeled alternatives guarantees, for every compatible election
and every alternative a, that the winner's cost is at most √13 times the cost
of a. Since √13 is positive and the four alternatives attain their minimum,
the per-alternative inequalities express exactly the guarantee against that
minimum. The literal settlement theorem is `result : ¬ claim`.

A rule sees every labeled ballot restricted to the arrived prefix, including
previously rejected alternatives. It receives the ordered arrival prefix and
all its past decisions. The first arrival initializes the incumbent. After
that the rule can keep the incumbent or switch to the latest arrival.
A fixed full strict ballot refines the actual metric distances, including a
consistent order on ties.

For each rule one fixed election realizes its computed decision path.
All leaves share the same labeled six-to-six opening. For each opening
decision the third-round comparisons agree across both fourth-round profiles. Each fourth profile has two compatible
metrics, one for each fourth decision. The common metric on all sixteen labels
uses the corresponding integer graph table scaled by 1000 plus one for
distinct labels. The proof checks metric laws, ballot compatibility, prefix
equalities, exact social costs and the positive minimum over all four
alternatives. The cost ratios for the four leaves are 5503/1503, 6503/1503,
11753/3253 and 7503/2003, all strictly above √13.
[Preregistered construction and independent replay](https://github.com/the-omega-institute/trureturing/issues/32348#issuecomment-7045275379)

## Admission and boundary

The source is a tier-1 published question. The preregistration screened §3,
§6, Lemmas 7–9 and 11, the available citation indexes and Lean repositories.
Lemma 8 gives a four-option obstruction to perfect matching, while Lemmas 9
and 11 give the tight three-option bound. The screen found no prior
settlement of the exact threshold question within its recorded coverage.
[Preregistration and search scope](https://github.com/the-omega-institute/trureturing/issues/32348)

The admission basis is `open-problem-resolution`. The proof shape is
`content`. The finite computation `leaf_strict` proves, in every branch,
that 13 times the squared cost of the selected optimum is strictly less than
the squared cost of the produced winner. It uses the exact cost table of the
compatible metric witnesses. The proof of `counterexample` uses that fact
to obtain the strict real inequality after replaying the rule, and `result`
uses that inequality at the actual optimum.

The Lean theorem `Padding.worst_case` gives the pointwise lower bound
11753/3253 > √13 for every horizon m = 4 + k and every prescribed order.
Fresh alternatives follow the old ones in every ballot, in arrival order. Each fresh label
lies at distance 10001 from any other label, so it costs 120012 and preserves
the old minimum. Any incumbent after round four is either the fourth-round
winner or a fresh alternative. This establishes a worst-case lower bound for
deterministic rules at twelve voters. Exact distortion above three alternatives
and strict increases between successive higher horizons are separate claims.
[Pointwise construction](https://github.com/the-omega-institute/trureturing/issues/32348#issuecomment-7045275379)
