---
slug: schiavo-2026-two-run-rent-or-buy
bibkey: schiavo2026repeatedrentorbuy
doi: null
url: https://arxiv.org/abs/2611.06955v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/OnlineAlgorithms/SchiavoTwoRunRentOrBuy.schiavo_section5b_third_question
---

# A competitive rule with two-run additive loss at most 2K

## Problem

Vasco Schiavo, *A Sharp Additive Bound for the Threshold Rule in Repeated Rent-or-Buy*, arXiv:2611.06955v1, §5.B, third question, PDF page 15:

> Can a rule lose at most 2K on two runs and also be c-competitive for some constant c?

There is a real constant $c\ge1$ such that for every real $K>0$ there is a deterministic prefix rule. For every finite input of nonnegative real increments and every comparator schedule on that input, the rule costs at most $c$ times the comparator cost. If the input comprises at most two constant consecutive runs, the same rule also costs at most the comparator cost plus $2K$. [Primary source](https://arxiv.org/pdf/2611.06955v1#page=15)

## Motivation

The ordinary threshold rule is competitive and can approach additive loss $3K$ on two runs. The drop-aware rule attains $2K$ on two runs. The question asks whether one policy can retain the optimal two-run loss with a global competitive guarantee. [Primary source, §5](https://arxiv.org/pdf/2611.06955v1#page=12)

## Gap

The preregistration records arXiv author and TCP acknowledgement searches, the author’s Zenodo version, zero indexed citations in OpenAlex and Semantic Scholar, and a rate-limited citing-works request. The inspected related results concern other timing or comparators, or stochastic objectives. The joint guarantee was not found in the searched scope. [Issue #32378](https://github.com/the-omega-institute/trureturing/issues/32378)

## Route

Use $c=3$. The rule resets at an ordinary threshold crossing, and can also reset at the first strict decrease if an ordinary crossing occurred strictly earlier. A simultaneous crossing and decrease counts as ordinary. A completed ordinary cycle pays for the reserve needed to cover a later extra reset in competitive accounting. The additive proof telescopes the policy and comparator potentials across constant blocks. For an early decrease, it compares costs through the first ordinary reset and then uses the one-block bound on the remaining suffix. If there is no reset, it uses the unfinished-cycle comparison.

## Falsifier

The same rule must meet both bounds using only visible increments. Call $t$ receives the first $t-1$ increments, the comparator chooses each action freely, and the full rent is charged on each reset call and the final call. Empty input, zero rates and a first crossing at the decrease are included. A counterexample would need a comparator schedule on the same input and a violation of one of the two inequalities under its stated hypotheses.

## Evidence

The Lean declaration is GID D5/S3/Combinatorics/OnlineAlgorithms/SchiavoTwoRunRentOrBuy.schiavo_section5b_third_question. Its module imports the proofs of prefix agreement, competitive cycle accounting and the additive constant-block bound. The kernel axiom closure is propext, Classical.choice and Quot.sound. [Public verification](https://github.com/the-omega-institute/trureturing/issues/32378#issuecomment-7047116310)

Current statement ID for the settling declaration is sha256:378dc7713423da3a7126353e7ed49b0a53129a5e5497c19ee0eb3b9586a612b4. The §3.9 audit is incomplete for the settling declaration. [Registration evidence and outstanding targets](https://github.com/the-omega-institute/trureturing/issues/32378#issuecomment-7047523344)

## Triage

Tier 1, preregistered in issue #32378. Resolution proved.

### What the settlement shows

One deterministic prefix rule attains the paper's sharp two-run additive bound and is competitive on arbitrary finite sessions. The proof gives factor three. The other questions in §5.B, including the best bounds over more than two runs, are outside this conclusion.

## ASSUMED-UNVERIFIED

Priority beyond the searched literature remains unverified. The preregistered arXiv source and author query returned three records, and the TCP synonym query returned twelve. OpenAlex (W7225191108) and Semantic Scholar each listed zero indexed citations. The citing-works request was rate-limited, so its results could not be checked. The author’s Zenodo version contains the same question. The joint guarantee was absent from the works inspected in those searches. [Literature search in issue #32378](https://github.com/the-omega-institute/trureturing/issues/32378)
