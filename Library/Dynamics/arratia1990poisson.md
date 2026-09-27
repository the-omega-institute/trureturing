---
bibkey: "arratia1990poisson"
authors: "Richard Arratia; Larry Goldstein; Louis Gordon"
year: 1990
title: "Poisson Approximation and the Chen-Stein Method"
doi: "10.1214/ss/1177012015"
url: "https://doi.org/10.1214/ss/1177012015"
claim: "Local-dependence terms control Poisson approximation for a count of events, including an explicit bound on its zero-count probability."
strata_touched: []
license: "citation-only"
triage: "anchor"
---

# Poisson Approximation and the Chen-Stein Method

Statistical Science 5(4), 403–424 (1990). The dependence quantities are defined
in section 3; Theorem 1 on page 406 bounds the count distribution and its
zero-count probability. Theorem 2 on the same page gives a process version.
The exposition attributes the proofs to the authors' 1989 Annals of Probability
paper, *Two Moments Suffice for Poisson Approximations: The Chen-Stein Method*.

This is `literature-attested` background for locally dependent rare-event counts.
The parity-kernel proof supplies its own event probabilities, separation rule,
factorial-moment domination, and reduction from Bayes overlap to zero counts.
The Poisson count approximation is a standard ingredient; the specified
trajectory-testing curve and constrained entropy optimization are separate
deductions, not claims of a new general Poisson approximation theorem.

Author-hosted primary text:
<https://dornsife.usc.edu/larry-goldstein/wp-content/uploads/sites/221/2023/06/pacs-1.pdf>.

For a growing set of marked rows, the relevant input is the **process** statement
of Theorem 2 on printed page 406, with the neighborhoods and quantities in
(4)–(6) on page 405. Its bound is

```math
\|\mathcal L(X)-\mathcal L(Y)\|\le2(2b_1+2b_2+b_3).
```

The paper's total-variation norm is twice the supremum over events. Each coordinate
of the comparison process is an independent Poisson variable with the original
Bernoulli coordinate's mean. Aggregating coordinates preserves an upper bound
on total variation; this permits grouping time-and-type events into row counts.

In the compensated parity model, a marked set of size m has total one-edge
probability m/n. The exact two-step reset proves independence from the **joint**
outside-neighborhood information, giving b3 = 0; nearby marked departures supply
b1 + b2 = O(s m²/n²). The resulting growing-row comparison is useful for the q
true signal rows when lambda q²/n tends to zero. It does not approximate the whole
ambient collection of background rows. Total variation alone also does not
transfer expectations of dimension-dependent losses at the square-root-q scale;
that step needs the separately established one-row relative estimate.
