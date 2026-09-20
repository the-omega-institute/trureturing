---
bibkey: balister2018covering
authors: "Paul Balister; Béla Bollobás; Robert Morris; Julian Sahasrabudhe; Marius Tiba"
year: 2018
title: "On the Erdős Covering Problem: the density of the uncovered set"
doi: 10.48550/arXiv.1811.03547
url: https://arxiv.org/abs/1811.03547
claim: "The paper develops distortion estimates for uncovered density and proves Schinzel's conjecture that some pair of moduli in every covering system is related by divisibility."
strata_touched:
  - D5/S3/Arith/Congruence/TwoOddPrimeUncoveredDensity
license: citation-only
triage: anchor
---

# Distortion and uncovered density

Locator: https://doi.org/10.48550/arXiv.1811.03547;
https://arxiv.org/abs/1811.03547, submitted 8 November 2018; metadata and abstract
checked 16 September 2026. This is background for the distortion and
second-moment route, alongside [the squarefree paper](balister2019erdos.md).

An arbitrary-head application must uniformly extend each later prime-power
block before applying the cap. Conditioning on pure-prime survivors alone
does not remove old mixed classes; conditioning on all old survivors changes
normalized cylinder costs. This proposed extension is not a quoted theorem
of these papers and has no local Lean proof.

The primary v1 text was also read for the labelled-modulus application in
[report 348](../../docs/reports/erdos7-odd-covering/profile-notes/321-384/348-fresh-prime-root-transport-and-two-copy-reduction.md).
Lemma 3.6 (pages 11–12) bounds moments by sums over congruence tuples;
Lemma 3.7 bounds their divisor sums. Section 6 (pages 17–19) explicitly
indexes all primes and accepts any constant kappa satisfying its
second-moment hypothesis (20), then supplies the recurrence in Lemma 6.2
and the unrestricted continuation criterion in Theorem 6.1.

For at most two labels per numerical modulus, the tuple argument gains
a single factor 4 in the second moment. The report proves this extension
under the same distorted laws, and uses kappa=4 when the period is coprime
to 210. An exact rational continuation reaches Theorem 6.1 at prime 167,
proving noncoverage in that scope. This labelled extension is an ordinary
deduction, not a literal statement of the paper's distinct-modulus
Theorem 7.1. The rational program checks the finite endpoint; it does not
machine-verify the measure argument or replace the analytic tail proof.
