---
bibkey: zhang2026lonelyrunnerdeletion
authors: Yuhan Zhang
year: 2026
title: "Tight instances of the Lonely Runner Conjecture: complete classification of one-entry modifications, a new infinite family, and the growth bound"
doi: 10.48550/arXiv.2608.13599
url: https://arxiv.org/abs/2608.13599v2
claim: "Question 2.11 asks whether LR([n-1] minus {r}) is at least 1/(n-1) for every n and r, with equality only for r=n-1 (apart from the n=3 symmetry)."
strata_touched:
  - D5/S1/Phase/LonelyRunnerDeletion
license: citation-only
triage: anchor
---

# Zhang's one-deletion Lonely Runner question

Yuhan Zhang's paper *Tight instances of the Lonely Runner Conjecture* leaves
Question 2.11 open.  Writing (N=n-1), the speed set is

\[
  [N]\setminus\{r\}=\{1,\ldots,N\}\setminus\{r\},\qquad 1\le r\le N,
\]

and the question asks whether its Lonely Runner value is at least (1/N),
with equality only at the deleted endpoint (r=N).  The case (N=2) has the
obvious additional equality for (r=1), which is included explicitly in the
formal statement.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2608.13599
- URL: https://arxiv.org/abs/2608.13599v2
- Locator: arXiv:2608.13599v2, Question 2.11; Remark 2.8 and Proposition 2.10 give the surrounding one-entry cases.

## Formal resolution

The theorem `D5/S1/Phase/LonelyRunnerDeletion/OneDeletion.result` proves the
full quantified statement.  For (r>N/2), time (1/r) gives a strict
surplus over (1/N) after the deleted speed is removed.  For
(2r\le N), a denominator (q) with (N+r<q<2N) and an inverse of (r)
modulo (q) gives a residue at least two away from either endpoint for every
remaining speed.  The endpoint (r=N) and the exceptional (N=2) cases are
sharp by the nearest-integer bound.

The formal definition uses a supremum over all real times and the distance
`|v*t - round (v*t)|`; the proof supplies explicit rational witnesses and a
uniform upper bound, so it does not replace the source's Lonely Runner value
by a finite numerical search.

## Scope and priority boundary

The bounded repository search found only the unrelated finite certificate
`D5/S1/Phase/LonelyRunnerFourteenOfTwenty`; no other module or PR addressed
arXiv:2608.13599v2 Question 2.11.  This is a bounded search statement, not a
worldwide priority claim.  The result settles the exact one-deletion family
and does not claim the unrestricted Lonely Runner Conjecture.
