---
slug: zhang-2026-lonely-runner-one-deletion
bibkey: zhang2026lonelyrunnerdeletion
doi: 10.48550/arXiv.2608.13599
url: https://arxiv.org/abs/2608.13599v2
triage: theorem
motivation_gids:
  - D5/S1/Phase/LonelyRunnerDeletion/OneDeletion
---

# Zhang Question 2.11: one-deletion Lonely Runner values

## Problem

Yuhan Zhang, *Tight instances of the Lonely Runner Conjecture: complete
classification of one-entry modifications, a new infinite family, and the
growth bound*, arXiv:2608.13599v2, Question 2.11, asks whether

\[
  \operatorname{LR}([n-1]\setminus\{r\})\ge {1\over n-1}
\]

for every (n) and (r\in[n-1]), and whether equality can occur only when
(r=n-1).  For (n=3), deleting either speed leaves a singleton and both
choices attain equality; the formal statement records that boundary case.

## Gap

The paper proves selected deletion values but leaves the all-(n,r) family as
Question 2.11.  The formal proof writes (N=n-1), defines the Lonely Runner
value as the supremum over real times of the nearest-integer distance, and
uses explicit rational times.  The endpoint (r=N) is sharp at time (1/N).

## Route

For (r>N/2), time (1/r) gives a strict lower bound.  For (2r\le N),
an explicitly constructed (q) with (N+r<q<2N), together with an inverse
of (r\pmod q), forces every retained residue away from both endpoints.

## Resolution

`D5/S1/Phase/LonelyRunnerDeletion/OneDeletion.result` proves, for every
(2\le N), (1\le r\le N),

\[
{1\over N}\le \operatorname{LR}([N]\setminus\{r\}),
\qquad
\operatorname{LR}([N]\setminus\{r\})={1\over N}
\Longleftrightarrow r=N\ \lor\ N=2.
\]

This settles the source question and its (n=3) equality symmetry.  It does
not assert the unrestricted Lonely Runner Conjecture.

## Evidence

- Lean: `D5/S1/Phase/LonelyRunnerDeletion/OneDeletion.lean`.
- Main theorem: `D5.S1.Phase.LonelyRunnerDeletion.OneDeletion.result`.
- Source locator: arXiv:2608.13599v2, Question 2.11.
- The bounded exact-name/identifier repository search found no competing
  implementation; the unrelated finite certificate is retained separately.

## Triage

`theorem`.  The result is a kernel-checked resolution of the registered
one-deletion family.  No priority claim is made beyond the bounded search
recorded above.
