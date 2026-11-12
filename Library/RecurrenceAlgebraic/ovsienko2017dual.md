---
bibkey: ovsienko2017dual
authors: Valentin Ovsienko; Serge Tabachnikov
year: 2017
title: Dual numbers, weighted quivers, and extended Somos and Gale-Robinson sequences
doi: 10.1007/s10468-018-9779-3
url: https://arxiv.org/abs/1705.01623v1
claim: The first non-homogeneous dual Somos-4 sequence with positive exponents and arbitrary integer initial shadows is conjectured to have all shadows integral exactly when p equals one.
strata_touched:
  - D5/S1/Recurrence/Invariants/SomosFirstDualIntegrality
license: citation-only
triage: anchor
---

## Verified locator

The fixed preprint is https://arxiv.org/abs/1705.01623v1, source archive
https://arxiv.org/src/1705.01623v1. Its archive SHA-256 is
`4f3be9b79dddec394f469db802bf98b2a754788657717e49c8cccc4f66c2c7f3`.
The journal article is https://doi.org/10.1007/s10468-018-9779-3.
The relevant preprint locator is §5.4, printed pages 10–11,
Corollary 5.2(i) and the unnumbered conjecture immediately after its proof.

The section fixes positive integers p and q and real initial values
a0=a1=a2=a3=1. Corollary 5.2(i) establishes the p=1 sufficient direction
for arbitrary integer initial shadows. The following conjecture reads:

> Note that our results do not imply the converse statement.
> However, we conjecture that the sequence (b_n), defined by the recurrence
> A_(n+4) A_n = A_(n+3)^p A_(n+1)^p + A_(n+2)^q (1+epsilon),
> is integer if and only if p=1 (and similarly for the second case).

The arbitrary initial shadows are inherited from the preceding corollary.
That corollary labels them b1,…,b4, while the section's real initial values
and Example 5.3 use indices 0,…,3. The formal statement normalizes the four
leading slots to 0,…,3. The integer tuple is fixed separately for each iff;
it is not moved inside a universal-initial-data predicate.

## Scope and prior results

The p=1 sufficiency is published prior mathematics. The formal proof here
uses an elementary quotient-ring criterion, rather than assuming a Laurent
phenomenon supplier. The rational dual orbit embeds coefficientwise into
the real dual orbit, and this embedding preserves and reflects integral
shadows. All positive exponents and every integer initial tuple are retained.

The second deformation and independent positivity or growth conjectures
are outside the selected target. The source's inconsistent exponent in the
second deformation has no role in the first-family statement.

The preregistered scope and supplied bounded literature/supplier screen are
in https://github.com/the-omega-institute/trureturing/issues/29468.
No exhaustive literature-absence, global continued-openness, priority or
originality claim follows from that screen. No third-party Lean source is
copied. The cited paper supplies the problem and published sufficient
direction; citation does not supply a kernel proof.
