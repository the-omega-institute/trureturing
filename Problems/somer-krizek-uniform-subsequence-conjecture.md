---
slug: somer-krizek-uniform-subsequence-conjecture
bibkey: somerkrizek2025uniformsubsequence
doi: 10.5281/zenodo.14679256
url: https://math.colgate.edu/~integers/z1/z1.pdf
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Periodic/SecantNumberPurePeriodRefutation
---

# Somer-Krizek uniform-subsequence conjecture

## Problem

Somer and Krizek, Conjecture 4.2, printed page 8, proposes the following.
For every `k >= 2`, let an integer sequence satisfy

`w(n+k) = a1*w(n+k-1) + ... + ak*w(n)`

for every `n >= 0`. Let `p` be prime, `e >= 1`, and `E > 0`. Assume that
`gcd(ak,p)=1`, that the least positive period modulo `p^e` is exactly
`p^e E`, and that every residue modulo `p^e` occurs exactly `E` times in
that least period. For every positive `g` coprime to `p` and every
nonnegative `s`, put `r=E/gcd(g,E)`. The conjecture asserts that every
residue occurs exactly `r` times among `w(s+ng)` for `0 <= n < p^e r`.

## Motivation

The paper proves the corresponding statement for second-order recurrences
and asks whether it extends to all higher orders. Example 4.3 gives a
supporting third-order instance. The conjecture is therefore a precise
test of whether the second-order mechanism survives at the first new order.

## Gap

The official journal PDF and DOI record identify the paper as INTEGERS 25
(2025), A1, version 1. The bounded public-source review recorded in issue
8695 checked the official 2025 and 2026 journal listings, the authors'
available later work, and exact title, DOI, author, conjecture-number, and
topic searches. It found no correction, proof, or refutation of the exact
claim in that scope. This is not an exhaustive literature or priority claim.

## Route

Take `k=3`, coefficients `(0,0,-1)`, and initial values `(0,1,2)`, so
`w(n+3)=-w(n)` for every `n`. The integer period is
`(0,1,2,0,-1,-2)`. Modulo three it becomes `(0,1,2,0,2,1)`, has genuine
least period six, and contains every residue exactly twice. Thus
`p=3`, `e=1`, and `E=2` satisfy the full hypotheses.

For `g=2` and `s=0`, one has `r=2/gcd(2,2)=1`. The first three sampled
residues are `(0,2,2)`, so residue one occurs zero times rather than once.
The candidate was released in the public handoff at issue 7333, comment
5733245266; this dossier credits that handoff and makes no first-discovery
claim.

## Falsifier

A proof that the displayed third-order sequence fails the recurrence, lacks
least modular period six, lacks two copies of each residue in its full orbit,
or has one copy of every residue in its first three step-two samples would
falsify this route. The explicit six-term word makes each condition finite
except the all-index recurrence, which follows from six-periodicity together
with `w(n+3)=-w(n)` at every residue class modulo six.

## Evidence

- Primary source: DOI `10.5281/zenodo.14679256`, printed page 8,
  Conjecture 4.2.
- Source module:
  `D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.lean`.
- The formal claim retains every quantified source parameter and hypothesis.
- The public result negates that complete claim and retains the actual
  six-code word in its raw type.
- The certificate proves the all-index recurrence, exact least period,
  full-orbit counts, and the failed sampled count.

## Triage

`theorem`. The explicit third-order recurrence refutes the universal
higher-order conjecture. It does not challenge the paper's proved
second-order theorem and asserts no corrected higher-order criterion.

## ASSUMED-UNVERIFIED

The literature review is bounded and does not establish exhaustive absence
of corrections, unpublished work, paywalled citing papers, or unindexed
resolutions. The released public handoff is credited for the candidate; no
claim of independent first discovery or worldwide publication priority is
made.
