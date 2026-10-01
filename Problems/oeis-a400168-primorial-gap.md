---
slug: oeis-a400168-primorial-gap
bibkey: karttunen2026a400168
doi: null
url: https://oeis.org/A400168
triage: theorem
motivation_gids:
  - D5/S0/Certificates/BradshawConjectureTwentyRefutation.result
---

# A400168 has a term greater than one

## Problem

Antti Karttunen, OEIS A400168, revision 8, September 23, 2026:

> Question: Are there terms greater than 1?

The NAME is `a(n) = A235224(A003415(n)) - A400164(n)`, with offset one.
Let $P_k$ be the product of the first $k$ primes and $P_0=1$.
Set $L(0)=0$ and, for $m>0$, let $L(m)$ be the largest $k\ge1$ with
$P_{k-1}\le m$, equivalently the least $k\ge0$ with $m<P_k$.
Set $D(0)=D(1)=0$ and
$D(n)=\sum_{p\mid n}v_p(n)(n/p)$. Let $M(1)=0$ and, for $n\ge2$,
$M(n)=\max_{p^e\mid n,\ p\text{ prime},\ e\ge1} L(n/p^e)$.
One is not a prime power. The question is exactly whether
$\exists n\ge1,\ L(D(n))>M(n)+1$.

The closed `claim` is the universal negative answer
$\forall n\ge1,\ L(D(n))\le M(n)+1$.
Karttunen asked the existence question; he did not assert this bound.
`result : Not claim` answers the original question positively.

## Motivation

The frozen Bradshaw arithmetic-derivative refutation constructs the same
factorization sum locally and relates it to the defining product rule.
The present question concerns its primorial length and an independent
maximum over all prime-power divisors, rather than a Collatz commutation.

## Gap

The exact original question was preregistered in
[issue 11883](https://github.com/the-omega-institute/trureturing/issues/11883)
before any mathematical or numerical probe (createdAt `2026-10-01T16:07:23Z`).
Its exact settlement criterion was:

> A negative settlement requires the universal inequality L(D(n))<=M(n)+1 for every n>=1; a positive settlement requires one exact certified witness.

The registration specified the
full domain and all zero/one conventions, Tier 1 classification, a positive
settlement by one exact input or a negative settlement by the all-index
inequality, and a bounded initial structural probe. Input snapshots were
repository `e58fc8a59139625024fa174daea612c90c9762fc` and Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`.

The live entry checked October 1, 2026 still asked the question. Bounded
screens of linked OEIS entries, arXiv, Crossref, author/citation surfaces,
and exact-ID/numeric GitHub queries found no matching resolution. The
successful exact arXiv and Crossref searches returned zero hits. General
web searches were ineffective because of redirect/challenge pages or
irrelevant results. This is bounded literature evidence, not exhaustive
priority certification. A400171 concerns a different additive primorial
logarithm and derivative divisibility and does not settle this question.

## Route

Use the exact input $n=2^{49}$. Its factorization is supported only at two,
so $D(n)=49\cdot2^{48}=13792273858822144$.
The prime-power divisor theorem represents every relevant divisor as
$2^e$, $1\le e\le49$. Consequently $n/2^e\le2^{48}$, with equality
at $e=1$. The first-threshold definition of $L$ is monotone by minimality.
The exact indexed thresholds are

$P_{12}=7420738134810\le2^{48}=281474976710656<P_{13}=304250263527210$

and

$P_{14}=13082761331670030\le D(n)<P_{15}=614889782588491410$.

They yield $M(n)=13$ and $L(D(n))=15$. Thus $a(n)=2>1$.
The calculation uses small-prime thresholds and the full prime-power
divisor API, without executing a divisor search up to $2^{49}$.

## Falsifier

A mismatch in indexed primorials, the zero length convention, positive
exponents in the divisor filter, or the factorization formula would break
source fidelity. A prior resolution of this exact question would invalidate
open-problem-resolution eligibility without changing the arithmetic.

## Evidence

The formal source is `D5/S3/Arith/OeisA400168PrimorialGap.lean`.
Its necessary definitions are `P`, `L`, `D`, `M`, and the closed `claim`;
its only public theorem is the closed `result : Not claim`.
All arithmetic and length facts are local to that proof.
The compiled claim and result have only the standard axiom closure
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorry` or additional
axiom. The scoped inspector confirms the closed `Not claim` typing.
The indexed threshold definition is unbounded, and the maximum retains
all prime-power divisors. The Reg mirror reconstructs the complete
negated universal claim and audits its derivative-length readout over
all natural inputs. Source locators and complete equivalence are in
`Library/Arith/karttunen2026a400168.md` and the six Describe nodes.

## Triage

Tier 1 recent externally posed sequence question, preregistered before the
probe in issue 11883. The result has `admission_basis: open-problem-resolution`,
`proof_shape: bind-only`, and `escape_witness: null`. Its computational
utility is `certified-instance` with `basis=refutes`, exact local
`claim` and `result` GIDs, and the typed negation of the universal negative
answer. The original existence question is answered yes.

The exact term two is certified by the local arithmetic in the result.
The mechanism is that the factor 49 moves the arithmetic derivative past
$P_{14}$, while all divisor quotients remain below $P_{13}$.
The factorization and maximum definitions cover every positive index;
no least-input, infinite-family, or all-index upper-bound result follows.
Those stronger questions remain unproved. No dependent claim in the source
is asserted to follow from a negative answer; the question is an isolated
existence question.

## ASSUMED-UNVERIFIED

Complete source equivalence is a semantic review obligation in addition
to kernel verification. Literature completeness and exclusive priority
are unverified: the specified bounded searches do not cover all sources.
The dossier concerns exactly the A400168 existence question and the
logically equivalent universal negative answer; it makes no claim about
A400171 or least indices. Canonical report assessment, final resolution
binding, freezing, emission and independent delivery review belong to the
publication boundary and are not supplied by source compilation alone.
