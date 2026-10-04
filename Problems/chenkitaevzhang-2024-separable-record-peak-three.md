---
slug: chenkitaevzhang-2024-separable-record-peak-three
bibkey: chenkitaevzhang2024separable
doi: 10.1016/j.dam.2024.05.004
url: https://arxiv.org/abs/2404.18517v1
triage: theorem
motivation_gids:
  - D5/S1/Words/Patterns/Separable/RecordPeak.actual_record_rising
---

# CKZ Conjecture 2: the four actual record distributions

## Problem

Chen, Kitaev and Zhang, *Distributions of statistics on separable
permutations*, arXiv:2404.18517v1, Section 3, Conjecture 2, page 17, asks:

> The distribution of rmax or lmin (resp., lmax or rmin) on irreducible
> (resp., reducible) separable permutations is unimodal with the peak
> being at k=3 for n>=5 (see Table 4).

The journal reference is *Discrete Applied Mathematics* 355 (2024),
169–179. The carrier is the actual classical $2413/3142$-avoiding
permutations, rather than a recursive replacement class. A proper direct
cut separates a nonempty prefix whose values are all below those of the
nonempty suffix. Irreducibility means positive length and no proper direct
cut; reducibility means a proper direct cut. The empty permutation belongs
to neither positive class. The singleton is irreducible and has one record
of each type; the reducible singleton class is empty.

The four strict record statistics are right maxima, left minima, left
maxima and right minima. A maximum exceeds every value on its indicated
side, and a minimum is below every value on its indicated side. These
counts are unshifted. For any of the pairs
$(\mathrm{irreducible},\mathrm{rmax})$,
$(\mathrm{irreducible},\mathrm{lmin})$,
$(\mathrm{reducible},\mathrm{lmax})$ and
$(\mathrm{reducible},\mathrm{rmin})$, let $a(n,k)$ be the corresponding
actual record-fiber cardinality. The complete target is, for every
$n\ge5$ and every natural $k$,

$$
\begin{aligned}
k<3&\implies a(n,k)\le a(n,k+1),\\
k\ge3&\implies a(n,k+1)\le a(n,k),\\
a(n,k)&\le a(n,3).
\end{aligned}
$$

A maximum at three is interpreted weakly. Strict inequalities on zero
tails and uniqueness are not required. [Issue 12664](https://github.com/the-omega-institute/trureturing/issues/12664)
registers this full target. A partial rising or transport result does not
settle the conjecture.

## Motivation

The actual rising side holds for every $n\ge4$ and every $k<3$ in all
four distributions. `RecordPeak.actual_record_rising` supplies the actual
right-maximum comparison from two to three. The
`RecordTransport.actual_four_record_transports_and_rising` theorem proves
the all-length exact actual record transports, their singleton corrections,
the low-record zero fibers and the complete four-distribution rising side.
Writing $i_t,d_t$ for the positive irreducible and reducible record counts,
these exact transports are

$$
\begin{aligned}
i_{\mathrm{lmin}}(n,k)&=i_{\mathrm{rmax}}(n,k),\\
d_{\mathrm{lmax}}(n,k)+\delta(n,k)&=i_{\mathrm{rmax}}(n,k),\\
d_{\mathrm{rmin}}(n,k)+\delta(n,k)&=i_{\mathrm{rmax}}(n,k),
\end{aligned}
$$

where $\delta(n,k)=1$ exactly when $n=k=1$. They reduce the remaining
four declining laws at $n\ge5$ to the actual irreducible right-maximum
law. `RecordFirstDecline.actual_four_record_first_decline` proves the
first declining comparison $a(n,4)\le a(n,3)$ at every natural length,
and its strict form for every $n\ge3$, on all four actual class/statistic
pairs. The proof establishes its exact positive quotient and infinite tail
inside the actual weighted inference.

## Gap

The actual irreducible right-maximum declining comparisons for arbitrary
$k\ge4$ and the global maximum remain open.
`RecordNewtonPositivity.actual_q_record_newton_nonnegative` proves the
unbounded coefficient sign law $[t^n]G_r(q(t))\ge0$ for every natural $r,n$.
Its proof constructs the Motzkin series from Mathlib's Catalan supplier,
derives its differential recurrence at every index, and propagates two
pairs of consecutive positive-composition certificates to the universal
tail. This removes the universal kernel-sign obligation.

The exact remaining bridge is the normalized actual $J_k$ coefficient
formula and its Newton transform. They must identify each actual decline
with a nonnegative combination of the defined kernels; the sign theorem
has no actual-record-fiber correspondence in its conclusion. No new
actual declining range, full open-problem resolution or KPI increment is
attributed to this partial unit.

## Route

Use the actual record quadratic and scalar series from the right-maximum
proof to derive the normalized Motzkin formula and Newton transform inside
the full declining proof. Apply the proved all-index kernel sign law and
extract the actual record coefficients. The exact transports
give the remaining three declining laws at $n\ge5$. Combine rising and
declining inequalities to obtain the global maximum. A conditional
generating-function theorem or finite row computation does not discharge
this route.

## Falsifier

An actual source-class permutation count at some $n\ge5$ and natural $k$
violating a required adjacent inequality, or exceeding the count at three,
refutes the corresponding conjectured law. A counterexample to an auxiliary
coefficient estimate refutes that estimate; it does not automatically refute
the actual permutation conjecture.

## Evidence

The source v1 and the author and institutional manuscript bodies retain
Conjecture 2. The bounded literature screen, detailed in the
[Library entry](../Library/Words/chenkitaevzhang2024separable.md), reports
no equivalent proof or refutation in the source manuscripts, five known
citing bodies and the related papers inspected. The journal version of
record body remains unverified. This is a non-discovery in the searched
scope, not exhaustive global novelty, priority or exclusive ownership.
Fu–Lin–Zeng's descent real-rootedness problem and arXiv:2608.27583v1
Conjecture 15 are separate open problems.

## Triage

Theorem: a Tier 2 published universal mathematical conjecture with exact
source classes and record definitions. The partial actual-carrier
theorems leave the complete conjecture open. None is a full external
settlement or carries an `OpenProblemResolutionClaim`.

## ASSUMED-UNVERIFIED

The journal version of record body, exhaustive citation coverage and global
novelty are unverified. Uncompiled algebraic research does not establish
the missing normalized actual coefficient formula or Newton transform. Reg enrollment
is user-paused; no completed registration audit is claimed.
