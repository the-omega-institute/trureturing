---
slug: lin-wang-cai-2023-broom-spectral-ratio-conjecture-5-4
bibkey: linwangcai2023laplacianratio
doi: 10.48550/arXiv.2302.10491
url: https://arxiv.org/abs/2302.10491v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/SpectralGraph/LinWangCaiBroomSpectralRatio.result
---

# An order-19 counterexample to Conjecture 5.4

## Problem

Z. Lin, J. Wang and M. Cai, *The Laplacian spectral ratio of connected graphs*,
arXiv:2302.10491v1, Conjecture 5.4, page 16, state:

> Let T be a tree with n ≥ 8 vertices. Then R_L(K_{1,n−1}) ≤ R_L(T) ≤ R_L(B_n^{(n−3)/2}) if n is odd; R_L(B_n^{(n−4)/2}) if n is even. The left (right) equality holds if and only if T = K_{1,n−1} (T = B_n^{(n−3)/2} or T = B_n^{(n−4)/2}).

The [source note](../Library/GraphInvariants/linwangcai2023laplacianratio.md)
records the definitions and version; the preregistration is
[#19460](https://github.com/the-omega-institute/trureturing/issues/19460).
The upper inequality is false: $R_L(B_{19}^{8})<R_L(B_{19}^{7})$.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Laplacian $L=D-A$, eigenvalues in nonincreasing order | `lapEig` uses `SimpleGraph.lapMatrix` and `Matrix.IsHermitian.eigenvalues₀` | Index $i$ denotes $\mu_{i+1}$ |
| $R_L=\mu_1/\mu_{n-1}$ | `spectralRatio` uses indices $0$ and $n-2$ | Exact for $n\ge2$; the total extension below two is irrelevant |
| Figure 2 broom, center $v_0$, leaves $v_1,\ldots,v_t$, path $v_{t+1},\ldots,v_{n-1}$ | `broom` symmetrizes precisely those edges with `SimpleGraph.fromRel` | Literal labelled construction |
| Odd and even broom parameters | `conjParam` | Natural subtraction and division; at nineteen it is eight |
| Every tree with $n\ge8$ | `claim` quantifies over `n`, `hn`, `T` and adjacency decidability, then assumes `T.IsTree` | No additional mathematical hypothesis |
| Both bounds | First and second conjuncts of `claim` | Both retained |
| Both equality characterizations | Final two equivalences in `claim` | Graph equality means existence of an isomorphism |
| Refutation | `result` proves `Not claim` | The upper-bound conjunct fails at `broom 19 7` |

`Fin n` fixes vertex labels without restricting finite graph isomorphism types.
Adjacency decidability supplies finite matrix entries, rather than a spectral
hypothesis. No source clause is dropped or weakened.

## Motivation

The conjecture specifies one broom as a maximizer among all trees of a fixed
order. A comparison between two brooms therefore suffices to refute its upper
half. At order nineteen its parameter is eight, but seven gives a larger ratio.

## Gap

The literature screen in #19460 covers arXiv:2302.10491v1, the journal abstract,
and Ma–Tang–Wang–Zheng, arXiv:2604.17907v1. The latter proves the separate star
lower bound in Theorem 1.8 and does not settle this broom upper bound. The full
journal paper, Lin–Cai–Wang, *New bounds on the Laplacian spectral ratio of
connected graphs*, DOI 10.21136/CMJ.2024.0170-24, was not read. Related work on
normalized Laplacians and broom trees listed in #19460 was not read either.
No prior settlement was found within the stated screen. Completeness and the
journal version's retention of the conjecture are `ASSUMED-UNVERIFIED`.

## Route

All Lean names below belong to
`D5.S3.Combinatorics.SpectralGraph.LinWangCaiBroomSpectralRatio`.
The private `broom7_tree` and `broom8_tree` prove the required tree properties.
Rayleigh bounds from two explicit rational vectors give

$$0<\mu_{18}(B_{19}^{7})<35467/10^6,
\qquad 9018480/10^6<\mu_1(B_{19}^{7}).$$

Positive rational matrix factorizations give

$$39388/10^6<\mu_{18}(B_{19}^{8}),
\qquad \mu_1(B_{19}^{8})<10014270/10^6.$$

These are the statements of `lapEig_pos` specialized to the first tree,
`broom7_small_bound`, `broom7_large_bound`, `broom8_small_bound` and
`broom8_large_bound`. The integer comparison is

$$10014270\cdot35467=355176114090
<355219890240=9018480\cdot39388.$$

`ratios_separated` combines the bounds, `broom_ratio_strict` gives the strict
comparison, and `result` contradicts the upper-bound conjunct of `claim`.
The module imports pinned Mathlib directly and imports no D5 owner.
Its `admission_basis` is `open-problem-resolution (#19460; Refuted)`;
its consumed helpers and result are classified `bind-only`, with no asserted
escape witness. The certified instances serve the refutation.

## Falsifier

A mismatch between Figure 2 and `broom`, a different eigenvalue ordering,
failure of a strict rational certificate, or a dropped conjecture conjunct
would invalidate this settlement's correspondence. The literal definitions
and full conjunction are retained; the kernel checks the certificates and
the final contradiction. A different statement in the journal version is
outside the scope of this arXiv-v1 settlement.

## Evidence

The public theorem is `result : ¬ claim`. The Scribe displays the negation of
the complete claim and records one Refuted resolution on that declaration.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

### Experiment

[Published experiment](https://github.com/the-omega-institute/trureturing-experiments/tree/184f9f00be01656cdf4243725d35cf7ce7aea526/docs/reports/lin-wang-cai-2023-broom-spectral-ratio-conjecture-5-4).
From that repository's root, run
`uv run --with numpy --with scipy --with networkx python docs/reports/lin-wang-cai-2023-broom-spectral-ratio-conjecture-5-4/check.py`.
The rerun exited 0. The script SHA-256 is
`cdb9f67cbb5850e890c71aec81ff8ce9bf7e2ef64d9cf8c48b91f88d393ad3d4`.

The exact rational elimination and the independent reduced recurrence give
negative inertia counts $2,18,1,19$ at thresholds $35467/10^6$ and
$9018480/10^6$ for $B_{19}^{7}$, and $39388/10^6$ and $10014270/10^6$
for $B_{19}^{8}$, respectively. The integer comparison agrees with the one
above. These are computed cross-checks; the Lean proof uses Rayleigh and
positive-definiteness certificates rather than an inertia-counting theorem.

The floating-point broom scan covers every integer $8\le n\le400$ and
$1\le t\le n-2$. The proposed parameter maximizes the computed broom ratio
exactly at $n\in\{8,\ldots,18,20,22,24,26,28\}$, and loses at the other
$377$ tested orders, under the script's relative comparison tolerance
$10^{-12}$. Computed maximizing parameters include $7,8,26,178$ for
$n=19,21,60,400$. At $n=3200$ the restricted search
$\lfloor0.4n\rfloor\le t<\lfloor0.5n\rfloor$ gives $t=1432$;
it is not an exhaustive search over all broom parameters at that order.

The exhaustive enumeration covers all nonisomorphic trees at each order
$8\le n\le20$, with floating-point spectral evaluation. Among the $317955$
trees of order nineteen it returns maximum ratio $254.278886$ and a
maximizing representative isomorphic to $B_{19}^{7}$. The proposed broom's
ratio is approximately $254.2459$. At orders $8$ through $18$ and at $20$
the returned maximizing representative is the proposed broom. These
readings do not certify exact optimality, uniqueness, or least order.

The bounded scalar optimization of the continuum surrogate over
$0.3\le\alpha\le0.6$ computes fraction $0.447977$ and gain $1.018092$
relative to one half. This computation does not prove a
discrete asymptotic theorem.

## Triage

| Item | Status and evidence kind | Scope |
| --- | --- | --- |
| Refutation of the proposed upper broom parameter | Proved, kernel-checked: `result`, using `broom_ratio_strict` | $n=19$, arXiv-v1 claim |
| Source and unchanged conventions | Proved in prose by literal correspondence in the statement echo | arXiv:2302.10491v1, pages 2, 13 and 16 |
| Least counterexample order | Open as an exact classification | No certified least-order claim |
| Global maximizing tree at nineteen | Open as an exact theorem | No exact optimality or uniqueness claim |
| Asymptotic optimal broom parameter | Open | No discrete asymptotic theorem |
| Failure for infinitely many orders | Open | No uniform infinite-family claim |
| Separate star lower bound | Proved in cited literature, not newly proved here | Ma–Tang–Wang–Zheng, arXiv:2604.17907v1, Theorem 1.8 |
| Inertia implication in the preregistration | Proved in prose below | Exact count eighteen suffices; “at least eighteen” alone does not |
| Source results that depend on the conjecture | Open beyond the stated refutation | No other proved result is invalidated by this argument |
| Finite tree enumeration | Computed, experiment above | All nonisomorphic trees at $8\le n\le20$, floating-point spectra; returned representatives are the proposed brooms except at nineteen |
| Numerical maximum at nineteen | Computed, experiment above | All $317955$ nonisomorphic trees; value $254.278886$ and one representative $B_{19}^{7}$ |
| Finite broom failure set | Computed, experiment above | Full broom scan $8\le n\le400$; the $n=3200$ restricted search is separately scoped |
| Continuum surrogate optimum | Computed, experiment above | Fraction $0.447977$ and gain $1.018092$; no convergence conclusion |

### What the settlement shows

**Proved in this module:** The proposed extremizer fails already inside the
broom family. Reducing the star-leaf parameter from eight to seven at
nineteen increases the spectral ratio. The four strict spectral bounds
give a finite certificate of this failure. No least-order or global
optimality theorem is asserted.

**Explanation, with asymptotic validity open:** Increasing the number of
star leaves shortens the remaining path. The numerical picture balances
an approximate spectral radius $t+2$ against a path-like algebraic
connectivity $(\theta/m)^2$, where $m=n-t-1$ and
$\tan\theta=-(t/m)\theta$, $\pi/2<\theta<\pi$. The surrogate objective is
$t m^2/\theta^2$. The experiment optimizes this surrogate but does not
prove its approximation error, convergence, or a uniform discrete gain.

**Computed finite evidence:** The experiment supports attainment by some
broom for trees of orders eight through twenty. Exact attainment for all
orders remains open. The separate star lower bound survives this
counterexample and has the literature status stated in the table.

**Proved in prose, inertia correction:** Write the eigenvalues in
nonincreasing order. Exactly eighteen negative eigenvalues of $L-xI$,
with no zero eigenvalue, force eighteen eigenvalues of $L$ below $x$ and
one above it, hence $\mu_1>x$. If all nineteen eigenvalues of $L-xI$ are
negative, then $\mu_1<x$. Thus “at least eighteen” does not alone imply
$\mu_1>x$. The delivered Lean proof does not use that overly broad
implication.

## ASSUMED-UNVERIFIED

- Completeness of the literature screen and absence of an earlier published settlement.
- Whether the journal version retains the arXiv-v1 conjecture unchanged.
- Exact least counterexample order, global maximizing trees and uniqueness.
- A rigorous asymptotic broom parameter and infinitely many counterexamples.
- Any unexamined dependency of other source results on the conjecture.
