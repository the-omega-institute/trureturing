---
slug: arxiv-2510-07530-gallardo-rahavandrainy-collatz-length-bound
bibkey: gallardo2025collatzlength
doi: 10.48550/arXiv.2510.07530
url: https://arxiv.org/abs/2510.07530v1
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/GallardoRahavandrainyCollatzLengthBound.result
---

# A polynomial bound for binary-polynomial Collatz length

## Problem

Gallardo and Rahavandrainy, *A variant of Collatz's Conjecture over Binary
Polynomials*, arXiv:2510.07530v1, §1, state: “However, several computations
suggest that here also r_A is bounded by a polynomial in deg(A) (see Section 3).”
The question is preregistered in [#20129](https://github.com/the-omega-institute/trureturing/issues/20129).
For every nonzero $A\in\mathbb F_2[x]$, the theorem `rA_quadratic` proves
$r_A\le 2+\lfloor\deg(A)^2/4\rfloor$. The theorem `result` proves the
literal polynomial-bound prediction, using $p(X)=X^2+2\in\mathbb N[X]$.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Nonzero binary polynomial $A$ | `A : Polynomial (ZMod 2)`, `hA : A ≠ 0` | Same coefficient ring and domain. |
| $M_1=x^2+x+1$; removal of all linear factors | Existing `M`, `oddPart` | Reused at GallardoRahavandrainyBinaryCollatz. |
| $A_0=A$, $A_{2k}=1+M_1A_{2k-1}$ for $k>0$ | `evenTerm A k` | Literal conditional expression. |
| $A_{2k+1}$ | Existing `oddSeq A k` | The natural index is half the source's odd index, rounded down. |
| Least positive $m$ with terminal pair $(x(x+1),1)$ for all $k\ge m$ | `rA A` | Natural infimum of precisely that set, plus one; the proof constructs a member. |
| Bound by a polynomial in degree | `claim`, `result` | Existential natural-coefficient polynomial; no extra hypothesis. |
| Explicit stronger estimate | `rA_quadratic` | $r_A\le2+\lfloor\deg(A)^2/4\rfloor$. |

The natural degree agrees with polynomial degree on the nonzero domain.
Definitions are total at zero; the theorem excludes zero. The existential
polynomial witness is an upper envelope of the sharper floor estimate.

## Motivation

The source's Theorem 1.2 proves termination with an exponential bound.
The settling GID is `D5/S1/Recurrence/GallardoRahavandrainyCollatzLengthBound.result`.
The imported owner also settles the distinct Conjecture 3.11 of
arXiv:2308.01181v2 under [#19299](https://github.com/the-omega-institute/trureturing/issues/19299);
its dossier and resolution claim remain attached to that owner's `result`.

## Gap

The polynomial-bound prediction is proved. The Lean proof gives a bound on
plateau duration and the quadratic length estimate. Exact plateau duration
and sharpness examples below are proved in prose, rather than asserted as
additional kernel-checked theorems. A linear uniform bound remains open.
Literature completeness is `ASSUMED-UNVERIFIED`.

## Route

Let $P=x(x+1)$ and $T(F)=\operatorname{oddPart}(1+M_1F)$. For odd $F\ne1$,
put $k=\min(v_x(F+1),v_{x+1}(F+1))$. Both multiplicities are positive and
$k\le\lfloor\deg(F)/2\rfloor$. A degree-preserving step removes one factor
of each linear polynomial, and decreases this minimum by one. Strong
induction on $k$ gives a strict degree decrease within $k$ steps
(`plateau_escape`). Strong induction on degree, using the consumed
`square_budget_step`, bounds the first odd hitting index by
$\lfloor\deg(A)^2/4\rfloor$ (`oddSeq_hit`). The terminal pair holds from the
next index onward (`rA_le_hit`), giving the extra two in `rA_quadratic`.
The public settling `result` chooses $X^2+2$ and applies that estimate.

## Falsifier

A nonzero binary polynomial whose length exceeds the stated estimate would
contradict `rA_quadratic`. A mismatch between the source's terminal-pair
count and `rA` would invalidate fidelity; the statement echo and the source
examples use that exact count.

## Evidence

The Lean modules are
`D5/S1/Recurrence/GallardoRahavandrainyBinaryCollatz.lean` and
`D5/S1/Recurrence/GallardoRahavandrainyCollatzLengthBound.lean`, with their
corresponding Blueprint Scribes. The axiom closure of every public declaration
is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The experiment is the [pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/8db3cff2b9136b3086be66583c454f3ca93fb369/docs/reports/gallardo-rahavandrainy-2025-binary-collatz-length-bound).
Command: `python3 docs/reports/gallardo-rahavandrainy-2025-binary-collatz-length-bound/check.py`
in that experiments checkout; exit 0.
Script SHA-256: `4f0db8a8d3cf2081c030bc3b8df0bb194c991b58c8831c2ef48f015531422238`.
It reproduces the source's degree sequences for $M_1^n+1$, $9\le n\le16$;
$x^n+x+1$, $31\le n\le34$; and its three polynomials $P_1,P_2,P_3$.
It enumerates every nonzero binary polynomial of degree at most 14.
The longest degree-$n$ plateau is $\lfloor n/2\rfloor$ for $2\le n\le14$;
at degree 14 the maximum length is 16 and the quadratic bound is 51.
These exact finite readings corroborate the conventions and do not prove
an unbounded claim.

The four-slot escape audit is unfinished under
[#20796](https://github.com/the-omega-institute/trureturing/issues/20796)
for `rA_quadratic`, `result`, and the six published owner prerequisites.
The existing owner's `result` is also included in #20796, with its exact-domain
registration boundary detailed in
[#19534](https://github.com/the-omega-institute/trureturing/issues/19534).
No `declared_validated` registration is asserted.

### Declaration roles and source consumers

The table is extracted from the elaborated declaration dependency graph;
consumer names refer to source declarations. Bind-only entries organize the
proof. The admission basis is `open-problem-resolution (#20129; Proved)`.

| Declaration | `proof_shape` | Escape witness | A direct source consumer |
| --- | --- | --- | --- |
| `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.evenTerm` | bind-only | `none` | `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.rA` |
| `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.rA` | bind-only | `none` | `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.claim` |
| `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.claim` | bind-only | `none` | `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.result` |
| `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.oddPart_data` | bind-only | `none` | `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.oddPart_degree` |
| `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.oddPart_odd` | bind-only | `none` | `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.oddSeq_hit` |
| `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.oddPart_degree` | bind-only | `none` | `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.oddSeq_hit` |
| `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.numerator_degree` | bind-only | `none` | `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.numerator_nonzero` |
| `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.numerator_nonzero` | bind-only | `none` | `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.step_data` |
| `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.step_odd` | bind-only | `none` | `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.iterate_odd` |
| `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.step_data` | bind-only | `none` | `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.step_degree` |
| `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.step_degree` | bind-only | `none` | `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.plateau_escape` |
| `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.step_same_factor` | bind-only | `none` | `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.step_same_plateau` |
| `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.plateau` | bind-only | `none` | `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.plateau_bound` |
| `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.plus_one_ne_zero` | bind-only | `none` | `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.plateau_bound` |
| `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.positive_degree` | bind-only | `none` | `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.plateau_bound` |
| `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.plateau_positive` | bind-only | `none` | `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.plateau_escape` |
| `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.plateau_bound` | bind-only | `none` | `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.reaches_one` |
| `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.step_same_plateau` | bind-only | `none` | `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.plateau_escape` |
| `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.step` | bind-only | `none` | `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.iterate_odd` |
| `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.iterate_odd` | bind-only | `none` | `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.reaches_one` |
| `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.plateau_escape` | content | `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.plateau_escape` | `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.reaches_one` |
| `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.square_budget_step` | bind-only | `none` | `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.reaches_one` |
| `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.reaches_one` | content | `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.reaches_one` | `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.oddSeq_hit` |
| `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.step_one` | bind-only | `none` | `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.oddSeq_tail` |
| `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.oddSeq_eq_iterate` | bind-only | `none` | `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.oddSeq_hit` |
| `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.oddSeq_hit` | content | `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.plateau_escape` | `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.rA_quadratic` |
| `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.oddSeq_tail` | bind-only | `none` | `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.rA_le_hit` |
| `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.rA_le_hit` | bind-only | `none` | `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.rA_quadratic` |
| `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.rA_quadratic` | content | `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.plateau_escape` | `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.result` |
| `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.result` | content | `D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.plateau_escape` | `settlement` |

## Triage

### What the settlement shows

| Item | Status and evidence kind | Evidence and scope |
| --- | --- | --- |
| Polynomial-bound prediction | Proved; kernel-checked | Public `result` proves `claim` for all nonzero binary polynomials. |
| Explicit quadratic estimate | Proved; kernel-checked | Public `rA_quadratic`. |
| Odd sequence reaches one within $1+\lfloor n^2/4\rfloor$ terms | Proved; kernel-checked | Consumed private `oddSeq_hit` bounds its first hitting index by $\lfloor n^2/4\rfloor$. |
| Degree does not increase under $T$ | Proved; kernel-checked | Consumed private `step_degree`, with both oddness hypotheses. |
| A degree plateau ends within its smaller root multiplicity | Proved; kernel-checked | Consumed private `plateau_escape` and `plateau_bound`. |
| Exact plateau mechanism | Proved in prose | Derivation below preserves both root valuations and identifies the first strict drop. |
| $g(n)=\lfloor n/2\rfloor$ for $n\ge2$ | Proved in prose | Exact plateau derivation and the explicit attaining families below. |
| Source estimate (4) for $n\ge2$ | Proved in prose | $2+\lfloor n^2/4\rfloor\le n(n+1)/2$; use `rA_quadratic`. |
| Source tables and finite maxima | Computed | The pinned experiment above, on precisely the listed examples and degrees at most 14. |
| Source table at degree 21 | Literature reading | The source’s §3 table gives $f(21)=46$; this is a paper-reported value beyond the experiment’s exhaustive degree-14 range. |
| A uniform $O(n)$ bound | Open | Neither the quadratic theorem nor the finite enumeration establishes it. |
| Other source consequences | Open; literature reading | The polynomial prediction and the conditional bound above are resolved; no exhaustive dependency classification of other source results is asserted. |
| Literature completeness | Open; literature reading | The screen in #20129 is partial. |
| Escape registrations | Open | #20796 and #19534 identify the missing evidence. |

### Exact plateaus and attaining examples

This paragraph is a proof in prose. Fix an odd $F\ne1$ of degree $d$.
Write $F+1=P^kC$ with
$k=\min(v_x(F+1),v_{x+1}(F+1))\ge1$.
At least one of $C(0),C(1)$ is 1: otherwise both root multiplicities exceed $k$.
For $0\le j\le k$ define $B_j=1+M_1^jP^{k-j}C$.
For $j<k$, both evaluations of $B_j$ are 1 and its degree is $d$,
since $\deg M_1=\deg P=2$ and $d>0$.
The identity $1+M_1=P$ gives $1+M_1B_j=PB_{j+1}$.
For $j<k-1$, $B_{j+1}$ is odd, so $T(B_j)=B_{j+1}$.
At a root $\alpha\in\{0,1\}$ where $C(\alpha)=1$, one has
$B_k(\alpha)=0$ since $M_1(\alpha)=1$.
Also $B_k\ne0$, because $M_1^kC=1$ is impossible for $k\ge1$.
Thus removing the linear factors from $B_k$ strictly decreases degree.
The plateau consists of exactly $B_0,\ldots,B_{k-1}$.
Since $2k\le d$, its length is at most $\lfloor d/2\rfloor$.
For degree $2k$, the odd polynomial $1+P^k$ has minimum multiplicity $k$;
for degree $2k+1$, use $1+xP^k$, whose multiplicities are $k+1$ and $k$.
They attain the bound. This proves $g(d)=\lfloor d/2\rfloor$ for every $d\ge2$.
These are consequences of the displayed polynomial identities; they are not
additional Lean declarations in this delivery.

For the source's conditional estimate (4), write $n=2q$ or $n=2q+1$.
For even $n\ge2$, the difference
$n(n+1)/2-(2+\lfloor n^2/4\rfloor)=q^2+q-2$ is nonnegative for $q\ge1$.
For odd $n\ge3$, it is $q^2+2q-1$, also nonnegative for $q\ge1$.
Hence that estimate is unconditional on this range.

### Literature scope

The preregistration records searches by title, identifier, authors and
polynomial Collatz terminology. It reports that the journal version
Revista de la Unión Matemática Argentina 69(1), 295–302,
DOI 10.33044/revuma.5555, retains the prediction.
Alon–Behajaina–Paran (arXiv:2401.03210) and Behajaina–Paran
(arXiv:2312.00390) use multiplier $x+1$ and remove only powers of $x$;
those statements do not settle the present two-root process.
The distinct Conjecture 3.11 is settled by the imported owner.
These are preregistration-reported literature readings.

## ASSUMED-UNVERIFIED

Prior-art completeness, including full-text and citation-index coverage, is
`ASSUMED-UNVERIFIED`. The journal-version reading is preregistration-reported.
The four-slot escape audit remains unfinished under #20796 and #19534.
