---
slug: bhanja-2025-restricted-sumset-question
bibkey: bhanja2025distinctterms
doi: null
triage: theorem
motivation_gids:
  - D5/S3/FiniteGroups/BhanjaRestrictedSumset/Result.result
url: https://arxiv.org/abs/2307.03977v2
---

# Unequal minima for sumsets with at most two distinct terms

## Problem

J. Bhanja, *Sumsets with a minimum number of distinct terms*, Integers 25
(2025), A12, arXiv:2307.03977v2, §4 “Further Remarks”, printed p. 11:

> Another sumset that may come immediately to the reader’s mind is the sumset
> h(≤r) A, which contains those elements of the group G that are the sum of h elements
> of A with at most r distinct elements. The sumset hA is a special case of h(≤r) A
> for r = h.

> Question 1. Is it always the case that the minimum size of both the sumsets hA
> and h(≤r) A are the same in any abelian group G, where the minimum runs over the
> subsets of G of size (say) k?

### Formal reading

Names have prefix `D5.S3.FiniteGroups.BhanjaRestrictedSumset.Result`.
`hSumset h A` is Mathlib's pointwise $h\mathbin{\bullet}A$, with exactly
$h$ summands. `restrictedSumset h r A` is the image of functions
$f:\operatorname{Fin}h\to G$ taking values in $A$ whose image has at most
$r$ elements, under $f\mapsto\sum_i f(i)$.
`minSize G k h` and `minRestrictedSize G k h r` are infima in the natural
numbers of the corresponding cardinalities over $k$-element finsets.
The claim requires a $k$-element subset to exist, so these infima are
actual minima. It quantifies over all abelian groups, $h\ge1$, $r\ge2$,
and all attainable cardinalities $k$. Allowing $k=0$ adds only a case in
which both sumsets are empty for $h\ge1$.

## Motivation

The settling declaration is `D5/S3/FiniteGroups/BhanjaRestrictedSumset/Result.result`.
The source note is `D5/L/FiniteGroups/bhanja2025distinctterms`.
Restricting the number of distinct summands can preserve the integer
minimum while changing minima in finite groups.

## Gap

For $m\ge2$, odd $h\ge3$ and $2^{m-1}<k<2^m$, every $k$-element subset
of $G=(\mathbb Z/2\mathbb Z)^m$ has
$h^{(\le2)}A=A$ and $hA=G$. Therefore
$\mu_{\le2}(G,k,h)=k<2^m=\mu(G,k,h)$.
The smallest example has $m=2$, $k=h=3$ and $r=2$.

## Route

Every element of $G$ has twice itself equal to zero. A sum with odd
length using at most two values is one of those values: exactly one
multiplicity is odd. Conversely, repeating any member an odd number of
times recovers it. This proves the restricted identity.

Since $2|A|>|G|$, the sets $A$ and $g-A$ intersect for each $g$ by the
finite-set pigeonhole principle, so $A+A=G$. For $h\ge2$, choose
$a_0\in A$, represent $g-(h-2)a_0$ as two members of $A$, and append
$h-2$ copies of $a_0$. Thus $hA=G$. The identities for every $k$-subset,
together with existence of such a subset, determine both minima.

## Falsifier

A mismatch between the image-cardinality restriction and “at most r
distinct elements”, or between the minima and optimization over all
$k$-element subsets, would invalidate the conclusion. A single convenient
subset alone would not establish the ordinary minimum.

## Evidence

**PROVED.** `elementary_two_group_gap` proves both sumset identities for
all $m\ge2$, odd $h\ge3$ and subsets with cardinality strictly between
$2^{m-1}$ and $2^m$. `elementary_two_group_minima` proves both exact
minima. `result` states exactly $\neg\mathrm{claim}$.

The immutable [experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/5175832e77ae14b93bc0075f43bd8126f57bddfc/experiments/bhanja-restricted-sumset-question)
contains `bhanja-q1.py`, SHA-256
`4c041a3988bd92a78819b081d13dfded6cdf3dda78b8988221311271e576220a`.
Command: `python3 bhanja-q1.py`; exit code 0. It tests every nonempty
proper-subset cardinality $1\le k<|G|$ for the groups in the following survey at $h=3$,
$r=2$, and checks the elementary 2-group identities for $m=2,3$,
$h=3,5$ in the strict half-to-full range.

The supplied literature search covers the current arXiv v2 and journal
version, title and identifier searches, and searches combining Bhanja
with Question 1, counterexample and at-most-distinct sumset terminology.
No settlement was found in that supplied scope. Goswami–Mistri,
arXiv:2603.04572, concerns all-distinct summands, a different restriction.

## Triage

### What the settlement shows

- **PROVED (Lean).** The entire elementary 2-group family and its exact
  minima are `elementary_two_group_gap` and `elementary_two_group_minima`.
  The universal equality is refuted by `result`.
- **PROVED (prose consequence).** At $h=3$ and $k=2^{m-1}+1$, the gap is
  $2^m-k=2^{m-1}-1$. For $m\ge2$ this cardinality lies in the strict
  range. Since powers of two are unbounded, so are the gaps.
- **COMPUTED.** At $h=3,r=2$ the minima differ in $(\mathbb Z/2)^2$,
  $(\mathbb Z/2)^3$, $\mathbb Z/2\times\mathbb Z/4$,
  $\mathbb Z/2\times\mathbb Z/6$, and the cyclic groups
  $\mathbb Z/7$ ($k=3$: $6$ versus $7$),
  $\mathbb Z/8$ ($k=5$: $7$ versus $8$),
  $\mathbb Z/9$ ($k=4$: $8$ versus $9$), and
  $\mathbb Z/12$ ($k=7$: $10$ versus $12$).
  The first number is the restricted minimum. Evidence is the exhaustive
  experiment above, with its pinned program, command, exit code and hash.
- **COMPUTED.** In the same survey the minima agree for every nonempty
  proper-subset cardinality $1\le k<|G|$ in $\mathbb Z/3$, $\mathbb Z/4$, $\mathbb Z/5$,
  $\mathbb Z/6$, $\mathbb Z/10$ and $\mathbb Z/3\times\mathbb Z/3$.
  This is finite computational evidence, with the same experiment entry.
- **PROVED (prose argument).** For the endpoint $k=|G|$ in a finite
  abelian group, the only subset is $A=G$. At $h=3,r=2$, every $g\in G$
  is $g+0+0$, using at most two distinct values from $A$. Thus both
  sumsets equal $G$, and both minima equal $|G|$. This endpoint is a
  prose argument, separate from the computed survey.
- **PROVED (mechanism).** Parity cancellation in exponent two is the
  mechanism of `elementary_two_group_gap`. The cyclic survey shows that
  failure is not confined to exponent two. For $\mathbb Z/7$,
  Cauchy–Davenport gives $|2A|\ge5$ and $|3A|\ge7$ for $|A|=3$;
  the computed restricted minimum is $6$. Thus cyclic wrap-around can
  separate the restricted minimum from the ordinary bound. The
  Cauchy–Davenport explanation is a prose application, not a Lean theorem
  in this module.
- **PROVED (literature).** Over the integers, the paper's increasing
  chain of $hk-h+1$ sums uses at most two values (§4, printed p. 11).
  Hence both minima are at least $hk-h+1$ for $k,h\ge1,r\ge2$.
  An arithmetic progression attains that size for $hA$, and its restricted
  sumset is contained in $hA$, so both minima equal $hk-h+1$.
- **OPEN.** Classifying the abelian groups giving equality for all
  attainable $k$, all $h\ge1$ and $r\ge2$ remains unresolved here.
  No positive conclusion for other open questions follows from this
  counterexample; the source's integer results retain their hypotheses.

## ASSUMED-UNVERIFIED

Exhaustive literature coverage and priority are unverified. Google
Scholar's complete cited-by list was unavailable in the supplied search
(403/429). No new network search is asserted. The cyclic and mixed-group
survey is finite computation, not a classification theorem.
