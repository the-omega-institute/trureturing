---
slug: mazorchuk-xu-2026-first-column-deficit-polynomial
bibkey: mazorchukxu2026cokernel
doi: 10.48550/arXiv.2610.07999
url: https://arxiv.org/html/2610.07999v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/BinomialBases/MazorchukXuTopPatterns.mazorchukXu_conjecture
---

# Mazorchuk–Xu: every first-column deficit has a counting polynomial

## Problem

Volodymyr Mazorchuk and Shuoyang Xu, *On the number of cokernel-closed additive
subcategories for uniformly oriented A_n quivers*, arXiv:2610.07999v2,
Section 5.7, conjecture:

> It seems reasonable to conjecture that $r(n,n+1-i)$ is a polynomial in $n$ of
> degree $2i$ and leading coefficient $\frac{1}{i!}$.

The preceding sentence specifies “any fixed number of missing points.” This dossier
anchors the whole conjecture: for every natural $i$, one rational polynomial $P_i$
has exact degree $2i$, leading coefficient $1/i!$, and satisfies
$P_i(n)=r(n,n+1-i)$ for every natural $n$ with $i\le n+1$.

Section 3, before Section 3.1, defines $T(n)=\{(a,b):0\le a\le b\le n\}$ and its
subsets satisfying Condition (star). Three selected points $(a,b),(c,d),(e,f)$,
allowing repetitions, with $a\le c,e\le b\le d,f$ force
$(\max(c,e),\max(d,f))$ and, if $b<\min(d,f)$, also $(b+1,\min(d,f))$.
Section 5.1 defines $r(n,k)$ as the number of these subsets with exactly $k$
selected first-column points. Empty subsets and rows are permitted.

### Source correspondence

| Source clause | Lean counterpart |
| --- | --- |
| Literal triangular subsets | `triangle`, `Star`, `family`, `count` in `MazorchukXuClosure` |
| Repeated selected points and both forced conclusions | All three membership premises in `Star`; `star_iff_rules` proves equivalence with the ordered-edge rules |
| Exact first-column statistic | `firstColumnCard`; `count_eq_edgeFamily_card` preserves its value |
| Every fixed deficit | Outer `∀ i : ℕ`, followed by `∃ p : Polynomial ℚ` before `∀ n` |
| Every defined rank | `∀ n : ℕ, i ≤ n+1 → p.eval (n : ℚ) = (count n (n+1-i) : ℚ)` |
| Exact degree and leading coefficient | `p.natDegree = 2*i` and `p.leadingCoeff = (i.factorial : ℚ)⁻¹` |
| Boundary cases | No exclusions of `i=0`, `n=0`, `i=n+1`, zero or tied coordinates, or empty rows |

There is no eventual threshold, fixed-deficit bound, nonempty-row or representation
hypothesis. The source does not require integer coefficients. The canonical embedding
of the rational polynomial into the reals preserves evaluation, degree and leading
coefficient. The separate recurrence convention at rank $-1$ is outside this domain.

## Motivation

The source question is preregistered at
https://github.com/the-omega-institute/trureturing/issues/22059, with the unchanged
prospective event and forecasts in comment 6406990092. Propositions 11–14 already
settle deficits zero through three; those cases are prior work. The theorem
`D5/S3/Combinatorics/BinomialBases/MazorchukXuTopPatterns.mazorchukXu_conjecture`
settles all deficits simultaneously through one parameter-unbounded construction.
Each of its nine modules has structural escape-witness content; no module uses the
open-problem-resolution admission exception.

## Gap

The generic positive-distinct-coordinate count alone cannot cover the conjecture:
zero coordinates and ties occur at the smallest valid ranks. The exact reconstruction
and support-fiber bijections retain all of them before the top coefficient is counted.

The mathematical endpoint has no residual hypothesis. The four-slot escape audit has
three validated count registrations and 33 unfinished targets under
https://github.com/the-omega-institute/trureturing/issues/22125#issuecomment-6409930292.
The three retained Closure registrations have `IE-C050` source-binding diagnostics;
the other 30 targets lack complete faithful family/readout and intervention evidence.
For the final theorem, the imported nullary `Conjecture` is owned by another module,
so the existing same-owner named-definition entry supplies no validated binding.
These audit gaps are not additional mathematical premises.

## Route

The map $(a,b)\mapsto(a,b+1)$ is an exact counted equivalence with strict ordered
edges. Sort the anchor neighbors and their complement. Each exceptional label has a
weak position, an ordinary cutoff and exceptional-edge bits. Monotone clique expansion,
rank-ceiling refinement and a universal greatest tail preserve the two closure rules.
Canonical labels reconstruct every admissible datum; recovering the labels, cutoffs
and bits gives the inverse. Thus this is an actual bijection with the literal family.

Group data by their positive coordinate support. With $M=n+1-i$, prescribed-support
compression and expansion give

$$
r(n,n+1-i)=\sum_{k=0}^{2i}a_{i,k}\binom{M}{k}.
$$

Here $a_{i,k}$ counts admissible weak-coordinate data at ordinary size $k$ using every
positive value. Its definition is independent of $n$. The rational shifted
falling-factorial sum therefore evaluates to the count at every valid rank.

A support of size $2i$ forces the $i$ positions and $i$ cutoffs to be positive and
pairwise distinct. The closure rules then determine the exceptional bits uniquely.
Choose the $i$ position values from $2i$ ordered values, then permute the complementary
cutoffs. This bijection proves $i!a_{i,2i}=(2i)!$. Consequently the coefficient at degree
$2i$ is $a_{i,2i}/(2i)!=1/i!\ne0$, proving exact degree and leading coefficient.

## Falsifier

A counterexample would be a natural deficit for which no single polynomial has all
three stated properties on every valid rank. A generic-only or eventual counting formula
would not rule this out. The theorem constructs the required polynomial for arbitrary
$i$ and proves its literal count identity throughout that domain.

## Evidence

The nine Lean modules from `MazorchukXuClosure` through `MazorchukXuTopPatterns` in
`D5/S3/Combinatorics/BinomialBases/` and their Blueprint Scribe give the definitions,
bijections and polynomial proof. Their symbolic finite sets have unbounded parameters;
`utility: none` records structural mathematics, not a bounded enumeration or certified
finite instance. No additional theorem or wrapper records a specialization.

Pinned Mathlib supplies ordered finite enumeration, finite-bijection cardinality,
choose/factorial identities, descending Pochhammer evaluation and polynomial APIs.
No exact full supplier was authenticated by the bounded repository, indexed Lean and
Enomoto-package searches described in the source issue and Library note. Differently
phrased equivalents, all later literature and worldwide priority remain outside those
searches. Source provenance does not certify originality.

## Triage

### What the settlement shows

- Proved: the complete source conjecture, by
  `D5/S3/Combinatorics/BinomialBases/MazorchukXuTopPatterns.mazorchukXu_conjecture`.
- Proved: exact support compression and the binomial expansion, by
  `MazorchukXuNormalization.coordinateDataSupport_fiber_card` and
  `MazorchukXuNormalization.count_eq_binomial_sum`; these explain polynomiality at
  small ranks, including tied and zero coordinates.
- Proved: the top factorial identity, by
  `MazorchukXuTopPatterns.patternCoefficient_top_factorial`; it explains both the
  exact degree and the leading coefficient, including deficit zero.
- Boundary: the result is the literal combinatorial conjecture. It adds no arbitrary-field
  representation theorem and does not resolve other source questions or claim a new
  proof of the source's already known first four formulas as separate results.
- Unresolved successor candidate: is $a_{i,k}>0$ for every natural $i$ and $k\le2i$,
  where $a_{i,k}$ is the exact `patternCoefficient i k` of
  `MazorchukXuNormalization`? The theorem proves the top coefficient is positive;
  it does not establish positivity of every lower support coefficient. This candidate
  has no completed literature, counterexample, discrimination or admission screening
  and carries no additional resolution credit.

## ASSUMED-UNVERIFIED

No worldwide novelty, priority, complete later-work census or exclusion of differently
expressed equivalents is asserted. Independent final reviews, required CI, merge and
containing-dev verification are delivery obligations separate from the mathematical
statement. The 33 unfinished escape-audit targets retain their linked-issue boundary;
three validated registrations do not establish overall audit completion.
