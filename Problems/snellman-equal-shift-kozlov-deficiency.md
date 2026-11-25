---
slug: snellman-equal-shift-kozlov-deficiency
bibkey: snellman2026kozlov
doi: 10.48550/arXiv.2611.26110
url: https://arxiv.org/pdf/2611.26110v1#page=52
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Kozlov/EqualShiftDivisibility.equal_shift_kozlov_deficiency_divisible
---

# Snellman's equal-shift Kozlov deficiency divisibility question

## Problem

Jan Snellman asks the following in *Hilbert functions over the exterior
algebra and f-vectors in higher rank III: Lattice points of the Kozlov
polytope*, arXiv:2611.26110v1, §10 item 2, p. 52.

> At equal shifts, find the polynomial L_{Koz(n)}(r) − a(r) for general n: it vanishes for n ≤ 3, and at n = 4, 5 (Corollary 35) it is divisible by r(r + 1). Is it always?

For every natural $n\ge 1$, use the ground set $\operatorname{Fin}(n)$.
Let $S_n$ be the set of f-vectors of downsets containing the empty face
and all singletons. Coordinate $k$, for $0\le k\le n$, counts faces of
size $k$. For each positive natural rank $r$, take the two counts

$$
a_n(r)=\#\left\{\sum_{i=1}^{r}v_i\,\middle|\,v_i\in S_n\right\},
\qquad
L_n(r)=\#\left(\mathbb Z^{n+1}\cap r\,\operatorname{conv}_{\mathbb R}(S_n)\right).
$$

The tuple of summands permits repetitions, and the sumset counts distinct
vectors. The convex hull and dilation are over the reals. For each $n$,
there exist $A,L\in\mathbb Q[X]$ which evaluate to the respective counts
at every positive natural $r$. The source's final yes-or-no question
asks whether every such pair satisfies $X(X+1)\mid L-A$. This includes
$n=1$. The separate requests for a general explicit formula and for
fill-rate limits and rates lie outside this question.

## Motivation

The two counts compare the actual proper equal-shift sums with all
lattice points in their convex-geometric dilation. The common roots
constrain the polynomial discrepancy across all positive ground-set sizes.

## Gap

Part III, Corollary 34, states that both counts are polynomials. It
credits Part II, Theorem 36, for the proper count and uses the transfer
formula of Part II, Theorem 41. Part III, Proposition 31(2), gives the
Ehrhart root at minus one for $n\ge3$, and Corollary 35 gives the
divisibility cases $n=4,5$.
[Part III, Corollaries 34 and 35](https://arxiv.org/pdf/2611.26110v1#page=30) ·
[Proposition 31](https://arxiv.org/pdf/2611.26110v1#page=28) ·
[Part II, Theorem 36](https://arxiv.org/pdf/2610.14985v1#page=27) ·
[Theorem 41](https://arxiv.org/pdf/2610.14985v1#page=31)

The exact all-$n$ divisibility question is posed in Part III, §10
item 2. The bounded search covered the three arXiv versions, the
immutable author archive, cited Kruskal–Katona and lecture-hall
decomposition results, the repository and formal-conjectures path
index, and arXiv, DataCite, Crossref and OEIS queries. It located the
published count formulas and the stated small-size cases. The bounded
search located no proof of the full divisibility statement.
[Preregistration #32792](https://github.com/the-omega-institute/trureturing/issues/32792)

Part II, Lemma 40 and the proof of Theorem 41, obtain the proper
chained representative by the lex submodule argument. The author's
Lean proper transfer takes an explicit surjectivity premise. The
formal proof below supplies an unconditional equal-shift construction
for the literal proper carrier. The lattice decomposition specializes
Part III, Theorem 6 and Corollary 7.
[Part II, Theorem 41](https://arxiv.org/pdf/2610.14985v1#page=31) ·
[Counting/Proper.lean](https://gitlab.liu.se/jansn19/exterior-convex/-/blob/2f05ce99d059c305ffcf6142fcf9efbbca02e24f/lean/ExteriorConvex/Counting/Proper.lean#L531) ·
[Part III, Theorem 6 and Corollary 7](https://arxiv.org/pdf/2611.26110v1#page=11)

## Route

At each degree, form the position-first lex segment whose mass is the
total number of missing faces in the input downsets. The upper-shadow
bound places its shadow inside the next chosen segment. Taking
complements yields proper downsets with the same coordinate totals.
The position-first property gives the chaining inequality.

The local LYM inequalities describe the literal real hull by normalized
antitone coordinates. Clipping an integral point at one unit of the
binomial capacities extracts a terminal chain member. The residual
normalized ratios are positive parts after subtracting one. Iterating
gives a chained integral decomposition of the literal real dilate.
Clipping also recovers the last summand of any bounded chain from its
sum, giving uniqueness.

Both counts at rank $r>0$ are first-to-last entries of transfer
matrices to power $r+1$. Each transfer matrix is upper unitriangular.
The falling-binomial expansion of its powers gives the corresponding
rational polynomial in $r$ and proves agreement at every positive
rank. Polynomial uniqueness then applies to any pair of interpolants.
At zero, power one selects the all-ones last column. At minus one,
power zero selects an identity entry, equal to one for $n=1$ and zero
for $n>1$. The two equalities give the two linear factors of $L-A$.

## Falsifier

A positive natural $n$ and rational polynomials agreeing with the two
literal counts at every positive rank would refute the proposed
divisibility if their difference evaluated to a nonzero value at zero
or minus one.

## Evidence

The settling declaration is
`D5/S3/Combinatorics/Kozlov/EqualShiftDivisibility.equal_shift_kozlov_deficiency_divisible`.
The companion `equal_shift_count_polynomials_exist` formalizes the
published existence statement by constructing both rational witnesses.
Its two continuation proofs use the literal transfer laws from the
chained representations supplied by `proper_sumset_surjOn` and
`lattice_chained_exists`. The exact source check binds
the two definitions of the counts, both existence claims and the
universal divisibility conclusion. The Lean endpoint has axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Triage

Tier 1, theorem, resolution Proved. The endpoint uses the
`open-problem-resolution` admission basis under the source's final
yes-or-no question. Its live proof uses the chained representations,
the matrix entries and polynomial uniqueness. Computational utility
is `none` for this universal proof. The exact source scope and
pre-probe criterion are recorded in the preregistration.
[Issue #32792](https://github.com/the-omega-institute/trureturing/issues/32792)

## ASSUMED-UNVERIFIED

Global priority and exhaustive absence of prior proofs remain unverified.
The bounded search covers the named source and the dependencies described
above.
