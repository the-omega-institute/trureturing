---
bibkey: mishraraundal2021weaving
authors: Rama Mishra; Hitesh Raundal
year: 2021
title: Hecke algebra trace algorithm and some conjectures on weaving knots
doi: null
url: https://arxiv.org/abs/1908.04152v3
claim: "Conjecture 5.2 asks for the fixed-width large-m twist-number asymptotic for W(n+1,m); the present formalization develops actual graph-rank state counts and coefficient terms; the uniform graph coefficient estimate and chronological port incidences are proved, while mixed-state transfer and the graph/Jones bridge remain open."
strata_touched:
  - D5/S3/Topology/WeavingDiagramPorts
  - D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate
  - D5/S3/Combinatorics/Graph/Polynomials/TutteCoefficientAsymptotics
license: citation-only
triage: anchor
---

# Weaving-knot twist-number conjecture

The primary source is arXiv:1908.04152v3. Definition 5.1 (printed p. 21)
defines the higher twist numbers from the Jones coefficients, and Conjecture 5.2
(printed p. 23) states the fixed-width large- $m$ asymptotic involving

$$
d=n\bmod 2,\qquad r=(n-d)/2,
$$

with links included and no coprimality condition on $m$. The literal $n=1$
boundary is not silently included in the formalization target; the full
geometric/Jones route must preserve the source's width and link conventions.

The conjecture box says only “For a fixed n”; it does not explicitly impose
n>=2. The repository's auxiliary geometry covers n>=2 and m>=3, without
coprimality, and supplies no result for the box's literal n=1 reading.

The graph layer in
`D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate` defines the finite
signed rank-state polynomial using actual connected-component ranks, including
isolated vertices. It derives nonnegative state exponents, at most $2j$
nonisolated vertices in a rank-$j$ state, a uniform fixed-rank cyclic-subset
count under a bounded-forward-degree ordering, and the
$O_k((e+1)^{k-j})$ bound for an individual rank-$j$ coefficient term.
The counting proof uses a finite injection into source images and forward
neighbor slots, followed by an injection of edge subsets into support patterns.

The forest contribution does **not** equal the negative-binomial comparison
series. For the triangle, $v=e=3$ and $b=1$: its forest polynomial is
$1-z+z^2$, so its cubic coefficient is zero, while
$[z^3](1+z)^{-1}=-1$. The companion
`TutteCoefficientAsymptotics` module instead sums integer-binomial comparison
terms over all subsets. Their total is the ideal coefficient, and their forest
part agrees with the actual forest coefficient. The forest error is therefore
minus a comparison sum over cyclic states. Grouping this sum and the actual
cyclic contribution by graph rank proves, uniformly for every connected simple
graph with forward degree at most $D$ and every $k\ge1$,

$$
\left|[z^k]H_G(z)-(-1)^k\binom{b+k-1}{k}\right|
\le C(D,k)(e+1)^{k-1},\qquad b=e+1-v.
$$

The constant depends only on $D,k$. Integer binomial coefficients retain
negative comparison exponents, so the theorem includes small graphs, trees,
and the one-vertex case without truncating the comparison series. The first
coefficient is proved exactly equal to $-b$. The explicit weaving incidences, signed Jones--Tutte convention,
and all-width asymptotic also remain unproved here.

WeavingDiagramPorts derives the finite chronological matching from the
repeated generator sequence and proves the two uniform-smoothing component
classifications, exact circle counts and actual crossing endpoint formulas.
These are repository derivations motivated by the source, not theorems
attributed to it. They do not identify the normalized integral Jones
invariant, establish a forest-coefficient equality or prove Conjecture 5.2.
No priority, originality, uniqueness or original-problem credit follows.
The existing Aharonov–Jones–Landau Library note concerns a separate algebraic
Artin/trace bridge and also leaves geometric Jones identification unpaid.

The inspected source audit also records later width-three coefficient results and
a 2026 JIMS paper whose full body was unavailable in the public access route.
Consequently this note records the source and formalization boundary only; it
makes no priority, uniqueness, or open-problem claim.

The related paper is Rama Mishra and Hitesh Raundal, *Asymptotics of
Normalized Khovanov Ranks of Weaving Knots*, The Journal of Indian
Mathematical Society 93(3) (2026), 376–394,
DOI 10.18311/jims/2026/48582. The retained publisher metadata, abstract and
access response were inspected; the full body was not available through
that public access route. Its solution scope, including whether it proves
the exact all-width, all-k leading constant, remains unverified. The
abstract's order statement settles neither solution nor non-solution of
Conjecture 5.2, and the bounded search does not establish global novelty.

## Verified locator

- Primary source: https://arxiv.org/abs/1908.04152v3
- TeX/PDF locator: Definition 5.1, equation (5.5), and Conjecture 5.2.
- Related Jones--Tutte source used for the eventual classical bridge: Dasbach and
  Lin, *A volumish theorem for the Jones polynomial of alternating knots*,
  Pacific Journal of Mathematics 231 (2007), 279–291.
