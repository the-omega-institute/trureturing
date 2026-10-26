---
bibkey: mazorchukxu2026cokernel
authors: Volodymyr Mazorchuk, Shuoyang Xu
year: 2026
title: "On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers"
doi: 10.48550/arXiv.2610.07999
url: https://arxiv.org/html/2610.07999v2
claim: "Section 5.7 conjectures that every fixed first-column deficit i gives a polynomial of exact degree 2i and leading coefficient 1/i!."
strata_touched:
  - D5/S3/Combinatorics/BinomialBases/MazorchukXuClosure
  - D5/S3/Combinatorics/BinomialBases/MazorchukXuFamilies
  - D5/S3/Combinatorics/BinomialBases/MazorchukXuOrder
  - D5/S3/Combinatorics/BinomialBases/MazorchukXuGeneric
license: citation-only
triage: anchor
---

# Mazorchuk and Xu: first-column deficit counts

## Verified locator

DOI: 10.48550/arXiv.2610.07999

URL: https://arxiv.org/html/2610.07999v2

The source is version 2. Section 3, before Section 3.1, defines the triangular subsets and Condition
(star), Section 5.1 defines the first-column statistic, and Section 5.7 states:

> It seems reasonable to conjecture that $r(n,n+1-i)$ is a polynomial in $n$ of
> degree $2i$ and leading coefficient $\frac{1}{i!}$.

The introductory fixed-parameter context is “any fixed number of missing
points.” Propositions 11–14 already give the deficits zero through three.
Proposition 15 concerns the separate restriction that all rows be nonempty.

The versioned HTML has SHA-256
`b0cb87d1bf47f986b282c2594bec44b78f65982e8f82ae227f5107eafe3468b1`.

## Literal finite model

For $n\in\mathbb N$, let $T(n)=\{(a,b):0\le a\le b\le n\}$.
A subset $Y$ belongs to $R(n)$ if every three selected points $(a,b),(c,d),(e,f)$,
allowing repetitions, with $a\le c,e\le b\le d,f$ force
$(\max(c,e),\max(d,f))\in Y$ and, when $b<\min(d,f)$,
$(b+1,\min(d,f))\in Y$. The statistic counts selected points with first
coordinate zero. Empty rows and the empty subset are allowed.

The conjecture asks for one polynomial for each $i\in\mathbb N$, valid at every
$n\in\mathbb N$ satisfying $i\le n+1$, with exact degree $2i$ and leading
coefficient $1/i!$. It does not assert integer coefficients. Rational
polynomials provide characteristic-zero numerical polynomials by the usual
embedding into the reals. There is no value of $r(-1,k)$ in this domain and no
field or representation-realization hypothesis in this combinatorial statement.

## Mathematical scope

The point map $(a,b)\mapsto(a,b+1)$ is a counted equivalence with strict ordered
edges on $0,\ldots,n+1$. The repeated-point condition becomes two universal
edge rules. Monotone clique-fiber expansion preserves these rules; an increasing
section gives the converse. Exceptional-to-ordinary incidence has a unique
cutoff, including an empty ordinary list, and monotone threshold graphs satisfy
both rules. Arbitrary cutoff data admit a bounded threshold completion;
fully generic data have a unique completion. Sorting the actual anchor-neighbor set and its complement extracts position and
cutoff data from every valid member of the literal finite family, with precisely
i exceptions and s(j)=p(j)+j+1. Agreement of the anchor edges,
cutoffs and exceptional-edge bits determines the entire labelled graph.

These structural results do not establish the conjecture. The finite
pattern/reconstruction bijection, the exact binomial counting identity and the
factorial count of generic patterns remain separate mathematical obligations.
No originality or priority claim is made. Bounded searches authenticated no
exact existing Lean supplier; differently expressed equivalents and the full
later literature are not excluded.
