---
bibkey: rather2026bookroots
authors: Bilal Ahmad Rather
year: 2026
title: On roots of domination polynomials for friendship and book graphs
doi: null
url: https://arxiv.org/abs/2604.08998v2
claim: "The literal arXiv v1/v2 Conjecture 5.4 classifies all real roots with multiplicities for every shared-edge four-cycle book of order n >= 1; the order-one book contradicts its odd clause."
strata_touched:
  - D5/S3/Combinatorics/Graph/Domination/RatherBookRootRefutation
license: citation-only
triage: anchor
---

# Real-root configurations for book domination polynomials

## Verified locator

Source: https://arxiv.org/abs/2604.08998v2

The versioned full texts are https://arxiv.org/pdf/2604.08998v1 and
https://arxiv.org/pdf/2604.08998v2. The v1 title is *Root geometry of
domination polynomials for friendship and book graphs*; v2 uses the title
in the metadata above. Section and printed-page locators below refer to
these arXiv versions. The v2 HTML conjecture is at
https://arxiv.org/html/2604.08998v2#S5.Thmtheorem4.

The subject here is the location and multiplicity of finitely many real
roots, viewed as a configuration on the Euclidean real line. The underlying
graph model and its polynomial remain in the graph-domination module.

## The graph and ordinary count

Section 2, printed page 3 and Figure 1(b), defines the book B_n for every
integer n >= 1 by identifying one common edge in n copies of C4. All other
vertices are distinct. Printed page 11 explicitly identifies B_1 with C4.
The local n >= 2 hypothesis in Proposition 5.3 and numerical tables do not
supply a global n >= 2 hypothesis to Conjecture 5.4.

A subset S dominates a finite simple undirected graph G when every vertex
belongs to S or has a neighbor in S. The ordinary domination polynomial is

$$D(G,X)=\sum_{S\text{ dominates }G}X^{|S|}.$$

The formal vertex type is Fin (2*n+2). Vertices 0 and 1 are shared, and
page i has new vertices 2*i+2 and 2*i+3, with cycle
0--1--(2*i+2)--(2*i+3)--0. Adjacency is precisely these edges and their
reversals, without loops. The polynomial sums over the existing
DominatingSetAverage.domSets and uses its mem_domSets theorem and the
existing SimpleGraph.IsDominating predicate. This is the ordinary count,
with no independence or certified-domination restriction.

## The entire conjecture

Section 5, Conjecture 5.4, printed page 12:

> The numerical data suggest the following sharper parity-dependent statement.
> (i) If n is even, then D(B_n,x) has exactly four real roots counting multiplicity:
> 0 with multiplicity 2, one simple root in (-infinity,-2), and one simple root in (-1/2,0).
> (ii) If n is odd, then D(B_n,x) has exactly four real roots counting multiplicity:
> 0 with multiplicity 2 and two simple roots in (-1/2,0).

The closed formal claim quantifies over every natural n >= 1 and contains
both parity implications. Each branch specifies distinct nonzero real
numbers a,b, actual Polynomial.IsRoot predicates, actual rootMultiplicity
values 2,1,1, and for every real r the equivalence between being a root and
being one of 0,a,b. Thus intervals, exact multiplicities and exhaustiveness
are all part of the claim.

## The order-one obstruction

For B_1=C4, all six pairs, four triples and the full vertex set dominate.
The empty set and four singletons fail. Consequently

$$D(B_1,X)=6X^2+4X^3+X^4=X^2((X+2)^2+2).$$

For a nonzero real a, the factor a^2 is strictly positive and
(a+2)^2+2 is positive. There is therefore no nonzero real root. Applying
the odd branch at n=1 would supply such a root and is contradictory.
The formal result is the negation of the complete universal claim, using
the actual graph equality and finite dominating-set enumeration. The
separately amended claim restricted to n >= 2 remains unsettled by this
argument. The familiar C4 count and positive quadratic are prior
mathematics, not independent new root-classification results.

## Source qualification and prior ingredients

The author bibliography at https://sites.google.com/view/bilalahmadrr/publications
lists the exact paper as Filomat (2026), to appear. The arXiv record states
acceptance by Filomat. The actual journal text, any corrections and any
independently revised author manuscript remain unread. The target is the
literal arXiv v1/v2 conjecture; agreement with a journal text, absence of a
correction and author intent concerning the boundary are not established.

The established book polynomial occurs in arXiv:1401.2092, Theorem 8;
Question 3 asks about its roots. ArXiv:1501.05856, Theorem 5, repeats the
polynomial and Theorem 10 describes a root-limit set. These are prior
ingredients, not the same finite-order parity classification. Jahari and
Alikhani, *Some families of graphs with no nonzero real domination roots*,
EJGTA 6 (2018), 17–28, DOI 10.5614/ejgta.2018.6.1.2, treats other graph
constructions. Certified domination uses a different invariant.

The relevant six-page article by Saeid Alikhani, *Some new results on
domination roots of a graph*, Electronic Notes in Discrete Mathematics 43
(2013), 425–430, DOI 10.1016/j.endm.2013.07.062, remains unread. Its located
arXiv:1210.3144v1 PDF contains only a one-page abstract, and the institutional
IPM M/12991 record links an empty TeX document. Neither establishes whether
the journal article settles an equivalent complete claim.

The inspected primary sources did not identify an equivalent settlement;
this is a bounded literature conclusion, with the named full-text gaps.
It supplies neither global novelty nor an exhaustive ownership claim.
