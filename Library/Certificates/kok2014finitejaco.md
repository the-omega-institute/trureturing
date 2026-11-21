---
bibkey: kok2014finitejaco
authors: Johan Kok; Paul Fisher; Bettina Wilkens; Mokhwetha Mabula; Vivian Mukungunugwa
year: 2014
title: Characteristics of Finite Jaco Graphs, J_n(1), n in N
doi: 10.48550/arXiv.1404.0484
claim: Theorem 2.10 (Conjectured) gives a two-branch maximum-total-degree addition law for all distinct orders at least three.
strata_touched:
  - D5/S3/ConceptDynamics/GraphColoring/JacoAdditionLawRefutation
  - D5/S3/ConceptDynamics/GraphColoring/JacoAdditionLaw
  - D5/S3/ConceptDynamics/GraphColoring/JacoDegreeShift
  - D5/S3/ConceptDynamics/GraphColoring/JacoMaximumSet
  - D5/S3/ConceptDynamics/GraphColoring/JacoProgression
license: CC-BY-3.0
triage: anchor
---

# Characteristics of finite Jaco graphs

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.1404.0484

Johan Kok, Paul Fisher, Bettina Wilkens, Mokhwetha Mabula and Vivian
Mukungunugwa, [arXiv:1404.0484v1](https://arxiv.org/abs/1404.0484v1),
*Characteristics of Finite Jaco Graphs, J_n(1), n in N*.
The [primary PDF](https://arxiv.org/pdf/1404.0484v1) locates the conjectured
addition assertion at Theorem 2.10 on printed page 7 and the explicit open
problem on printed page 11. Definitions 1.1--1.4 and 1.7 on printed page 2
specify the recursive graph, its Jaconian vertices and ordinary total degree.

## Source interpretation

The original theorem states, for distinct n,m at least three, that the maximum
degree of J_(n+m)(1) equals the sum of the two maximum degrees if J_n(1) or
J_m(1) has a unique Jaconian vertex, and equals that sum plus one otherwise.
The source's open prompt reads: “Prove Theorem (conjectured) 2.10.”

Vertices have positive labels. A forward arc from i to j exists exactly when
i<j and j<=2i-d^-(v_i); finite graphs truncate vertices and arcs beyond their
order. A Jaconian vertex attains the maximum ordinary total degree.
Uniqueness concerns a vertex within one graph. Forgetting orientation counts
each forward arc once as a simple edge and preserves ordinary total degree.

The source metadata links [CC BY 3.0](https://creativecommons.org/licenses/by/3.0/).
The statement and notation are adapted with attribution to the five authors.
The source includes a Creative Commons attribution notice. No executable code is copied from the article.

Kok's later [arXiv:2507.16500v1](https://arxiv.org/abs/2507.16500v1), Table 1,
is prior published numerical data containing the degree values used in the
counterexample. The proof uses existing exact recursive-graph suppliers,
not the table as an assumption. That paper's Claim 2.10 concerns domination
paths and is a different assertion.

Bounded source screening found no specific complete resolution in its
successfully inspected sources. MathDB live contents, complete citation
enumeration, the special issue *Reflections on Jaco Graphs*, the named
domination research note and unindexed sources remain coverage gaps. No
worldwide openness, first computation, or publication-priority claim follows.

## Corrected addition law

The repository's corrected law is not stated in the source. Write phi for
the golden ratio, frac(n) for the fractional part of (n+2)/phi and
alpha=sqrt(5)-2. For every finite family of natural orders with r members
and total N, Delta(N) minus the sum of the members' maximum degrees
equals floor(sum frac(n_j)-(r-1)alpha). For two summands the correction is
-1, 0 or 1 according to the position of frac(n)+frac(m) relative to alpha
and 1+alpha, attained at the orders (3,11), (3,4) and (4,6). The maximum-degree
formula floor((n+2)/phi)-1 that it rests on appears as Theorem 4.8 of Raso and
Kok, [arXiv:2611.01554v1](https://arxiv.org/abs/2611.01554v1), whose readable
text contains no addition law. A bounded web search found no published
statement of the corrected law; no worldwide priority claim follows.

## Maximum degree and the shifted order

Theorem 2.9 on printed page 7 states only that, with m=n+Delta_n, the graph
J_m(1) has maximum degree n or n-1. Its proof splits on the outdegree
d+(v_n), which equals b_n=floor((n+1)/phi), and in its second case concludes
only "n or n-1". The repository proves the sharper statement for every
natural n: Delta_n equals b_n or b_n-1, the first case holds exactly when the
fractional part of (n+2)/phi is below 1/phi, and the order n+Delta_n has
maximum degree n in the first case and n-1 in the second.

## Maximum sets

Lemma 2.2 (Conjectured) on printed page 4 asserts that b_(n-1)<b_n<b_(n+1)
implies that v_(b_n) is the unique Jaconian vertex of J_n(1), and the
open-problem list on printed page 11 asks to prove it. The repository proves
this implication for every n; the converse, which the source does not assert,
fails at n=5, where J_5={v_3} although b_4=b_5=3. It also proves the complete
description of the maximum set for n at least two: the label interval from
Delta_n to R_t with t=n-Delta_n, of one, two or three vertices, with exact
singleton criteria. The request attributes that description to Patel's
solution posted on MathDB; MathDB refuses automated fetches, and those answers
were not inspected, so they may already settle Lemma 2.2 and no priority is
claimed.

## Progressions of orders

The first open problem on printed page 11 records that the maximum degree of
J_(5k)(1) is 3k for 5k in [1,44] and 3k+1 for 5k in [45,99], and asks for a
partitioning of the orders that closes this pattern. The repository proves that for all d and k,
Delta(dk)=floor(d/phi)k+floor(beta_d k+alpha), where beta_d is the fractional
part of d/phi and alpha=sqrt(5)-2, and gives the exact range of k for each
value of the correction. For d=5 the correction equals q exactly on the blocks
[5k_q,5k_(q+1)-1] (the first starting at 1), with k_q=floor((5q-1)phi)+3q;
these blocks partition the positive integers.
Possible answers posted on MathDB were not inspected, so no priority is
claimed.
