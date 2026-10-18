---
bibkey: kochnarayan2025uniquedomination
authors: Garrison Koch; Darren Narayan
year: 2025
title: Maximal bipartite graphs with a unique minimum dominating set
doi: 10.48550/arXiv.2511.01719
url: https://arxiv.org/abs/2511.01719v1
claim: Conjecture 1 gives a universal upper bound on the number of edges of a finite bipartite graph without isolated vertices and with a unique minimum dominating set, gamma>=2 and n>=3gamma.
strata_touched:
  - D5/S3/Combinatorics/Graph/Domination/KochNarayanRefutation
license: citation-only
triage: anchor
---

# Maximal bipartite graphs with a unique minimum dominating set

## Verified locator

DOI: 10.48550/arXiv.2511.01719

Source: https://arxiv.org/abs/2511.01719v1

Garrison Koch and Darren Narayan, arXiv:2511.01719v1, Conjecture 1,
https://arxiv.org/html/2511.01719v1#Thmthm1 . The version-labelled HTML has
529796 bytes and SHA-256
`3d162c10af28d4c8bd3e99067957bdee5b0dc3fbfb1d9a5f2abadf4140d5f54d`.
The original source archive at https://arxiv.org/src/2511.01719v1 has 20238
bytes and SHA-256 `17eec52a57890ab6701926b32a504708d149170fae22ed079d63f85fa0e7ea0d`.
Its `PaperDraft.tex` has 74665 bytes and SHA-256
`7366e581aa872f30d593ecd7dc7eb43a1867a5da89f760cf492304fd862e7a08`;
the conjecture's TeX label is `conj:MAINEDGE`.

> Let G be a bipartite graph without isolated vertices with order n and dominating
> number gamma. Let G have a unique minimum dominating set. If gamma >= 2 and
> n >= 3gamma, then the size of G, s(G), is bounded above by m(n,gamma).

Writing a = ceil(gamma/2) and b = floor(gamma/2), the printed expression is

    Phi(n,gamma) = max(0,n-3gamma-2a-b+1),
    m(n,gamma) = 2gamma+2ab+min(n-3gamma,2a-b+1)(2a+1)
                 + sum(i=1,...,Phi(n,gamma)) ((2a+1)+ceil(i/2)).

Subtractions in this formula are integer subtractions. The positive part is
taken before interpreting the summation interval. A dominating set contains or
neighbors every vertex; minimum means minimum cardinality among all dominating
sets. The source does not assume connectedness, minimum degree two, or a balanced
split of the centers between the two parts.

## Counterexample and scope

On vertices 0 through 13, take parts {0,...,6} and {7,...,13}. Join 0 to
10,11,12,13; join 7 to 1,2, join 8 to 3,4 and join 9 to 5,6; join each of
1,...,6 to each of 10,12,13. These are 4+6+18=28 distinct unordered edges.
There are no isolated vertices. The unique minimum dominating set is
{0,7,8,9}, of cardinality four. At n=14 and gamma=4, the printed Phi is zero
and the printed bound is 26.

Construction Case 3 suggests the different residual index
max(0,n-3gamma-2a+b-1). Both indices are zero at (14,4), and Case 2 gives 26
there. The formal result refutes the printed Conjecture 1; it neither replaces
the index silently nor asserts a result for an unspecified corrected conjecture.
It gives no true extremal formula and does not resolve the earlier unrestricted
Fischermann-Rautenbach-Volkmann problem.

## Sources, reuse and search boundary

The native domination predicates and minimum-attainment interface are those of
`GraphCoverDomination`, a scoped Apache-2.0 source port from
google-deepmind/formal-conjectures commit
8323e878b83fcd7f4a448256069352a265460d75,
`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Domination.lean`.
That module retains the full attribution and license. The graph, finite
cardinality, bipartiteness and unordered-edge interfaces are pinned Mathlib
objects. The counterexample uses elementary counting and private-neighbor
reasoning also present in the source; no independent-invention claim is made.

The completed bounded source screen checked the arXiv ID, exact title and
unique-domination/bipartite topic queries, and a limited Crossref title lookup.
It found source v1 and no exact resolution in that scope. Access-limited searches
supply no negative evidence. Literal source-name and unique-domination searches
in the repository found the native general-purpose owners and no existing exact
resolution. These are bounded overlap results, not global novelty or priority
certification. A prior exact resolution would remove open-problem credit without
changing the formal counterexample.
