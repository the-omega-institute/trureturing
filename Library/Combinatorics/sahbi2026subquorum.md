---
bibkey: sahbi2026subquorum
authors: Rafik Sahbi
year: 2026
title: "Sub-quorum colorings of graphs"
doi: 10.48550/arXiv.2609.25128
url: https://arxiv.org/html/2609.25128v1
claim: "Conjecture 6.4 asks whether the sub-quorum chromatic number of Q_n is 2^(n-1) for every integer n>=2."
strata_touched:
  - D5/S3/Combinatorics/Graph/HypercubeSubQuorum
license: citation-only
triage: anchor
---

# Sahbi's hypercube sub-quorum conjecture

## Verified locator

DOI: 10.48550/arXiv.2609.25128

URL: https://arxiv.org/html/2609.25128v1

The primary source is arXiv:2609.25128v1, dated 20 September 2026. Its
versioned HTML was read on 23 September 2026. This note records the exact
definition, target, attribution, and mathematical mapping; it does not
reproduce the paper.

## Exact definition and target

Definition 2.2 takes an onto partial map from a colored support `S` to the
positive color set `{1,...,k}`. For each colored vertex `v`, the number of
vertices of its own color in the closed neighborhood, restricted to `S`,
is at least half the number of all colored vertices in that closed
neighborhood. Thus the center is included exactly once and uncolored
neighbors are excluded. The formal predicate `IsSubQuorumColoring` uses
the equivalent doubled natural-number inequality.

The source defines `psi_sq(G)` as the largest attainable color count. The
formal `SubQuorumAttainable n k` existentially packages the support and
onto coloring, and `subQuorumChromaticNumber n` uses `Nat.findGreatest`
with bound `2^n`. Surjectivity gives the bound `k<=|S|<=2^n`. A singleton
support attains one color in every dimension, proving that the selected
maximum is positive and attained rather than the default zero for an empty
predicate.

Conjecture 6.4 states, with its full quantifiers,

    for every integer n>=2, psi_sq(Q_n)=2^(n-1).

The source proves this only for `2<=n<=6`. The formal consumer proves the
displayed equality for every natural `n` satisfying `2<=n`; it does not
replace the target by a finite range, a total coloring, or a conditional
statement.

## Upper bound for arbitrary partial colorings

Given an arbitrary admissible onto `k`-coloring, let `E` be the colors whose
colored class contains an edge and `N` the remaining colors. Choose the two
endpoints of one edge for every color in `E`, and one representative for
every color in `N`. The selected map is injective: vertices selected for
different colors cannot coincide, while the two endpoints selected for one
edged color are distinct. Let `A` be the set of all selected vertices and
let `T` consist of the representatives of `N`. Then

    |A|=|N|+2|E|,  |T|=|N|,  and  |A|+|T|=2k.

For `t` in `T`, the class of `t` has no internal colored edge. Its number
of same-color neighbors is zero, so Definition 2.2 gives total colored
degree at most one. In particular, `t` has at most one neighbor in `A`.
Every `a` in `A` has at most `n-1` neighbors in `T`: if `a` lies in `T`,
the preceding degree bound and `n>=2` suffice; if `a` is an endpoint
selected from an edged class, its selected partner is a cube neighbor
outside `T`, and the cube is regular of degree `n`.

Let `B` be the complement of `A`. Use Huang's recursively signed cube
adjacency matrix `S_n`. It is symmetric, its nonzero entries have absolute
value one and occur exactly on cube edges, and `S_n^2=nI`. For a real
vector `x` supported on `T`, finite Cauchy-Schwarz in each row of `A`,
followed by reversing the finite sums and using the column bound on `T`,
gives

    sum_(a in A) (S_n x)_a^2 <= (n-1) sum_(t in T) x_t^2.

The square identity gives total energy
`sum_v (S_n x)_v^2=n sum_(t in T) x_t^2`; hence the energy on `B` is at
least `sum_(t in T) x_t^2`. Restricting `S_n x` to `B` therefore defines
an injective linear map from real functions on `T` to real functions on
`B`. `LinearMap.finrank_le_finrank_of_injective` and the dimensions of
finite function spaces imply `|T|<=|B|`.

Finally `|A|+|B|=2^n` and `|A|+|T|=2k`, so `2k<=2^n` and
`k<=2^(n-1)`. This argument applies to every admissible partial coloring,
including supports that omit cube vertices.

## Parity attainment

The even-parity vertices form an independent set because a cube edge flips
exactly one coordinate and therefore flips parity. Parametrizing this set
by `Fin (n-1) -> Bool` gives exactly `2^(n-1)` vertices. Assigning a
different color to every such vertex is onto and admissible: there are no
colored neighbors, so both closed-neighborhood counts equal one. This
attains the upper bound and proves the exact value.

## Attribution and library reuse

The definition, Lemma 5.4 selection idea, finite-dimensional cases, and
Conjecture 6.4 are due to Sahbi. The signed matrix facts come from Hao
Huang, "Induced subgraphs of hypercubes and a proof of the Sensitivity
Conjecture", Annals of Mathematics 190 (2019), 949-955, Lemma 2.2,
DOI 10.4007/annals.2019.190.3.6, also arXiv:1907.00847. The implementation
reuses the pinned Mathlib module `Archive.Sensitivity` and bridges its
operator to the existing repository graph
`D5/S3/Combinatorics/Graph/Hypercube.hypercube`; it does not define a
second hypercube.

The repository-derived content is the restricted norm/count argument and
its application to arbitrary source-faithful partial colorings. Pinned
Mathlib also supplies finite Cauchy-Schwarz, the finite-dimensional
injective rank comparison, and the dimension of finite real function
spaces. The Mathlib revision is
`db584cd6d46c92f209a44c0f1c829460d327499d`.

## Bounded prior evidence

The exact target, source version, quantifiers, Tier 1 classification, and
planned proof route were preregistered in repository issue 9523 under
programme issue 8654 before Lean or numerical probes. The issue records
the repository, pinned Mathlib, and literature search scope. Those checks
did not identify an earlier all-`n` resolution in the inspected material.
This is bounded search evidence only. Worldwide absence of an equivalent
proof, novelty, and priority remain `ASSUMED-UNVERIFIED`.
