---
slug: das-ashni-sangeetha-2026-mixed-power-extrema
bibkey: dasashnisangeetha2026graphpowers
doi: 10.48550/arXiv.2611.29397
url: https://arxiv.org/abs/2611.29397v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/SpectralGraph/MixedPowerExtrema.result
---

# Das–Ashni–Sangeetha Question 5.1

## Problem

Joyentanuj Das, Anto Jerrin Ashni R, and Sangeetha C ask for the graphs
minimizing or maximizing the largest eigenvalue of
Aα(Gᵏ) = α Deg(Gᵏ) + (1−α) A(Gᵏ) over connected graphs of
order n, for 0≤α<1. They cite a prior result for k=2 and ask
about the path and its dependence on α for k≥3.
[arXiv:2611.29397v1, §5, Question 5.1, printed p. 17](https://arxiv.org/pdf/2611.29397v1#page=17)

## Motivation

The adjacency extremum concerns α = 0, and the source cites the
mixed-matrix result for k = 2. Question 5.1 asks whether the path stays
extremal for small positive α when k ≥ 3, and how the answer depends on α.

## Gap

The literature screen recorded for the mixed range k ≥ 3 and 0 < α < 1
found no proof in the sources it could inspect.
[Preregistration and literature screen](https://github.com/the-omega-institute/trureturing/issues/34873)

## Route

For the lower bound, compare a connected graph to a spanning tree.
Reflect paired coordinates around the two attachment points of a
terminal-leaf move. The norm stays fixed and the mixed edge energy is
monotone under compression. The sum of distance deficits from a fixed
vertex decreases along the rooted moves, giving a path in finitely many
steps. At the last move a positive maximal vector gives strictness by
one extra incidence for k≥2, and by the eigenvector row identities
in the three possible coordinate orders for k=1. A chord on a
spanning path adds a power edge beyond the complete-power range. A
positive eigenvector and comparison to the complete graph characterize
the upper equality. At n=k+2, a missing power edge forces a spanning
shortest path.

## Falsifier

A graph in the stated domain violating either bound or either direction
of either equality classification would refute the result. A difference
between the mixed matrix or graph power used in Lean and those of the
paper would break the source correspondence.

## Evidence

The settling declaration is
`D5.S3.Combinatorics.SpectralGraph.MixedPowerExtrema.result`. The
correspondence uses the actual `graphPower` declaration and the
`mixedTop_isGreatest` real spectrum theorem. The theorem gives both bounds and both directions of each equality
condition.
[Formal proof and registration scope](https://github.com/the-omega-institute/trureturing/issues/34873#issuecomment-7224151884)

## Triage

For a finite connected simple graph G of order n≥1, any integer
k≥1, and any real 0≤α<1, write λ(H) for the greatest real
eigenvalue of α Deg(H) + (1−α) A(H). Then

**λ(Pₙᵏ) ≤ λ(Gᵏ) ≤ n−1.**

The lower equality holds exactly when n ≤ k + 1 or G is isomorphic to Pₙ.
The upper equality holds exactly when every pair of vertices has distance
at most k in G. The path and the complete graph attain the respective
endpoints. For n ≤ k + 1 every connected graph attains both endpoints.
The extremizer classes are independent of α throughout 0 ≤ α < 1. The source interval ends before α = 1.
[Public settlement](https://github.com/the-omega-institute/trureturing/issues/34873#issuecomment-7223071852)

## ASSUMED-UNVERIFIED

Worldwide priority remains unverified. The bounded literature screen
records inaccessible full texts and rate-limited citation indexes.
[Search scope](https://github.com/the-omega-institute/trureturing/issues/34873)
