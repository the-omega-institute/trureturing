---
bibkey: klavzaretal2026mobileproducts
authors: Sandi Klavžar; Aditi Krishnakumar; Dorota Kuziak; Ethan Shallcross; James Tuite; Ismael G. Yero
year: 2026
title: Moving through Cartesian products, coronas and joins in general position
doi: 10.1016/j.dam.2025.10.041
url: https://arxiv.org/abs/2505.00535
claim: "Section 3, after Proposition 3.7, conjectures that the mobile general position numbers of C₇ □ Pₛ and C₁₀ □ Pₛ are four for every s ≥ 5."
strata_touched:
  - D5/S3/Combinatorics/Graph/GeneralPosition/CylinderSevenTen
license: citation-only
triage: anchor
---

# Mobile general position on Cartesian products

## Verified locator

DOI: 10.1016/j.dam.2025.10.041

Source: https://arxiv.org/abs/2505.00535

The source is arXiv:2505.00535v2, published in Discrete Applied Mathematics
379 (2026), 768–780. Page numbers below refer to the arXiv PDF.

## Definitions

Section 1.1, page 3:

> The distance between vertices u, v ∈ V(G) is the length of a shortest u, v-path in G.

> If S ⊆ V(G) has the property that no three vertices of S lie on a common shortest path of G, then we say that S is a general position set of G.

> If a robot is located at a vertex u and u ∼ v, then we indicate the movement of the robot from u to v along the edge uv by u ⇝ v and refer to this as a move.

Section 1.1, pages 3–4:

> If a robot is stationed at a vertex u of S, then the move u ⇝ v is called a legal move if i) v ∉ S (thereby avoiding having more than one robot per vertex at any stage) and ii) the new set (S ∖ {u}) ∪ {v} is also a general position set.

Section 1.1, page 4:

> A configuration of robots on a general position set of G is called a mobile general position set if there is a sequence of legal moves starting from S such that every vertex of G is visited at least once by some robot.

> The mobile general position number, written Mobgp(G), is the largest number of robots in a mobile general position set of G.

Section 2, page 4:

> Recall that the Cartesian product G □ H of graphs G and H satisfies V(G □ H) = V(G) × V(H) and (g, h)(g′, h′) ∈ E(G □ H) if either gg′ ∈ E(G) and h = h′, or g = g′ and hh′ ∈ E(H).

The formalization uses finite occupied sets, one robot per vertex, and finite
sequences of configurations. The cycle coordinates are Fin r and the path
coordinates are Fin s, starting at zero. On the connected cylinders, the
distance equality through the middle vertex expresses shortest-path membership.

## The cylinder conjecture

Section 3, page 15, after Proposition 3.7:

> Hence, the only unknown values are Mobgp(C₇ □ Pₛ) and Mobgp(C₁₀ □ Pₛ) for s ≥ 5. We conjecture that the answer is four in these cases.

Theorem 3.4 and Lemma 3.5 supply four-robot lower bounds for r ≥ 5 and s ≥ 2.
Proposition 3.7 treats r = 9 and r ≥ 11 at heights s ≥ 5. The formal settlement
proves both remaining values for every s ≥ 5. Its five-robot obstruction works
at every height, and its four-robot traversal works for every s ≥ 2.

The literature screen includes arXiv:2507.16622, arXiv:2501.19385v5,
arXiv:2510.01294v2, arXiv:2604.15909v1 and arXiv:2412.09837v3. No prior
settlement was found in that screen; literature completeness is
ASSUMED-UNVERIFIED. The torus analogues are outside this settlement.

## Infinite integer-lattice question

Section 5, second bullet, asks whether the known static value for the
infinite integer lattice remains the mobile general-position value in higher
dimensions. The source-qualified resolution is recorded in
`Problems/klavzar-et-al-2025-mobile-general-position-integer-lattices.md` and
formalized by
`D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeMobile.result`.

The formal graph has vertex type `Fin k → ℤ` and signed-unit adjacency. Its
general-position predicate is the graph shortest-path predicate, and the
mobile predicate requires one common natural-time trajectory with an actual
LegalMove at every step, general position throughout, and coverage of every
lattice vertex. The result proves the universal bound and an attained witness
of size $2^{2^{k-1}}$ for every $k\ge1$. The witness starts at the fourfold
image of the static configuration; no reachability from the unscaled witness
is included.

The static double-exponential ingredient is attributed to arXiv:2003.12959v2,
Theorem 1, DOI 10.1016/j.amc.2020.125664. The mobile settlement adds the
actual lattice metric/geodesic bridge, a covering walk, serialized one-label
moves, and the finite-configuration bridge. It does not impose a finite box,
a traversal-time bound, simultaneous moves, or independent target-dependent
runs.
