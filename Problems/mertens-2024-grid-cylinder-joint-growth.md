---
slug: mertens-2024-grid-cylinder-joint-growth
bibkey: mertens2024domination
doi: 10.48550/arXiv.2408.08053
url: https://emis.de/ft/35919
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/Domination/MertensGridGrowth.result
---

# Ordinary grid and cylinder domination growth

## Problem

Stephan Mertens, Journal of Integer Sequences 27 (2024), Article 24.7.6,
after equation (22), p. 19, conjectures equality of the grid and cylinder
growth rates. Equations (15)–(17) use joint m,n tending to infinity.
Ordinary domination on pp. 1–2 counts every selected subset that contains
or neighbors each vertex. At z=1 the domination polynomial is exactly
this finite count, including nonminimal subsets without a symmetry quotient.

The complete event is: there exists a real mu in [1,2] such that for every
positive epsilon there is a natural N>=3 for which every m,n>=N satisfies
both |g(m,n)^(1/(mn))-mu|<epsilon and |c(m,n)^(1/(mn))-mu|<epsilon.
Here g counts ordinary dominating subsets of P_m Cartesian P_n, while c
counts those of C_m Cartesian P_n. There is no bound on either aspect ratio.
`MertensGridGrowth.JointGrowth` is exactly this event and `result` proves it.
Natural dimensions express the source integer domain m>=3,n>=1 without loss.

## Motivation

The grid and cylinder differ only at a seam of 2n boundary vertices.
Equality of their growth constants expresses that this boundary change has
vanishing cost per vertex when both dimensions grow without an aspect-ratio
restriction.

## Gap

The finite comparison alone does not establish that either joint limit
exists. The required existence step is the unrestricted grid limit, followed
by a cylinder estimate uniform in the other dimension.

## Route

The two graph families have the same labelled vertex set. Adding cylinder
seam edges gives g<=c. Filling both endpoint columns repairs every cylinder
subset into a grid subset. Recording the original intersection with those
2n boundary vertices makes this map injective into the grid family times
the boundary powerset, so c<=4^n g. No injectivity of filling alone is used.

For fixed positive a,b, choose floor(M/a)floor(N/b) disjoint translated
blocks. Independent grid-dominating subsets on these blocks, together with
all leftover vertices, dominate the big grid. Restriction recovers each
choice. This proves g(M,N)>=g(a,b)^(floor(M/a)floor(N/b)).

Take the supremum L of normalized logarithmic grid counts. All-vertex
selection and the powerset bound put L in [0,log 2]. The two covered side
proportions tend jointly to one, so the tiling lower bound and supremum
upper bound prove that the grid log rate tends jointly to L. The cylinder
log rate lies between that rate and that rate plus log 4/m, uniformly in n.
Exponentiating gives the exact event with mu=exp L. Neither an iterated
limit nor a preexisting grid-limit assumption is substituted for this argument.

## Falsifier

A counterexample to the complete event would have to exclude every mu in
[1,2]: for each such mu, some positive epsilon would admit arbitrarily
large pairs m,n for which at least one of the two displayed errors is at
least epsilon. Agreement on fixed strips, an iterated limit or a diagonal
sequence alone does not establish the event.

## Evidence

The mathematical source is the final Journal of Integer Sequences 27 (2024),
Article 24.7.6, https://emis.de/ft/35919, p. 19 after equation (22).
Its PDF has SHA-256
9a1c2e36ef5d634a6ebf7a178205b38f10f6663f50848a2d0522173f2ba35d93.
ArXiv v1 places the conjecture on p. 20 and is not byte-identical.
The source definitions on pp. 1–2 identify ordinary labelled dominating
subsets, including nonminimal ones. Equations (15)–(17) specify joint growth.
The declarations `finite_seam_bound`, `tiling_count` and `result` in
`D5/S3/Combinatorics/Graph/Domination/MertensGridGrowth` supply the finite
comparison, tiling estimate and complete joint event, respectively.

## Triage

Theorem: the target is the single proposition
`MertensGridGrowth.JointGrowth`, with ordinary closed domination, the two
specified Cartesian graph products, one common mu and one common cutoff
for both counts. The route includes existence of the unrestricted joint
limit.

## ASSUMED-UNVERIFIED

No worldwide openness or priority claim is made. No numerical value of mu,
grid convergence rate, minimal-domination count, fixed-width substitute or
symmetry-reduced enumeration is asserted.
