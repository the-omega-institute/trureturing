---
bibkey: onishchik2020kronecker
authors: A. L. Onishchik
year: 2020
title: "Kronecker theorem"
doi: null
url: https://encyclopediaofmath.org/index.php?title=Kronecker_theorem&oldid=47528
claim: "The closure of a subgroup of a finite torus is determined by the integer characters that vanish on its generators; the single-generator case characterizes power-orbit closures."
strata_touched:
  - D5/S3/Fourier/TorusOrbitClosure
license: citation-only
triage: anchor
---

# Integer relations and torus subgroup closures

## Verified locator

https://encyclopediaofmath.org/index.php?title=Kronecker_theorem&oldid=47528

Encyclopedia of Mathematics, "Kronecker theorem", revision 47528, last
edited June 5, 2020. The entry credits A. L. Onishchik as the originator of
the original article. The year above identifies this revision, not the
date of the classical theorem.

The opening theorem gives the simultaneous approximation criterion for
vectors a_i and b in R^n: integer combinations of the a_i approximate b
modulo Z^n exactly when every integer relation integral on all the a_i is
also integral on b. The following paragraph, beginning "Kronecker's
theorem is a special case", states the corresponding characterization
of the closure of the generated subgroup of R^n/Z^n.

The entry attributes the original theorem to Kronecker in 1884 and cites
Bourbaki's General Topology and Pontryagin's Topological Groups for the
group formulation. Those books are bibliographic pointers; no theorem
number or page locator from their bodies is asserted here.

## Correspondence with the formal statement

Take one generator. Under the coordinatewise isomorphism from R/Z to
Circle, x maps to exp(2 pi i x), and the integer character indexed by k
maps a point g to the product of g_i raised to k_i. An additive integer
relation becomes the multiplicative equality of this product with one.
The source's subgroup criterion therefore says that a point z belongs
to the closure of the integer powers of g exactly when it satisfies
every integer character relation satisfied by g.

In a compact group the closures of the integer and nonnegative power
orbits coincide. The formal proof reuses this compact-group closure
identity, so its natural-power formulation includes exponent zero.
An arbitrary finite index type is a reindexing of the finite-dimensional
torus; the empty index type additionally gives the singleton torus and
empty products, both included in the formal statement.

No rational independence, algebraicity or density in the entire torus
is assumed. Torsion generators and proper closed orbit subgroups are
retained. The formal proof uses Haar averaging, density of torus
characters and continuous separation of compact cosets. This proof
construction does not assert originality of the classical criterion.

The note attests the topological characterization only. It supplies no
algorithm for computing a finite relation basis and no algebraic
optimization or semidefinite-programming assertion.
