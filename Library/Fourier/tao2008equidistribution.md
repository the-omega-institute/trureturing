---
bibkey: tao2008equidistribution
authors: Terence Tao
year: 2008
title: "The van der Corput trick, and equidistribution on nilmanifolds"
doi: null
url: https://terrytao.wordpress.com/2008/06/14/the-van-der-corputs-trick-and-equidistribution-on-nilmanifolds/
claim: "The Weyl character criterion and geometric-series argument give Haar equidistribution of linear torus orbits; restriction to the actual closed cyclic subgroup retains integer relations and torsion."
strata_touched:
  - D5/S3/Fourier/Asymptotics/TorusOrbitEquidistribution
license: citation-only
triage: anchor
---

# Character averages on the actual orbit closure

## Verified locator

https://terrytao.wordpress.com/2008/06/14/the-van-der-corputs-trick-and-equidistribution-on-nilmanifolds/

Tao's author-hosted exposition, June 14, 2008, section "The classical van der
Corput trick", equations (1) and (2), states equidistribution for every
continuous function and its equivalence to cancellation of every nontrivial
character. Corollary 1, "Equidistribution of linear sequences in torii", applies
the geometric-series formula and requires total irrationality for the full
ambient torus. The following example explicitly distinguishes an orbit
confined to the kernel of a character and states equidistribution in that
smaller torus. These paragraphs were retrieved and read on September 26, 2026.

The full orbit-closure statement used here is the classical compact-group
rotation consequence of this character argument. The cited Corollary 1 does
not itself state the arbitrary disconnected-subgroup version. Its total
irrationality assumption is not an assumption of the formal theorem.

For the distinction between every-point convergence and almost-everywhere
ergodic convergence, the same author's "254A, Lecture 9: Ergodicity",
February 4, 2008, equation (15), the definition of a generic point, and
Exercise 10 give continuous-observable equidistribution and the equivalence
between unique ergodicity and uniqueness of an invariant Borel probability
measure. Exercise 11 concerns irrational circle rotations. These passages
were also retrieved and read; they are conceptual references, not claims
that the full subgroup statement occurs there verbatim.

https://terrytao.wordpress.com/2008/02/04/254a-lecture-9-ergodicity/

## Precise mathematical mapping

For a finite index type I and g in the multiplicative torus Circle^I, put
G = closure of the integer powers of g. Compactness identifies this with the
closure of the nonnegative powers. The measure is Haar measure on the subtype
G, normalized by its total compact set, not Haar measure on the ambient torus.

An ambient integer character restricts to a continuous character of G. If its
value at g is one, continuity makes the restriction identically one. Otherwise
its averages along g, ..., g^N tend to zero by the geometric-series estimate,
and translation invariance makes its Haar integral zero. Thus integer
relations are retained, including nonzero characters trivial on G.

Complex Tietze extension gives an ambient continuous extension of every
continuous function on G. Restriction therefore maps the dense multivariate
Fourier span onto a dense subspace of C(G, C). Uniformly bounded averaging
operators and continuity of Haar integration extend the character conclusion
to every continuous observable. Empty products, finite-order generators,
proper subgroups and disconnected orbit closures require no exclusions.

The Lean proof implements this classical argument using pinned Mathlib's
Tietze, Fourier-density, geometric-sum and Haar-invariance results. It makes
no mathematical novelty claim. The source's later nilmanifold discussion
carries a February 2013 correction and is not used. No numbered statement is
attributed to an unread Weyl or Oxtoby article.
