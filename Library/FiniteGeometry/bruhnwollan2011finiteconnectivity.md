---
bibkey: bruhnwollan2011finiteconnectivity
authors: Henning Bruhn; Paul Wollan
year: 2011
title: Finite connectivity in infinite matroids
doi: null
url: https://arxiv.org/abs/1101.5621v1
claim: Tutte linking preserves the minimum separating-cut connectivity in a contraction/deletion minor on exactly the terminals of a finite matroid.
strata_touched:
  - D5/S3/Combinatorics/Matroids/TutteLinking
license: citation-only
triage: anchor
---

# Finite Tutte linking

The primary source is Henning Bruhn and Paul Wollan,
*Finite connectivity in infinite matroids*, arXiv:1101.5621v1.
Page 1 defines the finite connectivity function by
r(X) + r(E minus X) - r(M). Page 2 defines the connectivity between
fixed disjoint sets X and Y as the minimum over X contained in U contained
in E minus Y. Theorem 1 on page 2 states that a finite matroid admits a
partition (C,D) of E minus (X union Y) for which the contraction/deletion
minor M/C-D preserves this minimum.

The native Lean theorem `TutteLinking.tutte_linking` has an arbitrary universe,
a finite ambient type, an arbitrary native matroid, and disjoint ground-contained
terminal sets. It supplies C, defines D as the remaining nonterminals, proves
that the actual minor has ground exactly the union of the terminals, and
identifies its terminal rank defect with the original cut infimum. All ranks
are finite extended ranks converted to natural numbers. Empty terminals,
empty ground, loops, coloops and rank zero remain in scope.

Theorem 1 attributes the result to W. T. Tutte. The original bibliographic
source is *Menger's theorem for matroids*, Journal of Research of the National
Bureau of Standards, Section B, 69B (1965), page 49,
DOI [10.6028/jres.069B.002](https://doi.org/10.6028/jres.069B.002).
The original full text gives the one-element deletion-or-contraction
preservation alternative in Section 3.7 on page 52 and the finite induction
in Section 4 on pages 52–53. It is available from
https://nvlpubs.nist.gov/nistpubs/jres/69B/jresv69Bn1-2p49_A1b.pdf.
Tutte's rank convention is defined by circuit-hitting dendroids in his
companion *Lectures on Matroids*; its connectivity formula carries an
additional one. Bruhn and Wollan's Theorem 1 supplies the directly matching
modern rank and cut convention used here. The source texts are cited,
not redistributed.

The proof reuses the repository's finite native matroid intersection theorem
and native contraction, deletion, closure and rank identities. No external
Lean source is transplanted into this module. This is a formalization of a
classical general theorem, with no originality claim.
