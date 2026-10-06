---
bibkey: dembowski1968finitegeometries
authors: Peter Dembowski
year: 1968
title: Finite Geometries
doi: null
url: https://link.springer.com/book/10.1007/978-3-642-85820-6
claim: Chapter I presents the coordinate model of finite affine and projective geometries, including lines over finite fields and their elementary incidence properties.
strata_touched:
  - D5/S3/Geometry/FiniteGeometry/AffinePlaneLines
license: citation-only
triage: anchor
---

# Finite affine planes in coordinates

## Verified source

Peter Dembowski, *Finite Geometries*, Springer-Verlag, 1968, Chapter I.
The chapter develops the standard coordinate construction over a finite field:
nonvertical lines are graphs of affine functions and vertical lines form the
remaining parallel class.

Hirschfeld, *Projective Geometries over Finite Fields*, 2nd ed., §1.1, gives a
parallel coordinate presentation and is a secondary locator for the same
elementary incidence facts.

## Relation to the Lean module

The repository module fixes the concrete coordinate model
`y = m * x + b` and `x = c`. Its `Option F` equivalence counts the lines
through a point, while the two-point theorem proves the standard uniqueness
property by field algebra. The source is cited for the classical geometric
model; the Lean file supplies the machine-checked coordinate proof.
