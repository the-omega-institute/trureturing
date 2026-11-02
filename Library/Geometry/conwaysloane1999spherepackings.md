---
bibkey: conwaysloane1999spherepackings
authors: J. H. Conway and N. J. A. Sloane
year: 1999
title: Sphere Packings, Lattices and Groups
doi: 10.1007/978-1-4757-6568-7
claim: Classical root-lattice and dual-lattice geometry, including the A-type simplex lattice; the local Lean proof establishes its integer minimum-shell formulation.
strata_touched: []
license: citation-only
triage: anchor
---

<!-- GID: D5/L/Geometry/conwaysloane1999spherepackings -->

# A-type dual lattice and simplex energy

The classical dual of the root lattice A_r is the projection of the integer
coordinate lattice onto the hyperplane with coordinate sum zero. For integer
y with r plus one coordinates, the squared norm of that projection is
sum(y_i squared) minus sum(y_i) squared divided by r plus one. Multiplying
by r plus one gives the unordered pair-difference energy. Translation by a
constant integer vector preserves the projected vector and this energy.

The local `SimplexMinimalShell.complete_shell` proves the all-integer minimum
and equality reconstruction directly: the minimum nonzero energy is r,
and equality consists of a signed singleton perturbation of a constant
vector. Setting one coordinate to zero gives the signed coordinate units
and signed all-ones charges. This is classical A-type dual minimum-vector
geometry, with no novelty claim.

The book identity, authors, year and DOI are confirmed by the Crossref record:
https://api.crossref.org/works/10.1007%2F978-1-4757-6568-7 .
The root/dual terminology and book reference are independently displayed at
https://errorcorrectionzoo.org/c/an and
https://errorcorrectionzoo.org/c/an_dual .
Those web entries establish the lattice identification, not a locator for
the complete equality proof. The book's full text was not inspected; the
integer cut-energy proof and its exact quantifiers are supplied by the local
Lean source.
