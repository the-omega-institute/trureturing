---
slug: klavzar-et-al-2025-mobile-general-position-integer-lattices
bibkey: klavzaretal2026mobileproducts
doi: 10.1016/j.dam.2025.10.041
url: https://arxiv.org/abs/2505.00535
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeMobile.result
---

# Mobile general position on integer lattices

## Problem

Klavžar, Krishnakumar, Kuziak, Shallcross, Tuite and Yero, “Moving through
Cartesian products, coronas and joins in general position”, arXiv:2505.00535v2,
Discrete Applied Mathematics 379 (2026), 768–780,
DOI 10.1016/j.dam.2025.10.041, Section 5, second bullet, asks whether the
known static value is also the mobile general-position value in higher-
dimensional infinite integer grids. The settled statement is

\[
  \operatorname{Mob}_{gp}(\mathbb Z^k)=2^{2^{k-1}}
\]

for every integer $k\ge1$, with the mobile definition requiring one common
sequence of legal one-robot moves that visits every lattice vertex.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Vertices of the integer lattice | `IntegerLatticeMotion.Vertex k = Fin k → ℤ` | The graph has every integer lattice vertex; no finite box is imposed. |
| Signed-unit adjacency | `IntegerLatticeMotion.lattice k` | Exactly one coordinate changes by $+1$ or $-1$. |
| Shortest-path general position | `CylinderSevenTen.IsGeneralPosition (lattice k)` | All ordered triples of pairwise distinct occupied vertices are excluded from a shortest graph path. |
| One common mobile trajectory | `IntegerLatticeMobile.IsMobile` | A single `c : ℕ → Finset (Vertex k)` precedes all time and coverage quantifiers. |
| Exact mobile value | `IntegerLatticeMobile.result` | Every finite mobile set satisfies the upper bound and an actual finite mobile witness attains it. |

The theorem includes the empty configuration in the universal upper-bound
domain. It assumes no cardinality invariant, finite region, bounded duration,
simultaneous moves, or independent run for each target vertex. The attaining
configuration is the fourfold coordinate image of the static witness, so the
trajectory starts at $4T$; reachability from the unscaled witness $T$ is not
claimed.

## Motivation

The source records the static double-exponential value and asks whether
mobility changes it in dimensions beyond the previously treated cases. The
formal result answers that question uniformly for every positive dimension.
The upper bound is inherited from the static general-position bound after
identifying coordinate betweenness with the actual lattice geodesic relation.
The lower bound uses a recursive static witness, a covering walk on the
signed-unit lattice, and a fourfold separation that permits a serialized
one-label translation while preserving general position.

## Gap

The cited Section 5 bullet is the external open-problem source for this
resolution. The static ingredient is attributed to arXiv:2003.12959v2,
Theorem 1, DOI 10.1016/j.amc.2020.125664; it supplies the known static
double-exponential extremum used by the construction. That known ingredient is
not counted as a second open-problem resolution here.

## Route

The source modules are:

* `D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeStatic.lean`,
  which proves the uniform static upper bound and constructs the exact witness;
* `D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeMotion.lean`,
  which proves the lattice metric/geodesic correspondence, the covering walk,
  and the serialized trace; and
* `D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeFiniteMotion.lean`,
  which converts the trace into one finite-set LegalMove trajectory.

`IntegerLatticeMobile.result` combines these live consumers. Its first branch
applies the static upper bound to the initial graph-general-position clause;
its second branch applies the finite-motion bridge to the scaled static
witness. `IsMobile` contains exactly the initial general-position clause, one
common trajectory, legal moves, general position at every time, and coverage.

## Falsifier

A finite mobile configuration larger than $2^{2^{k-1}}$ in any positive
dimension, or failure of the exhibited fourfold trajectory to satisfy the
actual graph LegalMove and coverage clauses, would contradict the result.
The theorem does not assert a finite traversal bound or reachability from the
unscaled static witness.

## Evidence

`D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeMobile.result` is the
single public result theorem. The selected Lean report has axiom closure
contained in {`propext`, `Classical.choice`, `Quot.sound`} and no `sorry`
or new axiom. The corresponding Scribe renders the complete `IsMobile`
definition and the conjunction of the universal bound and attained witness.

The retained component declarations are live consumers of the result path:
`IntegerLatticeStatic.card_le`, `IntegerLatticeStatic.exists_attaining`,
`IntegerLatticeMotion.between_iff_geodesic`,
`IntegerLatticeMotion.scaled_finset_trace`, and
`IntegerLatticeFiniteMotion.scaled_finset_mobile`. The public Cylinder helpers
`configuration_card`, `labelled_gp`, and `labelled_move` are the original
proofs with only `private` removed so the finite bridge can call them.

## Triage

### What the settlement shows

- **Upper bound — kernel-checked.** Initial general position is converted from
  graph geodesic betweenness to coordinate betweenness and fed to the static
  bound, with no nonempty premise.
- **Attainment — kernel-checked.** The recursive static witness is scaled by
  four. The covering walk and serialized labels give one common infinite
  trajectory; each step changes one occupied vertex along an actual signed-unit
  edge into a vacant vertex, and every intermediate set remains in graph
  general position.
- **Exact scope — kernel-checked.** The public result quantifies all natural
  dimensions with `1 ≤ k`, uses finite configurations of the full infinite
  lattice, and asserts both the upper bound and an exact-cardinality witness.
- **Known ingredient — literature attribution.** The static extremum is the
  cited Theorem 1 of arXiv:2003.12959v2 and is used as a proved repository
  component, not as a literature axiom.

The selected source registration records three validated audits
(`IntegerLatticeStatic.card_le`, `IntegerLatticeStatic.exists_attaining`, and
`IntegerLatticeMotion.lattice_distance`) and two unresolved Prop-valued
observation readouts (`IntegerLatticeMotion.between_iff_geodesic` and
`IntegerLatticeMotion.scaled_finset_trace`) under the linked issue exception.
The final result and finite-motion mirrors are disclosed with the same exact
missing-evidence boundary if the current template cannot lawfully realize
their source observations.

## ASSUMED-UNVERIFIED

The literature locator is bounded and does not establish an exhaustive
priority search. The cited static source attribution records the known
ingredient only. No finite-time bound, physical realization, or result beyond
the stated infinite-lattice mobile equality is asserted.
