---
slug: kagey-keehn-2023-rectangular-torus
bibkey: kagey2023rectangulartorus
doi: null
url: https://arxiv.org/abs/2311.13072v1
triage: theorem
motivation_gids:
  - D5/S3/Fourier/CharacterSelection/PeriodicGridCoverLift
  - D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy
---

# Rectangular-torus rotation descent

## Problem

Peter Kagey and William Keehn, *Counting tilings of the n x m grid, cylinder, and torus*, arXiv:2311.13072v1, Section 5.1, Conjecture 5.1.1 (the journal alias is JIS 27 (2024), 24.6.1, Section 6.1, Conjecture 42), ask whether a plane tiling represented by an n x m torus and fixed by a translated right action `r`, `r^3`, `rf`, or `r^3f` is equivalent to a gcd(n,m) x gcd(n,m) torus tiling.

The complete reading quantifies over every positive n,m, every applicable subgroup R <= D8, every actual right R-set T of decorated tile designs, every `f : ZMod n -> ZMod m -> T` with literal periodic lift `F : Z x Z -> T`, every h in `{r,r^3,rf,r^3f}` belonging to R, every allowed translation representative u before h, and every integral affine center. It asks for a genuine H on the full product `ZMod gcd(n,m) x ZMod gcd(n,m)` whose literal plane lift is pointwise identical to F. Equal and unequal dimensions, unit dimensions, nonprimitive periods, all quotient representatives, and nontrivial design actions are included. No minimality claim and no D8 action on an unequal finite rectangle is part of the problem.

The operational source maps are `r : (x,y) -> (-y,x)`, `r^3 : (x,y) -> (y,-x)`, `rf : (x,y) -> (y,x)`, and `r^3f : (x,y) -> (-y,-x)`, with labels `d -> d·h`. The source's inverse conjugation coordinate map is kept distinct from these operational maps.

## Motivation

The source models a finite torus as a repeating decorated plane. Periodicity is therefore a property of the actual lift, and a gcd-square presentation is useful only when it preserves the same design set and every plane label. The frozen periodic-grid cover and holonomy results listed in `motivation_gids` provide the repository's relevant periodic-lift context; they do not settle this source question.

## Gap

The compiled theorem already contains the complete period-transport and gcd descent. The reviewed gap was the source-to-constructor binding: the source label `r` uses the internal constructor `.r3`, while source `r^3` uses `.r`. The admission header also lacked the required explicit utility declaration, and this dossier did not use the canonical problem-candidate schema.

## Route

For a source translation representative u and center c, the decorated graph map is `(z,d) -> (A_h(z+u)+c, d·h)`. Graph fixedness and uniqueness of the design at each target cell give `F(A_h(z+u)+c) = F(z)·h`; conversely, this covariance and bijectivity of the affine cell map give graph equality. Instantiate the Lean theorem with the constructor mapping `r -> .r3`, `r^3 -> .r`, `rf -> .rf`, `r^3f -> .r3f`, `shift = u`, `center = c`, and `rho(d) = d·h`.

The literal lift gives periods `(n,0)` and `(0,m)`. Affine covariance transports each period through the signed-swap map, yielding both coordinate periods n and m. Integer Bézout combinations yield `(g,0)` and `(0,g)` for `g = gcd(n,m)`, and positivity of n,m yields `g > 0`. Defining `H([x]g,[y]g)=F(x,y)` is representative-independent because differences are in the period subgroup, and its plane lift is exactly F. If u is changed by a rectangular period, the same covariance at the shifted point gives the same source action. No label relabeling or abstract-period-only replacement is used.

## Falsifier

A source instance whose graph is fixed under operational `r` but fails covariance under the internal `.r3` substitution would falsify the exposition. For q=3, take `T = (Z/3Z)^2`, `d·r = (2-d_y,d_x)`, `d·f = (2-d_x,d_y)`, and `F(x,y)=([x]3,[y]3)`. With source r, shift zero and center `(2,0)`, the operational covariance is obtained from `.r3`; assigning the same-named internal `.r` gives the wrong design at `(1,0)`. This distinguishes the labels while leaving the compiled theorem's four maps intact.

## Evidence

The canonical source is `D5/S3/Combinatorics/KageyKeehnRectangularTorus.lean`, and its owning Scribe is `Blueprint/D5/S3/Combinatorics/KageyKeehnRectangularTorus.scribe.cs`; the generated Blueprint is the projection of that Scribe. The public theorem is `rectangular_torus_gcd_descent`, with the original theorem type and proof terms unchanged by this repair. The source note is `Library/FiniteGeometry/kagey2023rectangulartorus.md`. Current scoped evidence is renewed after the content changes; it is scoped to this module and its Scribe inputs.

## Triage

The external named question is admitted as a theorem-level open-problem resolution. The finite batch records `utility: none`, `proof_shape: bind-only`, and `admission_basis: open-problem-resolution (#23394; Proved)`. The theorem is a direct application of the period-subgroup construction already present in the compiled source; no wrapper theorem, stronger claim, or weakened source statement is introduced. The unfinished escape audit is disclosed under issue [#23394](https://github.com/the-omega-institute/trureturing/issues/23394); no `declared_validated` registration is claimed.

### What the settlement shows

The signed-swap covariance forces both source periods onto both coordinate axes, so the gcd periods exist for every positive n,m. The resulting H uses the same T and has an identical decorated plane lift. The argument covers unit, equal, unequal and nonprimitive dimensions and all four source actions. It does not assert a minimal square, a new action on an unequal finite rectangle, or a worldwide literature-priority result.

## ASSUMED-UNVERIFIED

The source-to-Lean mapping is now stated explicitly, but external source completeness and priority remain bounded and fallible. D5, private declarations, pinned Mathlib, and bounded external Lean-source queries were checked after the proof; the full supplier-first search order was not established. No exact whole supplier was found in that bounded scope, and no worldwide absence is claimed. A relevant Nivat affine-period helper is source-only, uses differing pins, and is not an adopted dependency. The public escape audit remains unfinished: dependent `SourceParams`/output transport and universe alignment, faithful realization/equivalence/readout, lawful enrollment, source selection, continuation, and current binding evidence are missing under issue #23394.
