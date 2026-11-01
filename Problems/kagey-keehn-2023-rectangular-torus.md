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

The mathematical task is to pass from transposing symmetry of the decorated periodic plane to a genuine gcd-square quotient with identical plane labels. The theorem `rectangular_torus_gcd_descent` supplies the quotient for every source instance in Problem, using the operational source-to-constructor correspondence in Route.

## Route

For a source translation representative u and center c, the decorated graph map is `(z,d) -> (A_h(z+u)+c, d·h)`. Graph fixedness and uniqueness of the design at each target cell give `F(A_h(z+u)+c) = F(z)·h`; conversely, this covariance and bijectivity of the affine cell map give graph equality. Instantiate the Lean theorem with the constructor mapping `r -> .r3`, `r^3 -> .r`, `rf -> .rf`, `r^3f -> .r3f`, `shift = u`, `center = c`, and `rho(d) = d·h`.

The literal lift gives periods `(n,0)` and `(0,m)`. Affine covariance transports each period through the signed-swap map, yielding both coordinate periods n and m. Integer Bézout combinations yield `(g,0)` and `(0,g)` for `g = gcd(n,m)`, and positivity of n,m yields `g > 0`. Defining `H([x]g,[y]g)=F(x,y)` is representative-independent because differences are in the period subgroup, and its plane lift is exactly F. If u is changed by a rectangular period, the same covariance at the shifted point gives the same source action. No label relabeling or abstract-period-only replacement is used.

## Falsifier

A source instance whose graph is fixed under operational `r` but fails covariance under the internal `.r3` substitution would falsify the exposition. For q=3, take `T = (Z/3Z)^2`, `d·r = (2-d_y,d_x)`, `d·f = (2-d_x,d_y)`, and `F(x,y)=([x]3,[y]3)`. With source r, shift zero and center `(2,0)`, the operational covariance is obtained from `.r3`; assigning the same-named internal `.r` gives the wrong design at `(1,0)`. The example distinguishes source action names from internal constructor names.

## Evidence

The canonical source is `D5/S3/Combinatorics/TorusTilings/KageyKeehnRectangularTorus.lean`, and its owning Scribe is `Blueprint/D5/S3/Combinatorics/TorusTilings/KageyKeehnRectangularTorus.scribe.cs`; the generated Blueprint is the projection of that Scribe. The public theorem is `rectangular_torus_gcd_descent`. Compiled evidence is the module's scoped Lean report, `.lake/build/stratalint/scoped-lean-report.json`, with its source-input provenance. The Scribe supplies the source-action interpretation, which is a semantic correspondence distinct from kernel checking. The source note is `Library/FiniteGeometry/kagey2023rectangulartorus.md`.

The original Section 5.1, page 23, and [journal Section 6.1, page 30](https://cs.uwaterloo.ca/journals/JIS/VOL27/Kagey/kagey6.pdf) place the conjecture immediately before the question of counting irreducible plane tilings, defined there as plane tilings that do not correspond to a smaller torus. Figure 11 illustrates a 6 x 4 presentation with a 2 x 2 presentation of the same plane.

## Triage

The theorem-level admission basis for the external named question is `admission_basis: open-problem-resolution (#23394; Proved)`, with `utility: none` and `proof_shape: bind-only`. The theorem directly applies the period-subgroup construction in the compiled source. The public escape audit remains unfinished under issue [#23394](https://github.com/the-omega-institute/trureturing/issues/23394); no `declared_validated` registration is claimed.

### What the settlement shows

**Kernel-checked endpoint and generality (proved).** Signed-swap covariance transports both source periods onto both coordinate axes, yielding a genuine gcd-square H with the same T and an identical decorated plane lift for every positive n,m. Unit, equal, unequal and nonprimitive dimensions and all four maps are included. The compiled theorem permits an arbitrary `rho : T -> T`, without an invertibility assumption, and arbitrary integral `shift` and `center`; the affine offset cancels in period transport. In an actual source instance, `rho(d) = d·h` uses that same h, with the constructor correspondence in Route. This is the theorem's existing range.

**Reducibility consequence (elementary, not a separate kernel-checked theorem).** For positive n,m with n != m, g = gcd(n,m) divides both dimensions, g <= min(n,m), and g^2 < nm. Thus every transposing-symmetric rectangular presentation covered by the source conjecture has a strictly smaller g x g presentation of the identical decorated plane. Relative to the given unequal n x m presentation, it is reducible in the source's sense of admitting a smaller torus. This gives a sufficient reducibility test for that symmetry class; the smaller presentation represents the same plane, rather than an additional plane to count.

**Minimality and counting (unresolved by this result).** The gcd square need not be minimal, and for n = m the conclusion can retain the original size. The theorem neither characterizes all minimal rectangular presentations nor enumerates inequivalent irreducible plane tilings for a design set. Absence of a transposing symmetry does not establish irreducibility. The source's adjacent irreducible-counting question therefore remains unsettled here: smaller periods and equivalences between presentations still require analysis.

**Source dependency impact (source-checked).** In both versions, the conjecture belongs to the final research questions, after the proved torus enumeration formulas. No later theorem in either source is stated or proved by assuming this conjecture; the later mathematical material consists of further questions and the enumeration and illustration appendices. The result settles this rectangular-to-square existence question and constrains its adjacent irreducibility question as above. It supplies no new enumeration formula, no D8 action on an unequal finite rectangle, and no worldwide literature-priority conclusion.

## ASSUMED-UNVERIFIED

External-source completeness and priority remain bounded and fallible. D5, private declarations, pinned Mathlib, and bounded external Lean-source queries were checked after the proof; the full supplier-first search order was not established. No exact whole supplier was found in that bounded scope, and no worldwide absence is claimed. A relevant Nivat affine-period helper is source-only, uses differing pins, and is not an adopted dependency. The public escape audit remains unfinished: dependent `SourceParams`/output transport and universe alignment, faithful realization/equivalence/readout, lawful enrollment, source selection, continuation, and current binding evidence are missing under issue #23394.
