---
slug: dabrowski-poulain-ragoucy-2026-switched-ssep-reachability
bibkey: dabrowski2026twistedssep
doi: 10.1088/1751-8121/ae751a
url: https://arxiv.org/html/2602.18204v2
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.result
---

# Dabrowski–Poulain d’Andecy–Ragoucy: full support under switched twisted SSEP

## Problem

Mathieu Dabrowski, Loïc Poulain d’Andecy and Eric Ragoucy,
“Twisted symmetric exclusion processes and set-theoretical R-matrices”,
*Journal of Physics A: Mathematical and Theoretical* **59**, 245203,
arXiv:2602.18204v2, Section 7, “Outlook”, asks:

> On the mathematical side, given two twisted SSEP, what are the conditions on the permutations defining the twists in order to have a non-zero probability of occupying any configuration after a certain number of switch between the twists of both models?

The same question is quoted verbatim in
[preregistration #30601](https://github.com/the-omega-institute/trureturing/issues/30601).
Its registered statement is:

> Let X = ⟦0,N−1⟧ (N ≥ 1), f, g ∈ Sym(X), H = ⟨f, g⟩ and D = [H, H]. The two models' sectors are the connected components of their configuration graphs (moves: the L−1 adjacent swaps and the twisted boundary move for f, respectively g). Starting from any sector of either model, alternating equilibrated switches give every configuration positive probability after finitely many switches **if and only if** the union of the two configuration graphs is connected, and:
>
> - for L ≥ 3: if and only if D acts transitively on X;
> - for L = 2: if and only if |K| = N² · |K ∩ (H_a × H_a)| for some (equivalently every) a ∈ X, where K = ⟨(f, f⁻¹), (g, g⁻¹)⟩ ≤ H × H and H_a is the stabilizer of a.

The preregistration also requires:

> The Lean statement must model the configurations, both move sets, the sectors and the Proposition 5.2 switching dynamics (at least its support), and state the equivalence for every N ≥ 1, L ≥ 2 and every f, g.

Here a configuration assigns a species in X to each site of a periodic ring.
The ordinary moves exchange adjacent sites. For a twist s, the boundary move
sends the ordered entries at (last, first) to (s(first), s⁻¹(last)), as in
Section 3.1, equations (3.1)–(3.3). A sector is the equivalence class generated
by these involutive moves. Switching has the meaning of Section 5.1: the
initial distribution is uniform on a sector, and each next model evolves to
its sector-uniform equilibrium. Proposition 5.2 assigns the next-sector
weight |C ∩ D|/|C|.

## Motivation

The source's switching examples exhibit oscillations between different sector
structures. The full-support question asks when alternating two such
structures removes every obstruction to reaching a configuration. A criterion
on f and g distinguishes obstructions in species space from restrictions
imposed by the number of sites.

## Gap

Tier 1; #30601 registers the Section 7 question for all positive N and all
L ≥ 2. Proposition 5.2 supplies the sector intersection kernel, but the
question asks for a necessary and sufficient condition on arbitrary twists.
The classifications below are repository-derived and are not attributed to
the paper. The preregistration's bounded enumeration is not the proof of this
uniform result. Global literature openness is ASSUMED-UNVERIFIED: #30601
records a limited citation search and an unreadable MathDB query; that search
does not certify the absence of another resolution.

## Route

The Lean carrier is `Configuration L N := Fin L → Fin N`. `sector` uses
`Relation.EqvGen` of the elementary move relation. `branchingProbability` is
the rational intersection-cardinality ratio, and positivity is proved
equivalent to `overlap`, since the initial representative belongs to its
sector. `alternatingSectorReach` iterates overlapping sectors of alternating
models; `switchSupport` is their union. The independently recursive
`alternatingSupport` is proved equal to it for every finite initial set C and
every step count, including sets that are not sectors.

The support is monotone in the switch count. Every union-graph move can be absorbed in
at most two successive alternating sector expansions, and every supported
configuration remains in the initial union component. Induction on paths and
switches therefore proves that full switching reachability is equivalent to
union connectivity.

For L ≥ 3, adjacent transpositions generate every site permutation
(`siteReachGroup_eq_top`). Combining the boundary move with the endpoint
transposition yields a coordinatewise paired twist; conjugation places it at
any two distinct sites. Let H = ⟨f,g⟩ and
K = ⟨(f,f⁻¹),(g,g⁻¹)⟩. The first projection of K is H. Thus arbitrary a,b ∈ H
lift to elements of K acting on coordinate pairs (i,j) and (i,k), where i,j,k
are distinct. Their commutator acts by [a,b] at i and trivially elsewhere.
`Subgroup.commutator_le` then supplies every element of D = [H,H] at each
coordinate (`derived_singleCoordinate_mem`). Transitivity of D lets the
proof update the coordinates one at a time and connect any two
configurations (`unionConnected_of_derived_transitive`). This uses arbitrary
commutators through projection lifts; it does not require a separate theorem
identifying D with the normal closure of the single commutator [f,g].

For necessity, connectivity first forces H to be transitive: entries starting
in the H-orbit of one species remain in that orbit. Fix a species a and take
P = D ∨ Hₐ inside H, the subgroup join of the commutator subgroup and the
stabilizer. Containing D makes P normal with abelian quotient H/P. Define the
species charge χ(h·a) = hP. It is well defined because Hₐ ≤ P, and
χ(s·b) = sP·χ(b). The product ∏ᵢ χ(xᵢ) is invariant under adjacent exchanges
and the boundary move, whose two charge factors cancel
(`charge_product_move`). A path from the constant a configuration to one
with a single entry changed to b forces χ(b) = 1. Writing its representative
in P as a derived element times a stabilizer element gives d·a = b for some
d ∈ D (`derived_transitive_of_unionConnected`). Equivalently, when H is
transitive but D is not, this abelian species charge obstructs full support.

For L = 2, `twoSiteEquiv` reads a configuration as (last, first). The site flip
normalizes K, sends each paired generator to its inverse, and fixes (a,a).
A diagonal configuration's union component is therefore its K-orbit.
Orbit–stabilizer, the explicit `pairStabilizerEquiv`, and Mathlib's
pretransitivity characterization turn full K-orbit size into
|K| = N²·|K ∩ (Hₐ × Hₐ)|. Lean states this for every a; for N ≥ 1 one such
a already suffices, since its full orbit makes K transitive.

## Falsifier

For some positive N, L ≥ 2 and twists f,g, a disagreement between full
alternating equilibrium support and union connectivity would refute the
switching bridge. At L ≥ 3, a connected union with intransitive D, or
transitive D with a disconnected union, would refute the derived-group
criterion. At L = 2, a disagreement between union connectivity and the stated
K-stabilizer cardinality equality would refute the two-site criterion. A
boundary exchange with the opposite convention, or a switch that does not
use the sector-equilibrium model, would fail the source correspondence.

## Evidence

`D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.result` is the settling declaration.
Its exact Lean statement is:

```lean
theorem result {L N : ℕ} (hL : 1 < L) (f g : Equiv.Perm (Fin N)) :
    registeredReachabilityAnswer hL f g ∧
    ((3 ≤ L → (unionConnected hL f g ↔ lAtLeastThreeCriterion f g)) ∧
      (L = 2 → (unionConnected hL f g ↔ lTwoCriterion f g))) ∧
    (∀ (s t : Equiv.Perm (Fin N)) (x y : Configuration L N),
      overlap hL s t x y ↔ 0 < branchingProbability hL s t x y) ∧
    (∀ (start : Bool) (C : Finset (Configuration L N)) (k : ℕ),
      alternatingSupport hL f g start C k = switchSupport hL f g start C k)
```

`registeredReachabilityAnswer hL f g` means

```lean
fullSwitchingReachability hL f g ↔
  (unionConnected hL f g ∧
    (if 3 ≤ L then lAtLeastThreeCriterion f g else lTwoCriterion f g))
```

`lAtLeastThreeCriterion f g` is
`MulAction.IsPretransitive (derivedTwistGroup f g) (Fin N)`.
`lTwoCriterion f g` requires, for every `a : Fin N`,

```lean
Nat.card (pairTwistGroup f g) =
  N ^ 2 * Nat.card
    ↥(pairTwistGroup f g ⊓ pointPairStabilizer (twistGroup f g) a)
```

`fullSwitchingReachability` quantifies over both starting models, every
initial sector representative and every target configuration, with an
existential natural switch count for each target. It does not specify an
optimal count. For a fixed finite system, starting model and sector,
monotonicity of support permits taking the maximum of finitely many target
counts to obtain one common full-support count; this finite-maximum
consequence is not a separate conjunct of `result`.

The scoped Lean report matches the current Lean source hash and records the
settling theorem's axiom closure as {propext, Classical.choice, Quot.sound},
with type fingerprint `sha256:a2343f321f9528c51ef6c349ea9ffbbe1032ff67e4814c6b672b058134def921`. The module imports pinned
Mathlib only and contains no `sorry`, new axiom or `native_decide`.

## Triage

`theorem`. The admission basis is `open-problem-resolution (#30601; Proved)`.
The source classifies every declaration, including `result`, as
`proof_shape: bind-only`, using pinned Mathlib and consumed helpers. The
external-question settlement supplies the admission basis; the dossier does
not reclassify these applications as new foundational group theory.

### What the settlement shows

- [proved: D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.result]
  For every positive N, every L ≥ 2 and every pair f,g, full alternating
  equilibrated-switch support from any sector of either model is equivalent
  to union connectivity and to the applicable permutation-group criterion.
  The formal quantifiers are targetwise ∀target ∃k; the common-count reading
  follows for each fixed finite system by the finite-maximum argument above.
- [proved: D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.result]
  For L ≥ 3, the criterion is transitivity of the derived subgroup D of
  H = ⟨f,g⟩. The sufficient mechanism is independent single-coordinate
  derived-group action obtained from commutators of paired lifts. The
  necessary mechanism is the H-orbit restriction followed, for transitive H,
  by the invariant abelian species charge in H/(D ∨ Hₐ). These mechanisms are
  implemented by the private helpers consumed by `result`.
- [proved: D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.result]
  For L = 2, the exact criterion is
  |K| = N²·|K ∩ (Hₐ × Hₐ)| for every a, with
  K = ⟨(f,f⁻¹),(g,g⁻¹)⟩. For positive N the equivalent one-a formulation
  follows from the full diagonal orbit. The two-site proof uses the flip
  symmetry and orbit–stabilizer, not the three-distinct-sites construction.
- [proved: D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.result]
  The statement includes the source kernel's strict-positivity equivalence
  and equality of the two alternating-support constructions for every finite
  initial C and k. It extends the preregistered positive-N domain to N = 0,
  where the configuration space is empty and the reachability and action
  conditions are vacuous; L = 0 and L = 1 are excluded.
- [open] Quantitative bounds or optimal values for the full-support switch
  count, individual transition probabilities after repeated switches, and
  finite-time relaxation or mixing rates are not determined by `result`.
- [open] Switching before sector equilibrium, unstable-field dynamics, more
  general set-theoretical Yang–Baxter models, integrable open boundaries and
  asymmetric deformations mentioned in Section 7 are outside this
  settlement.
- [open] Global priority and absence of an independent resolution beyond the
  preregistration's cited search scope are unverified.

## ASSUMED-UNVERIFIED

- Global literature openness and priority: #30601's search does not exclude
  later or unindexed resolutions, and no independent exhaustive literature
  search is certified by this dossier.
