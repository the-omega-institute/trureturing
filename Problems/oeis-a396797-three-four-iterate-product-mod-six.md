---
slug: oeis-a396797-three-four-iterate-product-mod-six
bibkey: hanna2026a396797
doi: null
url: https://oeis.org/A396797
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/ThreeFourIterateProductModSix
---

# Coefficients of the A396797 three-four iterate product series modulo six

## Problem

OEIS A396797, Paul D. Hanna, Jun 15 2026. The following NAME and COMMENT
quotes are supplied by the orchestrator and recorded in
`Library/Arith/hanna2026a396797.md`:

NAME:

> G.f. satisfies A(x) = x + A^3(x)*A^4(x).

Here `A^n(x)` denotes the n-th compositional iteration, not an ordinary power.

COMMENT:

> Conjecture: a(n) = 1 (mod 6) for n >= 1.

### 范围与诚实边界

The resolution concerns the first conjecture for every positive index of the
unique zero-constant integer formal power series satisfying the NAME equation.
The second comment, asserting `[x^n] A^k(x) ≡ k^(n−1) (mod 6)` for all k,
is not resolved here. Existence and uniqueness identify the constructed series
with the defining equation; no coefficient congruence is assumed.

## Motivation

This is a first-tier recent OEIS conjecture, selected in the lane brief under
the recent-small-conjecture route. KPI = open problems resolved. The target is
the universal positive-index assertion, not a bounded numerical check.

## Gap

The supplied search-seat report found no proof in its searched scope: the OEIS
entry and revision history were read on 2026-09-08, and identifier searches were
made on arXiv, MathOverflow, and GitHub. This Stage-B seat had no network access
and did not repeat those searches. This is not an exhaustive literature search
or a first-publication priority claim.

## Route

Stabilized successive approximations construct the integer coefficient sequence
`a` and `generatingSeries`; `generating_equation` proves its zero constant term
and defining functional equation. Degree induction gives `generating_unique`.
The private `product_contract` shows that a product of two zero-constant
compositional iterates gains one degree of agreement, for arbitrary iterate
counts, supplying both stabilization and uniqueness.

Over `ZMod 6`, `mod_six_fixed` proves that `x/(1-x) = mobius 1` is a fixed point
of the three-four transformation. The frozen `mobius_iterate` formula reduces
the iterates to `mobius 3` and `mobius 4`; the identity
`(1-3X)(1-4X) = 1-X` in `ZMod 6` and cancellation of the unit `1-X` give the
formal-series equality. `hanna_conjecture` maps the proved integer equation
to `ZMod 6`, applies the private uniqueness theorem over that ring, and reads
off every positive-degree coefficient of `mobius 1`.

The generality-I module binds the frozen prerequisite
`D5/S1/Recurrence/Invariants/CompositionalIterateCongruence`, reusing `iterate`,
`mobius`, and `mobius_iterate`. Its freeze prerequisite statement_id is
`sha256:4063c4732963765b6b16b5dda51775b4d179cfc3a203c91ed15e3ebffb0467e7`,
read from `Golden/Frozen/state/D5/S1/Recurrence/Invariants/CompositionalIterateCongruence.lean.json`.
The prerequisite's five-six fixed-point result does not substitute for the
three-four construction and uniqueness argument.

## Falsifier

An index `n ≥ 1` whose coefficient in the unique zero-constant integer solution
satisfies `a(n) % 6 ≠ 1` would contradict the assertion. The orchestrator's
exact check is supporting evidence only; no finite check proves the unbounded
statement, and this seat did not rerun that check.

## Evidence

- Lean module: `D5/S1/Recurrence/Invariants/ThreeFourIterateProductModSix.lean`.
- Main theorem: `hanna_conjecture`.
- Companions: `generating_equation`, `generating_unique`, `mod_six_fixed`.
- Public definitions: `a`, `generatingSeries`.
- Axioms: std3, exactly `propext`, `Classical.choice`, `Quot.sound` for each
  public theorem, as reported by the implementation seat and recorded in its
  compiler log `/tmp/threefour-iterate-mod-six.lean.log`, read by Stage-B.
- The Scribe resolution claim for this slug is attached only to the Describe
  node of `hanna_conjecture`.

## Triage

`theorem`. The formal proof closes the first OEIS conjecture for all positive
indices. The second comment is outside the resolution claim's scope.

## ASSUMED-UNVERIFIED

The OEIS quotes, authorship, and date were supplied by the orchestrator. The
search seat, not this Stage-B seat, read the OEIS revision history on 2026-09-08.
The reported literature search covered that entry and history plus identifier
searches on arXiv, MathOverflow, and GitHub; it did not establish exhaustive
coverage of the literature or private indexes. Stage-B had no network access.
First-publication priority and the source-to-Lean identification are not
kernel-checked facts. Stage-B did not rerun Lean, C# compilation, emission,
freezing, or admission checks; those operations belong to the orchestrator's
verification and handoff, not to the dossier's evidence of local execution.
