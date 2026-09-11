---
slug: oeis-a396099-iterate-product-two-three-mod-four
bibkey: hanna2026a396099
doi: null
url: https://oeis.org/A396099
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Parity/IterateProductTwoThreeModFour
---

# The A396099 period-four coefficient pattern

## Problem

OEIS A396099 (Paul D. Hanna, Jun 02 2026) gives the NAME:

> G.f. satisfies A(x) = x + A^2(x)*A^3(x).

Here A^k denotes the k-fold compositional iterate, as the entry's formulas
and PARI program make explicit: A^2(x) = A(A(x)) and A^3(x) = A(A(A(x))).
The single resolution anchor of this dossier is the COMMENT:

> Conjecture: a(n) = [1,3,3,1] repeating (mod 4) for n > 2.

The entry also states three companion conjectures:

> Conjecture: all terms are odd.

> Conjecture: [x^n] A(A(x)) == 0 (mod 4) for n > 2.

> Conjecture: [x^n] ( A(x) - x*A(A(A(x))) ) == 2 (mod 4) for n > 2.

These are settled by `all_odd`, `iterate_two_mod_four`, and `shift_mod_four`,
respectively, without adding a second resolution claim.

## Motivation

This is a first-tier OEIS conjecture from the 2026 entry. The KPI is open
problems resolved: `hanna_conjecture` proves the anchored pattern for all
indices greater than two, and the same module settles the three companions.

## Gap

The supplied search found no proof: the search seat read the OEIS entry and
revision history on 2026-09-09 and searched the identifier on arXiv,
MathOverflow, and GitHub. This Stage-B seat had no network access and did
not independently repeat that literature search.

## Route

A is the stabilised fixed point of F ↦ X + iterate F 2 · iterate F 3, using
the frozen `iterate`. `generating_equation` gives A(0) = 0, a(1) = 1, and
A = X + A∘2·A∘3. `generating_unique` covers every zero-constant integer
solution. The frozen `fixed_unique` hardcodes iterates 5 and 6, so the
implementation adapted minimal private contraction and stabilisation lemmas.

Over ZMod 4, `mod_four_identity` identifies Ā with
F := mobius 1 + 2X⁴·((1−X)(1+X²))⁻¹. Unit-denominator cancellation proves
iterate F 2 = X + 2X² and F = X + (X + 2X²)(F + 2F²) in characteristic
four. Degree-of-agreement induction identifies this rational fixed point
with the reduction of A.

The geometric expansion of F proves `hanna_conjecture`: for n > 2,
a(n) % 4 is 1 when n % 4 belongs to {2, 3}, and 3 otherwise. Starting at
n = 3, this is precisely the OEIS [1,3,3,1] repeating pattern. It also
proves `all_odd` for n ≥ 1. The composition and shifted-series identities
give `iterate_two_mod_four`, [xⁿ]A∘2 ≡ 0 (mod 4), and `shift_mod_four`,
[xⁿ](A − X·A∘3) ≡ 2 (mod 4), both for n > 2. Thus all four quoted
conjectures are settled, with only the pattern theorem anchoring this dossier.

Target generality is I because the module imports the frozen
`D5/S1/Recurrence/Invariants/CompositionalIterateCongruence`, itself generality G.

## Falsifier

A counterexample index n > 2 whose coefficient fails the specified
modulo-four pattern would falsify the anchored assertion. The orchestrator's
exact coefficient check is supporting evidence only, not the universal proof.

## Evidence

- Lean module: `D5/S1/Recurrence/Parity/IterateProductTwoThreeModFour.lean`.
- Main theorem: `hanna_conjecture`.
- Companions: `generating_equation`, `generating_unique`, `mod_four_identity`,
  `all_odd`, `iterate_two_mod_four`, `shift_mod_four`.
- Axioms: std3 = `propext`, `Classical.choice`, `Quot.sound`, as reported
  for all seven public theorems by the implementation seat.
- Frozen dependency statement_id:
  `sha256:4063c4732963765b6b16b5dda51775b4d179cfc3a203c91ed15e3ebffb0467e7`.

## Triage

`theorem`. The formal proof closes the universal pattern assertion and
settles the three quoted companion conjectures.

## ASSUMED-UNVERIFIED

The quotations were supplied by the orchestrator and copied from
`Library/Recurrence/hanna2026a396099.md`. The search seat, not this seat,
read the OEIS revision history. The literature scope was the OEIS entry and
history plus identifier searches on arXiv, MathOverflow, and GitHub; no
exhaustive literature or first-publication priority claim follows. This
seat had no network access. Source-to-Lean identification and the
orchestrator's exact numerical check are not kernel-checked facts.
