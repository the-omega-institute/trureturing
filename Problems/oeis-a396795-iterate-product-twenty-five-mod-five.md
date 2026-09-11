---
slug: oeis-a396795-iterate-product-twenty-five-mod-five
bibkey: hanna2026a396795
doi: null
url: https://oeis.org/A396795
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Residue/IterateProductTwentyFiveModFive
---

# Divisibility of the A396795 coefficients

## Problem

OEIS A396795, Paul D. Hanna, Jun 06 2026, gives the following NAME and COMMENT,
quoted verbatim from `Library/Recurrence/hanna2026a396795.md`:

> G.f. A(x) satisfies A^2(x) * A^3(x) = x^2 + 25*x^3, where A^n(x) is the n-th iteration of A(x).

> Conjecture: a(n) == 0 (mod 5) for n > 1.

## Motivation

This is a first-tier OEIS conjecture from the 2026 entry. The KPI is open
problems resolved. The target proves divisibility for every index greater
than one of the uniquely determined normalized integer formal series.

## Gap

The search seat reported no proof found after reading the OEIS entry and
revision history on 2026-09-09 and performing identifier searches on arXiv,
MathOverflow, and GitHub. This Stage-B seat has no network access and did not
repeat those searches. This is a bounded search report, not a claim of
exhaustive literature coverage or first-publication priority.

## Route

The escape content is `iterate_product_lift`, general in the natural modulus
`m` and in both natural iterate indices `i, j`. For an integer formal series
`f` with `constantCoeff f = 0`, if `m` divides every coefficient of `f - X`
and `m ∣ i + j`, then `m²` divides every coefficient of
`iterate f i * iterate f j - X²`.

Write `f = X + C m * b` by coefficientwise division and work in `ZMod (m²)`.
There `(m : ZMod (m²))` squares to zero, and `nilpotent_iterate` gives
`iterate f k = X + C (k·m)·b` after mapping. The quadratic correction
vanishes; the cross-term scalar `C ((i+j)·m)` vanishes **whenever**
`m ∣ i + j`, which is the direction the theorem uses and proves. The converse
holds for `m > 0` but fails at the degenerate modulus zero, where every scalar
vanishes: `m = 0`, `i = 1`, `j = 0` gives a vanishing scalar while `0 ∤ 1`.
The theorem is stated with `m ∣ i + j` as a hypothesis, so it covers `m = 0`
without asserting that equivalence. The public
`subst_annihilate` supplies the substitution step of `nilpotent_iterate`.

At `(m,i,j) = (5,2,3)`, the lift makes successive degree-by-degree corrections
exact and divisible by 5. `generatingSeries` selects the proved existential
witness and `a n` denotes its degree-n coefficient. `generating_equation`
asserts `iterate A 2 * iterate A 3 = X² + 25X³`, `A(0) = 0`, and `a(1) = 1`.
Thus it realizes the NAME: `A^n` is the frozen compositional `iterate` from
`D5/S1/Recurrence/Invariants/CompositionalIterateCongruence`, not an ordinary
power. `generating_unique` covers every normalized integer solution.
`hanna_conjecture` concludes `n > 1 → 5 ∣ a n` through `solution_five`,
`error_divisible`, and the lift. Target generality is I because the module
imports the frozen `Invariants/CompositionalIterateCongruence`, itself G.

## Falsifier

An index `n > 1` for which the normalized solution has `5 ∤ a(n)` would
contradict the conjecture. The orchestrator's exact coefficient check is
supporting evidence only; the theorem has no finite index bound.

## Evidence

- Lean module: `D5/S1/Recurrence/Residue/IterateProductTwentyFiveModFive.lean`.
- Main theorem: `hanna_conjecture`.
- Companions: `subst_annihilate`, `nilpotent_iterate`, `iterate_product_lift`,
  `generating_equation`, `generating_unique`.
- Public definitions: `generatingSeries`, `a`.
- Axioms: std3, exactly `propext`, `Classical.choice`, `Quot.sound`, as
  reported by the implementation seat's `#print axioms` checks.
- Frozen direct import: `D5/S1/Recurrence/Invariants/CompositionalIterateCongruence`,
  statement_id `sha256:4063c4732963765b6b16b5dda51775b4d179cfc3a203c91ed15e3ebffb0467e7`.

`iterate_product_lift` is NOT an instantiation of any frozen public theorem.
The frozen `D5/S1/Recurrence/Invariants/TripleIterateProductModFour` fixes
`(m,i,j) = (4,1,3)` and the frozen
`D5/S1/Recurrence/Residue/IterateProductNineModThree` fixes `(3,1,2)`.
`IterateProductNineModThree.lift_mod_nine` is public on dev, but its modulus
and both iterate indices are fixed; the scalar helpers `subst_annihilate` and
`nilpotent_iterate` are private in both siblings. That is why those two are
published here for the first time, together with the variable-modulus,
variable-index lifting theorem, which neither sibling states. Neither sibling is
imported by this module.

| OEIS entry | (m,i,j) | Defining equation (superscripts mean iteration) |
| --- | --- | --- |
| A396794 | (4,1,3) | `A(x) * A^3(x) = x^2 + 16*x^3` |
| A396793 | (3,1,2) | `A(x) * A^2(x) = x^2 + 9*x^3` |
| A396795 | (5,2,3) | `A^2(x) * A^3(x) = x^2 + 25*x^3` |

## Triage

`theorem`. The formal proof closes the universal coefficient divisibility
assertion for the unique normalized integer solution of the NAME equation.

## ASSUMED-UNVERIFIED

The quotations and attribution were supplied by the orchestrator and copied
from the Library note. The search seat, not this seat, read the OEIS revision
history on 2026-09-09. The reported literature scope comprised the OEIS entry
and history plus identifier searches on arXiv, MathOverflow, and GitHub;
private indexes and exhaustive literature coverage were not established.
This seat had no network. Source-to-Lean identification, source dates,
search completeness, and first-publication priority are not kernel-checked
facts. Compilation, std3 axiom output, and the exact numerical check were
reported by the implementation seat or orchestrator, not rerun by Stage B.
