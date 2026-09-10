---
slug: oeis-a396844-scaled-quadratic-reversion-mod-sixteen
bibkey: hanna2026a396844
doi: null
url: https://oeis.org/A396844
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Parity/ScaledQuadraticReversionModSixteen
---

# Refutation of the A396844 mod-sixteen conjecture

## Problem

OEIS A396844, Paul D. Hanna, Jul 03 2026, gives the following NAME and
COMMENT, quoted verbatim from `Library/Recurrence/hanna2026a396844.md`:

> G.f. A(x) satisfies A( x*A(x) - 4*x*A(x)^2 ) = x^2.

> Conjecture: for n > 8, a(n) == 12 (mod 16) iff n is of the form 2*4^k+1 otherwise a(n) is divisible by 16.

The conjecture is refuted at n = 17. The orchestrator reports
`a(17) = 113101684573952804`, congruent to 4 modulo 16. Since 17 is not
of the form `2*4^k+1`, the "otherwise divisible by 16" clause is false.
The supplied numeric-check locator is `results/verify-a396844-mod16.out`;
that file was not available at this worktree path during Stage B.

## Motivation

This is a first-tier OEIS conjecture from 2026. KPI = open problems resolved.
The resolution is a refutation together with a corrected classification
for every natural index n >= 2.

## Gap

The search seat reported no proof found after reading the OEIS entry and
revision history on 2026-09-09 and searching the identifier on arXiv,
MathOverflow and GitHub. This seat has no network and did not repeat those
searches. This records the search scope, not a proof of absence.

## Route

Write the normalized series as `A = X + X^2*C`. A contracting operator on C
has a fixed point constructed by stabilized coefficients.
`generating_equation` gives `A(0) = 0`, `a(1) = 1` and
`A.subst(X*A - 4*X*A^2) = X^2`, exactly the OEIS equation.
`generating_unique` identifies every normalized integral solution with A.
`mod_four_identity` gives `A = X` modulo 4.

A coefficientwise substitution argument preserves annihilated differences.
It shows that four times the shifted alternating-dyadic series is the
mod-16 fixed point for C. The frozen module
`D5/S1/Recurrence/Invariants/AlternatingDyadicReversionModFour` supplies its
public `inverseSeries`, `R = sum_j (-1)^j X^(2^j)`, and public
`inverse_equation`, `R + R(X^2) = X`. Thus `A = X + 4*X*R` modulo 16.
Coefficient induction gives `mod_sixteen_classification`: for n >= 2,
`a(n) = 4` modulo 16 iff `n = 2^k+1` with k even, `a(n) = 12` modulo 16
iff `n = 2^k+1` with k odd, and `16 | a(n)` iff n is off this support.

`hannaClaim` is the closed Prop stating both clauses of the quoted OEIS
conjecture for n > 8. `hanna_conjecture_false : not hannaClaim` refutes it
symbolically at `17 = 2^4+1`: exponent 4 is even, so `a(17) = 4` modulo 16.
17 is NOT of the form `2*4^k+1`; in particular, `2*4^2+1 = 33`.
The conjecture's divisibility clause therefore fails. Its residue-12 clause
is correct, since `2*4^k+1 = 2^(2*k+1)+1` is exactly the odd-exponent case.
The classification is the corrected statement, not a proof of the conjecture.

Target generality is I because the proof imports the frozen module above,
itself generality G, with statement_id
`sha256:ebfceee0d5bda860ab48b7b166d70a8e3e1c5aeb4e969050423894b570ddd652`.
Only `hanna_conjecture_false` carries `ResolutionKind.Refuted` in Scribe.

## Falsifier

The counterexample index is 17: n > 8, n is outside `2*4^k+1`, yet
`16` does not divide `a(n)`. The orchestrator's exact integer check is
supporting evidence only; the kernel refutation uses the symbolic residue.

## Evidence

- Lean module: `D5/S1/Recurrence/Parity/ScaledQuadraticReversionModSixteen.lean`.
- Main theorem: `hanna_conjecture_false : not hannaClaim` (Lean `¬ hannaClaim`).
- Companions: `generating_equation`, `generating_unique`, `mod_four_identity`,
  `mod_sixteen_classification` (the corrected statement).
- Claim definition: `hannaClaim`; series and coefficients: `generatingSeries`, `a`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`), as reported by
  the implementation seat for all five public theorems.

## Triage

`theorem`. The refutation and the corrected classification are kernel
theorems. The resolution kind is `Refuted`, attached to
`hanna_conjecture_false`, not to the classification or a companion.

## ASSUMED-UNVERIFIED

The quotes and attribution were supplied by the orchestrator. The OEIS
revision history was read by the search seat, not by this seat. Literature
scope was the OEIS entry and revision history plus identifier searches on
arXiv, MathOverflow and GitHub on 2026-09-09. This seat had no network;
first-publication priority, source-to-Lean identification and completeness
of the literature search are not kernel-checked facts. The exact numeric
output at the supplied locator was not read by this seat.
