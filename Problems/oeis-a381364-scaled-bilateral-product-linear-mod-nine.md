---
slug: oeis-a381364-scaled-bilateral-product-linear-mod-nine
bibkey: hanna2025a381364
doi: null
url: https://oeis.org/A381364
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Bilateral/ScaledBilateralProductModNine
---

# The A381364 scaled bilateral product congruence

## Problem

This dossier cites its own Library note,
`Library/ArithSums/hanna2025a381364.md`, for the A381364 conjecture.
The two entry statements describe instances of one family:

OEIS A381364, Paul D. Hanna, Feb 21 2025, NAME:

> G.f. A(x) satisfies 1/3 = Sum_{n=-oo..+oo} x^n*A(x)^n * (A(x)^n + 2*x)^(n-1) * (x^n + 2*A(x))^(n-1).

COMMENT:

> Conjecture: for n > 0, a(n) == 6 (mod 9).

OEIS A381365, Paul D. Hanna, Feb 21 2025, NAME:

> G.f. A(x) satisfies 1/3 = Sum_{n=-oo..+oo} x^n*A(x)^n * (A(x)^n + 2*x)^(2*n-1) * (x^n + 2*A(x))^(2*n-1).

COMMENT:

> Conjecture: for n > 0, a(n) == 6 (mod 9).

## Motivation

This is a first-tier OEIS conjecture from 2025. The mathematical target is a
universal congruence for the normalized generating series. KPI = open problems
resolved; no repository cumulative count is asserted.

## Gap

The supplied search report found no proof: the search seat read the OEIS entry
and revision history on 2026-09-09 and performed identifier searches on arXiv,
MathOverflow, and GitHub. This Stage-B seat had no network access and did not
repeat those searches. The reported gap is a proof of the universal congruence
from the literal bilateral equation, including the negative indices.

## Route

The escape witness is the **general** theorem `hanna_conjecture_general`, covering
every `c ≥ 1`, rather than the two named instances: the unique normalized integer
solution of
`1/3 = Σ_{n∈ℤ} xⁿ·Aⁿ·(Aⁿ + 2x)^{cn−1}·(xⁿ + 2A)^{cn−1}`
has `a(c,n) ≡ 6 (mod 9)` for every `n > 0`. In the checked source's parameter
convention, A381364 is `c = 1` and A381365 is `c = 2`.

The literal Laurent summand is retained in `laurentTerm` over `LaurentSeries ℚ`
with integer exponents, including negative indices. Thus the formalized equation
is the OEIS equation, rather than a paraphrase. The finite-window theorem and
pairing of opposite indices give a well-defined integral coefficient construction:
the summand has order at least `n` for `n ≥ 1` and order at least `c·k²` for
`n = −k`, `k > 0`. Each coefficient therefore depends on finitely many indices;
no infinite sum object or summability assumption is used. Formal power series
and Laurent series remain the ambient objects. Pairing proves the nonzero
remainder even, giving `H = 2J`. An integral contracting iteration has a fixed
point with `a c n := coeff n (approximation c (n+1))`.

The normalized form `(1 + 2x)(1 + 2A)(1 − 3H) = 3` yields
`A − (1 − 3xG) = 9(1 + 2B)J`, where `G = (1 + 2x)⁻¹`.
Since `coeff m G = (−2)^m ≡ 1 (mod 3)`, every positive coefficient is
`6 (mod 9)`. Existence uses `generating_equation`; `generating_unique` identifies
every normalized integer solution with the constructed series.

The actual IMPORTED and frozen prerequisite is `D5/S1/Recurrence/Bilateral/BilateralProductModFour`,
statement_id `sha256:e80c04dabc53956b6912a1f482e052ba0c5fb1bb30d501daf127d6ae3b41e406`; the module header therefore has generality `I`.
Its public statements concern the unscaled family; the implementation adapted
the private agreement and embedding arguments rather than reusing them verbatim.
The brief's requested prerequisite `D5/S1/Recurrence/Bilateral/ScaledBilateralProductModNine` is the target itself, not its
import. Its requested `Golden/Frozen/state/D5/S1/Recurrence/Bilateral/ScaledBilateralProductModNine.lean.json` was absent in the
Stage-B inspection, so no statement_id for that target can be quoted. This
dependency discrepancy is recorded as a plan deviation; no self-import or
unverified freeze is asserted.

## Falsifier

A positive index `n` in the normalized integer solution for A381364
(`c = 1`) whose coefficient is not congruent to 6 modulo 9 would falsify this
entry's assertion. More generally, such an index for any `c ≥ 1` would falsify
the escape theorem. The orchestrator's exact finite check is supporting evidence
only and cannot exclude every counterexample index.

## Evidence

- Lean module: `D5/S1/Recurrence/Bilateral/ScaledBilateralProductModNine.lean`.
- Entry theorem: `hanna_conjecture_a381364`; the general escape theorem is
  `hanna_conjecture_general`. The source has no declaration named `hanna_conjecture`.
- Companions: `finite_window`, `polynomial_form` (the normalized form
  `(1 + 2x)(1 + 2A)(1 − 3H) = 3`), `generating_equation`, and `generating_unique`.
- Axiom boundary: std3 (`propext`, `Classical.choice`, `Quot.sound`);
  single-file verification output is recorded in
  `build/op-a381364-stage-b/lean.log`.

The orchestrator supplied readings attributed to `results/verify-r21.out`:
for both `c = 1` and `c = 2`, coefficients were integral through `n < 24`, the
computed coefficients reproduced the published DATA exactly
(`1, 6, 69, 1185, 25971, 638664, 16870146` and
`1, 6, 267, 13686, 850848, 58650900, 4328042982`, respectively), the residual of
the defining relation was identically zero through degree 23, and
`a(n) ≡ 6 (mod 9)` held at every index `1..23`, with zero violations in both
cases. The orchestrator solved the defining relation in exact rational
arithmetic, rather than reading coefficients off a printed recurrence. These
are supporting checks, not proof; the referenced output file was absent from
this worktree during Stage-B inspection, so this seat did not independently
verify those readings.

## Triage

`theorem`. The general formal statement specializes to this entry's conjecture
at `c = 1`. Its source identification is subject to the provenance boundary below.

## ASSUMED-UNVERIFIED

The OEIS quotations and entry date were supplied by the orchestrator and copied
from the Library notes. The OEIS entry and revision history were read by the
search seat, not this seat. The reported literature scope is the OEIS entry and
revision history plus identifier searches on arXiv, MathOverflow, and GitHub;
it does not establish an exhaustive literature search or first-publication
priority. This seat had no network. The numerical readings above are attributed
to the orchestrator; their referenced file was not available here. Source-to-Lean
identification and the implementation's adaptation history are not kernel-checked
facts. The supplied implementation-seat envelope described an earlier simplified
proof and was not used to certify the inspected source or its escape witness.
