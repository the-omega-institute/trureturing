---
slug: oeis-a305550-integral-egf-substitution-totient-period
bibkey: bala2022egfgeneral
doi: null
url: https://oeis.org/A305550
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Periodic/IntegralEgfTotientPeriod
---

# Bala's general integral e.g.f. substitution conjecture

## Problem

OEIS A305550 NAME (entry by Ilya Gutkovskiy, Jun 15 2018):

> Expansion of e.g.f. Product_{k>=1} (1 + (exp(x) - 1)^k).

COMMENT (Peter Bala, Jul 08 2022):

> Conjecture: Let k be a positive integer. The sequence obtained by reducing a(n) modulo k is eventually periodic with the period dividing phi(k) = A000010(k).

In the same comment:

> More generally, we conjecture that the same property holds for integer sequences having an e.g.f. of the form G(exp(x) - 1), where G(x) is an integral power series.

The broader sentence appears verbatim on both A305550 and A004123. These are
two source locations of **ONE conjecture settled once**, not two resolutions.

## Motivation

This is a first-tier OEIS conjecture from the 2022 entry/comment. The target
covers every integral power series and every positive modulus. KPI = open
problems resolved; no repository cumulative count is asserted.

## Gap

No proof was found within the supplied search scope: the search seat read the
OEIS entry and revision history on 2026-09-09 and searched identifiers on arXiv,
MathOverflow, and GitHub. This Stage-B seat had no network access and did not
repeat those searches. This is a scoped negative search, not a priority proof.

## Route

The escape witness is the **general** e.g.f. bridge
`n![Xⁿ] G(exp X − 1) = Σ_{k ≤ n} g_k · k! · S(n,k)`, valid for every integral
power series `G`, together with transport into the imported frozen totient-period
theorem. It is not merely the single-entry instance. The binomial theorem
expands each power of `exp X − 1`; powers of `exp` are rescaled exponentials
whose degree-n coefficients are `jⁿ/n!`; the imported Stirling
inclusion-exclusion identity gives `k!·S(n,k)`. The divisibility
`X^k ∣ (exp X − 1)^k` truncates the substitution to a finite sum in each degree,
so no infinite object is assumed in the coefficient argument. Its right-hand
side is visibly an integer: integrality is a consequence, not an assumption.

Periodicity itself is **IMPORTED** from the frozen module with
GID `D5/S1/Recurrence/Periodic/StirlingTransformTotientPeriod` and
statement_id `sha256:d6767ceb21f921d2a1a07b1bea6813c14127e562af25853770d17cc532cce98d`.
Applying its `stirling_transform_totient_period` gives period `φ(m)` modulo `m`
from `n ≥ m` for every positive `m`, proving Bala's general conjecture for every
integral `G`. This lane's new content is the bridge plus the distinct-part
identification, not a re-proof of the period.

For A305550, continuity transports Mathlib's distinct-part partition product
through substitution and identifies its weight with `Q(k)`, the number of
partitions of `k` into distinct positive parts. The proved `generating_equation`
identifies the exact product e.g.f. Neither onset `n ≥ m` nor period `φ(m)` is
claimed minimal. Target generality: G.

## Falsifier

An integral coefficient function `g`, a positive modulus `m`, and an index
`n ≥ m` with unequal residues of `egfCoefficient g (n + φ(m))` and
`egfCoefficient g n` would refute the proved bound. To refute only the
weaker eventual-periodicity conjecture would require failures arbitrarily far
out for a fixed modulus. The orchestrator's exact check is supporting evidence
only; a bounded search does not establish the universal assertion.

## Evidence

- Own Library note: `Library/ArithSums/bala2022egfgeneral.md` (bibkey `bala2022egfgeneral`),
  URL `https://oeis.org/A305550`, matching this dossier's URL.
- Lean module: `D5/S1/Recurrence/Periodic/IntegralEgfTotientPeriod.lean`.
- Main theorem: `bala_conjecture_egf_general`.
- Companions: `egf_shift_eq_stirling_transform`,
  `distinct_parts_generating_identity`, `generating_equation`.
- Axioms: std3 = `propext`, `Classical.choice`, `Quot.sound`.

The orchestrator supplied the following readings attributed to
`results/verify-r20.out` (that file was not available at the supplied worktree
path to this seat): the computed sequence reproduces the published A305550 DATA
exactly, `1, 1, 3, 19, 135, 1171, 12543`; distinct-part weights are
`Q(0..9) = 1, 1, 1, 2, 2, 3, 4, 5, 6, 8` (A000009); period `phi(m)` from
`n >= m` has zero violations for every `m` in `1..48`; and the bridge identity
was checked for three random integral `G` at every `n < 14`. These finite checks
are supporting evidence only, not proof.

## Triage

`theorem`. The formal proof closes this universal conjecture via the general
bridge and the imported frozen periodicity theorem.

## ASSUMED-UNVERIFIED

The quotations, attributions, source identification, and numerical readings
were supplied by the orchestrator. OEIS revision history was read by the search
seat, not this seat. Literature scope was the OEIS entry/revision history and
identifier searches on arXiv, MathOverflow, and GitHub; this seat had no network.
The broader sentence's duplicate occurrence on A004123 is source testimony,
not a kernel-checked fact. No exhaustive literature search or first-publication
priority is claimed. The source-to-Lean identification is documented by the
bridge and exact generating equation but the external source itself is not
kernel-checked.
