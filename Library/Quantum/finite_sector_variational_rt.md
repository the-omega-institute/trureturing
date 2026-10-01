---
bibkey: finite_sector_variational_rt
authors: the-omega-institute/trureturing
title: "Finite-sector variational domination and orientation-cover obstruction"
year: 2026
doi: null
url: https://github.com/the-omega-institute/trureturing/tree/dev/D5/S3/Quantum/Entanglement
claim: "Repository-derived finite-sector variational lemma and finite-phase orientation monodromy obstruction."
strata_touched: []
license: citation-only
triage: anchor
---

## Scope

This note records two repository-derived finite statements added on branch lane/theory/rt-variational-20260930. They are finite-dimensional facts and do not claim a continuum or gravitational RT theorem.

## Variational lemma

For a nonempty finite sector type and an entrywise nonnegative real matrix A, the Lean declaration simplex_quadratic_dominates_weighted_complex_form supplies a simplex point r such that Q_A(w) <= Q_A(r) for every simplex point w. It also proves R_A(p,x) <= Q_A(r) for every simplex point p and every complex unit-l2 vector x, where R_A uses sqrt(p_i) sqrt(p_j) A_ij times Re(conj(x_i) x_j).

The witness argument sets y_i = sqrt(p_i) * norm(x_i), uses finite Cauchy-Schwarz to obtain sum_i y_i <= 1, fills the deficit at one coordinate to produce a simplex point w >= y, and applies Re(conj(x_i) x_j) <= norm(x_i) norm(x_j).

## Orientation obstruction

The exact Fibonacci certificate in docs/reports/fib-canonical-budget/certificate.py computes a common phase period 80 modulo 5040 = 16 * 9 * 5 * 7, with local periods 8, 8, 20, and 16 for 16, 9, 5, and 7. The GoldenScaleHelix deck step flips a Boolean orientation. The declaration orientationCover_monodromy proves identity monodromy for every even cycle, with explicit 80-step and 16-step instances. Hence this finite phase data defines a trivial two-sheet orientation cover; a Mobius interpretation would require an additional odd gluing or independent parameter loop.

This is a statement about the chosen finite Boolean-flip model only. It does not rule out an unrelated geometric Mobius or Klein realization.

## Verification status

The declarations are present on the branch above. Focused Lean kernel checks passed in PR CI after the namespace fix; Scribe and current harness checks are pending the next run.
