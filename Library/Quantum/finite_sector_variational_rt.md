---
bibkey: repo-finite-sector-variational-rt
title: "Finite-sector variational domination and orientation-cover obstruction"
year: 2026
url: https://github.com/the-omega-institute/trureturing/tree/dev/D5/S3/Quantum/Entanglement
claim: "Repository-derived finite-sector variational lemma and a finite-phase orientation monodromy obstruction."
strata_touched:
  - D5/S3/Quantum/Entanglement/FiniteSectorSchurUpper
  - D5/S3/CompletionDynamics/GoldenMobius/GoldenScaleHelix
license: citation-only
---

## Scope

This note records two repository-derived finite statements added on branch `lane/theory/rt-variational-20260930`. They are finite-dimensional facts and do not claim a continuum or gravitational RT theorem.

## Variational lemma

For a nonempty finite sector type and an entrywise nonnegative real matrix (A), the Lean declaration `simplex_quadratic_dominates_weighted_complex_form` supplies (r) in the real simplex such that

[
sum_{i,j} A_{ij}w_iw_j le sum_{i,j} A_{ij}r_ir_j
]

for every simplex (w), and

[
sum_{i,j}sqrt{p_i}sqrt{p_j}A_{ij}operatorname{Re}(overline{x_i}x_j)
le sum_{i,j}A_{ij}r_ir_j
]

for every simplex (p) and complex unit-(ell^2) vector (x). The witness argument sets (y_i=sqrt{p_i}lVert x_iVert), uses finite Cauchy--Schwarz to obtain (sum_i y_ile1), fills the deficit at one coordinate to produce a simplex (wge y), and applies the phase bound (operatorname{Re}(overline{x_i}x_j)lelVert x_iVertlVert x_jVert).

## Orientation obstruction

The exact Fibonacci certificate in `docs/reports/fib-canonical-budget/certificate.py` computes a common phase period (80) modulo (5040=16cdot9cdot5cdot7), with local periods (8,8,20,16) for (16,9,5,7). The GoldenScaleHelix deck step flips a Boolean orientation. The declaration `orientationCover_monodromy` proves identity monodromy for every even cycle, with explicit (80)- and (16)-step instances. Hence this finite phase data defines a trivial two-sheet orientation cover; a Möbius interpretation would require an additional odd gluing or independent parameter loop.

The distinction agrees with the repository's D-ZCOCT boundary: a Klein four-group orbit is not itself a Klein bottle topology, and nontrivial Möbius monodromy requires explicit parameter transport.

## Verification status

The declarations are present on the branch above. Focused Lean kernel and CI checks for the new commits are pending until a pull request run is available.
