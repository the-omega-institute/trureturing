---
slug: ann-item-six
bibkey: abednikolaevanovikov2026traces
doi: 10.48550/arXiv.2610.34388
url: https://arxiv.org/abs/2610.34388v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/AbedNikolaevaNovikovItemSix.result
---

# Abed–Nikolaeva–Novikov Conjecture 11.1, item 6

## Problem

Abed, Nikolaeva and Novikov, *How characterisations of traces and central elements fail: sharp violation constants via Michelson contrast and noncentrality*, arXiv:2610.34388v1, Conjecture 11.1, ask whether the spectral-mean trace-violation envelope in complex dimension two equals $1/\sqrt{1-\delta^2}-1$ throughout the faithful contrast range.

### Statement echo

For every real $\delta$ with $0\le\delta<1$, let $V(\rho)$ be the real supremum of
\[
\frac{\operatorname{Re}\operatorname{Tr}(\rho\,\operatorname{specMean}(A,B,1/2))-\sqrt{\operatorname{Re}\operatorname{Tr}(\rho A)\,\operatorname{Re}\operatorname{Tr}(\rho B)}}{\sqrt{\operatorname{Re}\operatorname{Tr}(\rho A)\,\operatorname{Re}\operatorname{Tr}(\rho B)}}
\]
over positive definite complex $2\times2$ matrices $A,B$. The envelope is the real supremum of $V(\rho)$ over positive definite complex qubit densities whose spectral contrast is $\delta$. The settled proposition is
\[
\forall\delta\in\mathbb R,\quad 0\le\delta<1\Longrightarrow
\operatorname{envelope}(\delta)=\frac1{\sqrt{1-\delta^2}}-1.
\]
The Lean declaration is `D5/S3/Quantum/Matrix/AbedNikolaevaNovikovItemSix.result`.

## Motivation

The equality gives the sharp outer envelope for every faithful complex qubit density at each prescribed contrast. It includes arbitrary positive scales and unrestricted positive definite complex inputs.

## Gap

The source stated the equality as Conjecture 11.1, item 6. The source's stronger fixed-density sharpness, the singular endpoint, dimensions at least three and the remaining conjecture items are separate questions.

## Route

The proof reduces the two-component off-diagonal term to a completed-square scalar inequality. The contrast trace/determinant identity then yields a uniform upper bound after spectral diagonalization. A positive definite family with a parameter tending to zero supplies the matching lower limit for every $\delta\in[0,1)$, so the two nested suprema have the same value.

## Falsifier

A counterexample would be a faithful positive definite complex qubit density and a contrast in $[0,1)$ for which the displayed envelope equality fails, or a failure of the positivity, boundedness or nonemptiness conditions needed by the defining real suprema. The Lean result proves the complete proposition; the independent finite checker is evidence for selected exact instances only.

## Evidence

The kernel-checked settling declaration is `D5/S3/Quantum/Matrix/AbedNikolaevaNovikovItemSix.result`, with the expanded claim mirrored in its Blueprint document. Its axiom closure is contained in `{propext, Classical.choice, Quot.sound}`. The supporting trace-positivity owner is `D5/S3/Quantum/Matrix/AbedNikolaevaNovikovAFDensityBound.trace_pair_pos`.

The independent checker is pinned to commit `899d34d8041742cedebc176045cf870d202805a2` in `the-omega-institute/trureturing-experiments`, path `docs/reports/michelson-trace-violation-two-dim/check.py`, SHA-256 `c38a22de5c2abd02f88fce0dac6b6444e2f856c112698a8887cb50157c4e6ae0`. Running `python3 /tmp/ann2610i6-check.py` at that immutable source exits 0 and reports 2800 exact scalar cases, 756 complex-vector/density cases, a non-diagonal unitary transport check, symbolic determinant and trace identities, the sharp-family limit, and `ALL_CHECKS_OK`.

The escape audit for newly public non-result declarations remains unfinished under [issue #24453](https://github.com/the-omega-institute/trureturing/issues/24453). No `declared_validated` registration is claimed without the required CI reading.

## Triage

- **Proved — completed-square scalar estimate.** `scalar_squared` proves the completed-square estimate controlling the two-component off-diagonal term; this is kernel-checked evidence.
- **Proved — uniform upper bound.** `trace_bound`, `quotient_bound` and `V_bound` combine the contrast trace/determinant identity with the scalar estimate to prove the uniform upper bound for every positive definite complex qubit density; this is kernel-checked evidence.
- **Proved — sharp outer supremum.** `sharp_positive`, `sharp_traces`, `family_limit` and `sharp_lower` construct a positive definite family approaching the bound for each $\delta\in[0,1)$ and prove the matching outer supremum equality; this is kernel-checked evidence.
- **Computed — independent exact checker.** The pinned experiment command exits 0 with `ALL_CHECKS_OK` for exactly 2800 scalar cases, 756 complex-vector cases, non-diagonal unitary transport, determinant and trace identities, and the sharp-family limit. Its script SHA-256 is `c38a22de5c2abd02f88fce0dac6b6444e2f856c112698a8887cb50157c4e6ae0`; this finite computation is separate from the Lean proof.
- **Open — fixed-density equivalence and sharpness.** A separately formalized theorem giving the equivalence and sharpness statement for every individual faithful density is not claimed.
- **Open — neighbouring regimes.** Dimension at least three, the endpoint $\delta=1$, the other Conjecture 11.1 items and attainment classification beyond the proved limit are outside this result.

### What the settlement shows

The item-6 conjecture is proved on the full faithful qubit interval. The completed-square mechanism controls the off-diagonal contribution, while the trace/determinant identity converts spectral contrast into the exact envelope. The same argument supplies the matching limit through positive definite matrices, so the result is sharp as an outer supremum even when no individual positive definite pair is asserted to attain it. The source's fixed-density, higher-dimensional and singular-endpoint questions remain open.

## ASSUMED-UNVERIFIED

The literature screen is partial. Completeness of the search for prior proofs, refutations, equivalent formulations and all relevant cited sources is `ASSUMED-UNVERIFIED`; no worldwide priority claim is made.
