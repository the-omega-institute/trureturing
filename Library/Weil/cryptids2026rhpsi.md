---
bibkey: cryptids2026rhpsi
authors: Google LLC (Google DeepMind)
year: 2026
title: Cryptids — formal RH Chebyshev psi estimate and analytic source closure
doi: null
url: https://github.com/google-deepmind/cryptids/blob/e5f59ed70d1549a61ef8873a6fbae9268fdbd557/Cryptids/Semantics/Riemann/Analytic.lean
claim: The original formal proof derives the real-variable Chebyshev psi estimate with coefficient seven eighths for every x at least 5000 under the Riemann hypothesis.
strata_touched:
  - D5/S3/Weil/Mertens/Cryptids/Schoenfeld
license: Apache-2.0
triage: anchor
---

The original supplier is google-deepmind/cryptids at immutable revision
`e5f59ed70d1549a61ef8873a6fbae9268fdbd557`. In
`Cryptids/Semantics/Riemann/Analytic.lean`, the exact original theorem is
`ConjectureMachines.Semantics.Riemann.abs_psi_sub_self_le_seven_eighths_of_five_thousand_le`.
With the source's `SchoenfeldPsiBound` expanded, it states

$$
\mathrm{RiemannHypothesis}\;\Longrightarrow\;
\forall x\in\mathbb R,\quad 5000\le x\;\Longrightarrow\;
|\psi(x)-x|\le\frac78\sqrt{x}(\log x)^2,
$$

where $\psi$ is Mathlib's `Chebyshev.psi` and the RH premise is Mathlib's
`RiemannHypothesis`. The 17 modules under `D5/S3/Weil/Mertens/Cryptids/`
transplant this original formal proof and its necessary analytic closure;
they are not a new local discovery, a newly peer-reviewed paper, or a proof of RH.

Copyright (c) 2026 Google LLC. The Apache-2.0 full license is retained at
`docs/reports/licenses/cryptids-LICENSE.txt`, with copyright and source notices
in the transplanted Lean modules.

The upstream pins are `leanprover/lean4:v4.35.0-rc4` and Mathlib
`1f414401f69059aa7eead47b53ee40bd38455eeb`; the project pins are
`leanprover/lean4:v4.35.0` and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. Their inequality selects the
A17.2 source-transplant route rather than a Lake dependency. Routing and
necessary current-pin API adaptations preserve the original proof ownership.
Retire the transplant when the Mathlib revision actually adopted in this
repository's `lake-manifest.json` supplies an equivalent RH-only real-variable
estimate for every $x\ge5000$; directly reference that supplier and remove the
unused transplanted closure.

## Locator

https://github.com/google-deepmind/cryptids/blob/e5f59ed70d1549a61ef8873a6fbae9268fdbd557/Cryptids/Semantics/Riemann/Analytic.lean
