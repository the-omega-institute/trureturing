---
bibkey: lyng2026compactstrassen
authors: Daniel Lyng
year: 2026
title: "Econlib compact scalar Strassen construction"
doi: null
url: https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean
claim: "Compact real convex order is equivalent to existence of a martingale coupling; the attributed construction is adapted to native ProbabilityMeasure and conditional expectation."
strata_touched:
  - D5/S3/Analytic/Convexity/FiniteMajorization
  - D5/S3/Analytic/Probability/CompactQuantile
  - D5/S3/Analytic/Probability/CompactConvexOrder
  - D5/S3/Analytic/Probability/FiniteMartingaleCoupling
  - D5/S3/Analytic/Probability/ConditionalMeanAtoms
  - D5/S3/Analytic/Probability/ConditionalMeanApproximation
  - D5/S3/Analytic/Probability/CompactStrassen
license: citation-only
triage: anchor
---

## Verified locator

Source: https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean

The original endpoint is `strassen_iff` at line 92 of the cited source. The proof supplier is the immutable Econlib source at revision `d7bd9477476cade1c6695c8891746048ceddc52f`, by Daniel Lyng. The selected construction and its consumed dependencies are ported under Apache-2.0; the complete 10,174-byte license is retained at `docs/reports/licenses/econlib-strassen/LICENSE.txt` (SHA-256 `0d542e0c8804e39aa7f37eb00da5a762149dc682d7829451287e11b938e94594`). The bounded original-source inventory found no NOTICE file. This observation does not assert the absence of notices outside that inventory.

The donor uses Lean 4.29 and Mathlib revision `8a178386ffc0f5fef0b77738bb5449d50efeea95`; the host uses Lean 4.35 and Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`. This is an attributed source port, not a package installation. Modifications adapt the native probability-measure map API, reuse the frozen `CostTransport.IsCoupling` predicate and pinned Birkhoff and convexity results, group the construction by mathematical ownership, and identify the bounded-Borel tested condition with native joint-a.e. conditional expectation. Retire ported subproofs when equivalent results become available at the host's pinned library boundary.

The exact host result quantifies over all real endpoints and both Borel probability laws assigning mass one to their closed interval. Tests are convex and continuous only on that interval. The witness is one joint probability measure with both exact pushforward marginals and conditional expectation of its second coordinate given the first equal to the first, almost everywhere under the joint law. Atomic, singular, and singleton laws are included. No strict endpoints, density, supplied coupling, finite support, uniqueness, sampling algorithm, process extension, or novelty claim is asserted.

The construction passes through generalized quantiles and stop-loss inequalities, finite majorization and Birkhoff, genuine finite-Dirac joint laws, conditional-mean quantile-bin approximation preserving convex order, compact weak-limit extraction preserving both marginals, and extension from continuous to bounded Borel martingale tests. The native conditional-expectation bridge consumes coordinate integrability derived from the compact marginal laws.

Historical background is Volker Strassen, *The existence of probability measures with given marginals*, Annals of Mathematical Statistics 36 (1965), 423–439, DOI https://doi.org/10.1214/aoms/1177700153; institutional copy: https://www1.cmc.edu/pages/faculty/MONeill/Math%20138/papers138/Strassen.pdf. Printed pages 433–435 (PDF pages 11–13) contain the sequence/global-concavity Theorem 8 and the two-marginal conditional-expectation existence argument with bounded-continuous test equations. That passage is not a verbatim statement of the interval-local native host theorem, and the full original proof is not claimed to have been audited. Hirsch and Roynette (2012), DOI https://doi.org/10.1051/ps/2011164, is additional background. The Lean source above supplies the ported proof.
