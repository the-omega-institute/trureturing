---
bibkey: sakamoto2026regularized
authors: Hiroki Sakamoto; Kazuhiro Sato
year: 2026
title: Data-Driven Regularized Time-Limited h2 Model Reduction from Noisy Impulse Responses
doi: null
url: https://arxiv.org/abs/2601.08372v2
claim: A finite-horizon discrete-time reduction objective and its gradient can be expressed using noisy impulse responses with a specified regularizer.
strata_touched:
  - D5/S3/Quantum/Dynamics/HamiltonianEffectCompletionGenerator
license: citation-only
triage: anchor
---

# Noisy impulse-response reduction

## Version and locator

The full HTML at https://arxiv.org/html/2601.08372v2 was checked. It identifies version 2, dated 30 April 2026. The title and noise-regularization formulation differ from the earlier version, so this note binds v2.

Relevant locations are Sections III–IV, Problem 1, equations (23)–(40), Theorem 1, and Theorem 2. The latter assumes bounded iterates and states convergence to a stationary point. It is not a statement of global optimization over arbitrary reduced models.

## Dependency boundary

Section 14 of the unified theory uses this as prior art for directly learning a finite-horizon objective. Its supervised records pair an initial feature with a later state target, whereas the source uses impulse responses of a discrete-time input-output system. Neither experiment is silently substituted for the other.

The repository's fixed-reference spectral optimizer has additional canonical constraints. Its matrix concentration argument requires its own independence and boundedness conditions. The source's reported SLICOT results are not repository measurements; its algorithm has not been run here.
