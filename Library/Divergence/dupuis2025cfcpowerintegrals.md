---
bibkey: dupuis2025cfcpowerintegrals
authors: Frédéric Dupuis
year: 2025
title: Integral representations and order properties of spectral powers in Mathlib
doi: null
url: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/IntegralRepresentation.lean
claim: One common positive measure represents spectral powers between one and two by an integrable compensated resolvent kernel on the whole positive cone.
strata_touched:
  - D5/S3/Quantum/Lieb
license: Apache-2.0
triage: anchor
---

# Compensated power integral supplier

At the pinned Mathlib revision, the CFC representation for 1 < p < 2 supplies
one measure for every nonnegative input, with norm integrability of the
whole kernel. The real kernel is
`t^(p-1) * (t^(-1) * x + t * (t+x)^(-1) - 1)`.
Its CFC is a positive multiple of the sum of a linear term, a shifted
ring-inverse term, and a constant. The existing
`CStarAlgebra.convexOn_ringInverse_algebraMap_add` supplies the only curved
term. The three summands are not integrated separately.

The new connected convexity proof integrates the compensated kernel using
`MeasureTheory.integral_convexOn_of_integrand_ae` and the representation
`CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₁₂`.
The pinned Mathlib Order module lists operator power convexity on [1,2]
as a TODO; its existing operator concavity proof on [0,1] is the analogous
integral method, not the missing convexity theorem.
The endpoints are affinity and the noncommuting square identity. The result
applies to arbitrary complete ordered complex C-star algebras, and therefore
supplies Jensen's uniform condition on every complete complex Hilbert space.

The referenced Mathlib source credits Frédéric Dupuis and is Apache-2.0;
the shifted inverse proof is in the same pinned Rpow/RingInverseOrder module.
The mathematical operator convexity result and the integral method are
classical. The Mathlib source cites Eric A. Carlen, *Trace inequalities and
quantum entropies: An introductory course*, Lemma 2.8. No mathematical
originality or completion of Hiai Problem 5.18 is claimed.
