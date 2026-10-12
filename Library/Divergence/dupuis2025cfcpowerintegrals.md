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

Pinned Mathlib Order lists operator power convexity on [1,2] as a TODO.
This is a Mathlib scope boundary, not a missing third-party supplier:
Physlib revision `b9043cc548ef6d63a28454cf3a57fb12a0c2e142` already supplies
`LownerHeinzCore.power_Icc_one_two_operatorConvexOn_Ici` and its integral
proof. The local consumed proof uses that attributed source, with
`CStarAlgebra.convexOn_ringInverse_algebraMap_add` as its shifted-inverse
input. Its upstream integral uses the entire kernel x times
rpowIntegrand01(q,t,x), q=p-1, rather than the alternative compensated
rpowIntegrand12 representation described above. The exact source mapping
and assumptions are in `tsukamotomoriyamasaki2026lieb.md`.
The closed endpoints, arbitrary complete ordered C-star scope and uniform
all-Hilbert Jensen condition are retained; no independent general power
convexity proof is claimed.

The referenced Mathlib source credits Frédéric Dupuis and is Apache-2.0;
the shifted inverse proof is in the same pinned Rpow/RingInverseOrder module.
The mathematical operator convexity result and the integral method are
classical. The Mathlib source cites Eric A. Carlen, *Trace inequalities and
quantum entropies: An introductory course*, Lemma 2.8. No mathematical
originality or completion of Hiai Problem 5.18 is claimed.

## Verified locator

https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/IntegralRepresentation.lean

Declarations `Real.exists_measure_rpow_eq_integral_rpowIntegrand₁₂` and
`CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₁₂` locate the
compensated whole-kernel representations described above. The shifted
inverse convexity input is
`CStarAlgebra.convexOn_ringInverse_algebraMap_add` in the same pinned
`Rpow/RingInverseOrder.lean` source:

https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/RingInverseOrder.lean
