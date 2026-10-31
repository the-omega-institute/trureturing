---
bibkey: toobysmith2026phasepolynomial
authors: Joseph Tooby-Smith
year: 2026
title: "Physlib charge balance and infinite-order unitary phase"
doi: null
url: https://github.com/leanprover-community/physlib/tree/a8823c76303bab825824ddecb7bd540880c4ae62/PhyslibAlpha/Particles/BeyondTheStandardModel/TwoHDM
claim: "Generic diagonal coefficient rescaling, charge balancing, and existence of an infinite-order complex unitary phase."
strata_touched:
  - D5/S3/Quantum/Algebra/CommonPhasePolynomial
license: Apache-2.0
triage: anchor
---

# Diagonal charge balancing

`ChargeBalance.lean` supplies `MvPolynomial.coeff_aeval_diag` over any commutative ring and
`MvPolynomial.coeff_eq_zero_of_charge_ne_zero` over any field. The latter assumes a nonzero
scalar with no nontrivial integer power equal to one and formal invariance under the specified
diagonal substitution. It concludes that a monomial of nonzero integral charge has zero coefficient.

`Invariants.lean` supplies `TwoHiggsDoublet.EffectivePotential.exists_infiniteOrder_unitary`.
Its other generation theorem concerns six variables, two charge constraints and five generators;
it does not supply unrestricted complex-coordinate quadratic generation.

The pinned source uses Lean 4.35.0 and Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
The three leaf proofs retain their original copyright and the full Apache-2.0 license in
`docs/reports/licenses/physlib-phase-polynomial-LICENSE.txt`. No NOTICE file occurs in the
pinned source tree. The transplants retire when equivalent declarations are available in this
repository's pinned Mathlib, and consumers then use those declarations directly.

## Verified locator

https://github.com/leanprover-community/physlib/tree/a8823c76303bab825824ddecb7bd540880c4ae62/PhyslibAlpha/Particles/BeyondTheStandardModel/TwoHDM
