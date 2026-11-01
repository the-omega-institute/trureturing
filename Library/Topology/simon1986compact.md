---
bibkey: simon1986compact
authors: Jacques Simon
year: 1986
title: Compact sets in the space Lp(0,T;B)
doi: 10.1007/BF01762360
url: https://doi.org/10.1007/BF01762360
claim: Theorem 1 characterizes relative compactness in Banach-valued finite-exponent Lp by compact interval integrals and uniform internal translations.
strata_touched: []
license: citation-only
triage: anchor
---

# Interval-integral compactness and internal translations

Simon, Annali di Matematica Pura ed Applicata 146, 65–96, states an
if-and-only-if compactness criterion for Banach-valued functions. Section 3,
Theorem 1, printed page 71, assumes compactness of the integral sets only
for strictly interior subintervals, 0 < a < b < T. The finite-exponent
range includes p = 1. The sufficiency proof on pages 72–74 uses averaging
and time reversal to handle both interval ends. Remark 3.4 explains why
an interior averaging argument alone does not settle the whole interval.

The sufficiency specialization with observations on all 0 ≤ a < b ≤ T
has stronger hypotheses than Simon's original theorem. It is not the full
original equivalence. Right-closed instead of open intervals represent
the same Lebesgue almost-everywhere classes.

The same Theorem 1 also has a compactness conclusion in C(0,T;B) for
p = infinity. Section 1 defines this continuous-function space on the
closed interval [0,T], while L-infinity is a space of almost-everywhere
classes. The proof uses right means and opposite time directions. The
theorem does not separately state an arbitrary-family continuous lifting
with a common modulus and uniqueness in the absence of the integral
compactness premise. The local-window consistency and representative
construction in `IntervalLInfinityRepresentative` are derived arguments,
without an originality claim or exact separate literature attestation.

The equal-mesh estimate bounds the whole-interval power error by
2 divided by the cell width times the integral, over positive shifts
up to that width, of the internal translation power error. Its cells
include the first and last portions of the original interval. This
particular restricted-domain assembly is a derived proof route; the
compactness criterion itself is literature-attested. No optimal-constant
or mathematical originality claim is made.

The selected analytic source supplier is TauCetiProject/TauCeti revision
`ef2b35da80dbe9f123fd200fcf160a036fe69813`,
`TauCeti/MeasureTheory/Integral/Average.lean` (SHA256
`cd2ede6573aaf1c5c80fd56e048f70859a5fb94c97b9a944e33b292374af2c67`)
and `TauCeti/MeasureTheory/Function/Lp/LIntegralRpow.lean` (SHA256
`6954ce124fb51025e4afe01c0992d2afedfb83740ee5f2835471f09f6f9c4c77`).
Its Hölder and average-norm proofs are reused with original attribution.
The full Apache-2.0 license is retained at
`docs/reports/licenses/tauceti-sphere-port-LICENSE.txt`.
The source pin uses Lean 4.36.0-rc1 and a different Mathlib revision, so
these selected leaves are ports rather than a direct package dependency.
Each port is replaced by a direct application when this repository's
adopted Mathlib revision contains an equivalent declaration.

The total-boundedness transfer proof is reused from
uda-lab/leray-hopf revision `e704400f2fb2f26b2ee7f4372c3e1ecbbc82f3dc`,
`LerayHopf/Bochner/StepFunctionCompactness.lean`, SHA256
`6dcaf556f129c58d31f9ff6ba442da592723c6cbbfe6de54513951f21916f26f`.
The selected theorem is general over pseudometric spaces; its original
p = 2 mesh-compactness neighbors are not used as an all-p result.
The original Apache-2.0 license is retained at
`docs/reports/licenses/leray-hopf-interval-LICENSE.txt`.
The source pins Lean 4.31.0-rc2 and Mathlib
`15a89b2468bc01f1a6230d6e49ef5efc5286e502`; the selected proof is a port,
not a package dependency. Replace the port when this repository's adopted
Mathlib revision supplies the equivalent transfer theorem.

## Verified locator

DOI: https://doi.org/10.1007/BF01762360.
Primary publication: https://link.springer.com/article/10.1007/BF01762360.
Theorem 1 is in Section 3, printed page 71; the sufficiency proof and
boundary discussion are on printed pages 72–74, including Remark 3.4.
The consulted original PDF has SHA256
`86b81eb6be3be81afd97fd43f185f63929f552fdaaaf13ee7a9d89f6483a3db3`.
The article is cited and paraphrased; no publisher text or PDF is redistributed.

Selected Lean sources:
https://github.com/TauCetiProject/TauCeti/blob/ef2b35da80dbe9f123fd200fcf160a036fe69813/TauCeti/MeasureTheory/Integral/Average.lean
and
https://github.com/TauCetiProject/TauCeti/blob/ef2b35da80dbe9f123fd200fcf160a036fe69813/TauCeti/MeasureTheory/Function/Lp/LIntegralRpow.lean.

Uniform-approximation transfer source:
https://github.com/uda-lab/leray-hopf/blob/e704400f2fb2f26b2ee7f4372c3e1ecbbc82f3dc/LerayHopf/Bochner/StepFunctionCompactness.lean,
`LerayHopf.totallyBounded_of_uniform_approx'`.
