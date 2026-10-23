---
bibkey: tauceti2026gaussianpolynomial
authors: The Tau Ceti contributors; Rémy Degenne
year: 2026
title: Gaussian-polynomial totality through exponential-moment determinacy
doi: null
url: https://github.com/TauCetiProject/TauCeti/tree/f749c1bb6b118c898f8d152e8ff9ad3d2b339dfd
claim: Gaussian-polynomial tests at every positive width detect every complex Lebesgue L2 vector without a decay assumption on that vector.
strata_touched:
  - D5/S3/Quantum/Analysis/Hermite/GaussianPolynomialTotality
  - D5/S3/Quantum/Analysis/Hermite/PhysicalProductTotality
license: Apache-2.0
triage: anchor
---

# Gaussian-polynomial totality construction

Source: The Tau Ceti contributors, TauCetiProject/TauCeti,
revision `f749c1bb6b118c898f8d152e8ff9ad3d2b339dfd` (Apache-2.0).

The retained source is adapted from:

- `TauCeti/Probability/Moments/Determinacy.lean`;
- `TauCeti/Probability/Moments/VanishingMoments.lean`;
- `TauCeti/Probability/Distributions/Gaussian/PolynomialMemLp.lean`.

The complex-MGF strip argument in Determinacy credits Mathlib's
`Mathlib/Probability/Moments/ComplexMGF.lean`, copyright 2025 Rémy Degenne.
That attribution is retained with the Tau Ceti copyright in the adapted source.
The full Apache-2.0 license is in
`docs/reports/hermite-suppliers/tauceti-LICENSE.txt`.
The exact donor source tree contains no file with NOTICE in its name.

The donor uses Lean `v4.35.0-rc3` and Mathlib
`b63f6e8a68d220e3b3bc4f3792bb53650d375f24`.
This repository uses Lean `v4.33.0` and Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`.
The adapted port retains the original analytic and positive/negative density
construction as local proof steps in the actual Lebesgue Gaussian-polynomial
totality theorem. It introduces no separate moment-determinacy or normalization
statements, and makes no originality claim for the donor argument.

At a future Mathlib pin of this repository, retire the port when an exact direct
application proves the same totality statement for every positive Gaussian width
and the actual Hermite and physical-graph consumers still validate with the port
removed. Upstream acceptance at another pin is insufficient.

## Verified locator

https://github.com/TauCetiProject/TauCeti/tree/f749c1bb6b118c898f8d152e8ff9ad3d2b339dfd

Attributed donor source scope at this revision:

- `TauCeti/Probability/Moments/Determinacy.lean`;
- `TauCeti/Probability/Moments/VanishingMoments.lean`;
- `TauCeti/Probability/Distributions/Gaussian/PolynomialMemLp.lean`.

## Physical product Hermite totality

The physical product receiver uses the local product continuity, finite-volume
rectangle, pi-lambda and sigma-finite separation argument adapted from these
files at the same immutable Tau Ceti revision:

| Selected donor file | SHA-256 |
| --- | --- |
| `TauCeti/Analysis/InnerProductSpace/L2/Pi.lean` | `f47108bdeda7269a68753776780231637797c34cf34ee30574ad1d42f6516fab` |
| `TauCeti/MeasureTheory/Integral/PiSystem.lean` | `53354d6de311b699666837e84b94fd7b055c229992df9b89198992e3f2b70682` |

For every natural dimension, including zero, every positive hbar and positive
coordinate mass and frequency, the receiver uses the actual physical Hermite
functions of theorem 31.1 in
`docs/develop/theory/SYMPLECTIC_PREDICTIVE_COMPLETION.md`. Their physical length
is sqrt(hbar/(mass times frequency)); their Hermite convention is probabilists'
Hermite, evaluated at sqrt(2) times the coordinate divided by that length. Each
coordinate factor includes its Gaussian and factorial/pi normalization.

Every natural multi-index supplies a function in actual complex Euclidean
Lebesgue L2. For any complex L2 vector, vanishing of all displayed mode pairings
implies that the vector is zero almost everywhere. The factors are real numbers
embedded in Complex, so multiplication by a physical mode agrees with the
conjugate-first-slot pairing. In dimension zero the empty product is the constant
one and the actual volume is the Dirac measure. No physical completeness
assumption or abstract Hilbert basis replaces the displayed functions.

The receiving proof constructs the one-dimensional density from the established
Gaussian-polynomial result, extends the pairing continuously through finite
product tests, separates finite-volume rectangles and measurable sets, and
returns to Euclidean volume through its actual measure-preserving coordinate
equivalence. The source retains the Tau Ceti copyright and Apache-2.0 license;
the adaptation makes no research originality claim.

Receiving source:
[PhysicalProductTotality.lean](../../D5/S3/Quantum/Analysis/Hermite/PhysicalProductTotality.lean),
`D5.S3.Quantum.Analysis.Hermite.PhysicalProductTotality.physical_product_totality`.

At a future Mathlib pin of this repository, retire the product-totality port when
a direct application supplies this actual all-dimension, all-positive-parameter
totality statement and its actual consumers validate after the port is removed.
A donor result at another pin does not satisfy that test. The totality statement
does not supply an orthonormal-integral theorem, eigenoperator action, operator
core, tensor operator domain, metaplectic transport, normal-state second moments,
Gibbs trace, or completion of the original theorem 2.4.
