---
bibkey: eveson1995birkhoff
authors: S. P. Eveson and R. D. Nussbaum
year: 1995
title: An elementary proof of the Birkhoff-Hopf theorem
doi: 10.1017/S0305004100072911
url: https://sites.math.rutgers.edu/~nussbaum/Pubs/nusseveson1995.pdf
claim: The Hilbert projective contraction coefficient is the hyperbolic tangent of one quarter of the image diameter; finite positive rectangular matrices have diameter equal to the logarithm of their maximal entry cross ratio.
strata_touched:
  - D5/S3/Analytic/Convexity/BirkhoffSharpContraction
license: citation-only
triage: anchor
---

## Verified locator

S. P. Eveson and R. D. Nussbaum, *An elementary proof of the Birkhoff-Hopf theorem*,
Mathematical Proceedings of the Cambridge Philosophical Society 117(1), 31–55.
DOI: https://doi.org/10.1017/S0305004100072911.
Author original: https://sites.math.rutgers.edu/~nussbaum/Pubs/nusseveson1995.pdf.
Theorem 5.3, printed pages 48–50, supplies the sharp scalar contraction argument;
Theorem 6.2, printed page 52, gives the positive rectangular matrix diameter.
The article is cited and is not redistributed.

For a finite nonempty row type and an independently sized finite nonempty column
type, the formal result uses strictly positive real entries and strictly positive
input vectors. Its distance is the logarithm of the maximum coordinate ratio
divided by the minimum. With Theta the maximal entry cross ratio and L its positive
square root, the image diameter is log Theta and the least nonnegative global
coefficient is (L-1)/(L+1). Singleton types, rank one and proportional pairs remain
in scope. Neither a positive pair attaining the diameter nor a distinct positive
pair attaining the coefficient is claimed.

The consumed scalar and residual-vector upper proof is adapted from
https://github.com/TauCetiProject/TauCeti/tree/afa08a3ed16fb167e35de371afb1eb03fbc5913a,
files TauCeti/Analysis/SpecialFunctions/Log/BirkhoffCrossRatio.lean and
TauCeti/Data/Matrix/BirkhoffContraction.lean. Copyright (c) 2026 The Tau Ceti
contributors. Authors: The Tau Ceti contributors. The full applicable Apache-2.0
license is retained at docs/reports/licenses/tauceti-birkhoff/LICENSE.txt.
The complete source tree has a root LICENSE and no NOTICE file. The source pins
Lean v4.36.0-rc2 and Mathlib 1b1ccf4b088b32fa3f23f2de1127433254a81e1e;
the host pins Lean v4.35.0 and Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
This is source adaptation with no package or pin change. Modifications replace the
foreign pairwise-supremum metric and hyperbolic API by finite max/min distance,
maximal cross ratio, its square root, and strictly positive sharpness constructions.
Retire each adapted estimate when an equivalent statement is supplied by the
host's actual pinned Mathlib revision and directly apply that supplier.

The diameter lower proof uses positive coordinate spikes with common positive
padding. The coefficient lower proof balances a maximal minor, selects a positive
scalar secant, then fills the other coordinates by a fixed positive parameter.
Its input distance is exactly the secant parameter, independently of the padding.
These are interior approximation arguments and do not use boundary vectors as
members of the strictly positive domain.
