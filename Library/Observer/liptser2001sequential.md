---
bibkey: liptser2001sequential
authors: Robert S. Liptser and Albert N. Shiryaev
year: 2001
title: Statistics of Random Processes
doi: 10.1007/978-3-662-13043-8
url: https://doi.org/10.1007/978-3-662-13043-8
claim: Martingale localization and conditional Hellinger processes relate finite predictable energy to likelihood convergence.
strata_touched:
  - D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SequentialHellingerLocalization
license: reference-only
triage: anchor
---

# Conditional energy and localization

The reference develops likelihood ratios, changes of measure, and martingale
methods for stochastic processes. The sequential Hellinger criterion and the
localization method are classical mathematics; no novelty is claimed here.
The DOI, title, and authors are identified by the Crossref record for the
linked Springer volume. No book text or source code is reproduced.

The formal statement uses a discrete predictable energy sequence with values
in the unit interval. The cut at time n tests the energy accumulated before n.
One included increment may cross the chosen level, so the total cut energy is
bounded by that level plus one. Conditional second-moment bounds then control
centered partial sums, while conditional first-moment bounds control a
nonnegative error sum. Countably many integer levels give one full-measure
set on which both conclusions hold on every finite-energy path.

This is a common-localization formulation of the classical argument. It does
not identify trajectory densities or assert equivalence or singularity of
path laws without the additional likelihood and measure-comparison bridges.
