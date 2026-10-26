---
bibkey: tauceti2026metricvariation
authors: The Tau Ceti contributors
year: 2026
title: Total variation and the metric speed of absolutely continuous curves
doi: null
url: https://github.com/TauCetiProject/TauCeti/blob/49035f0ebf0e506dc2f1c078374b2dea4ac9c6dd/TauCeti/MeasureTheory/Function/MetricDerivative/Variation.lean
claim: An integral density controlling every endpoint distance controls the total metric variation; the source also develops metric-derivative variation identities for AC curves.
strata_touched:
  - D5/S3/Geometry/Metric/MetricACSpeed
license: Apache-2.0
triage: anchor
---

# Metric variation and an integral chord bound

The immutable source is TauCeti revision
`49035f0ebf0e506dc2f1c078374b2dea4ac9c6dd`,
`TauCeti/MeasureTheory/Function/MetricDerivative/Variation.lean`.
Its theorem `eVariationOn.le_lintegral_of_edist_le_lintegral` applies to
arbitrary pseudometric extended spaces, curves and nonnegative extended
integral densities. If the density integral bounds every pair of endpoints
in a closed real interval, it bounds the total variation on that interval.
The proof sums adjacent half-open interval integrals over arbitrary monotone
partitions and uses measure monotonicity.

The receiving `MetricACSpeed.lean` preserves this proof as the private,
consumed `variation_le_lintegral_of_edist_le_lintegral`. Its only changes are
the canonical header, private name and surrounding namespace. It is used in
the actual metric-speed/variation proof. The upstream copyright and full
Apache-2.0 license are embedded in the receiving Lean source. The upstream
root contains no NOTICE file at this revision.

The source uses `leanprover/lean4:v4.36.0-rc1`; the receiving repository uses
`leanprover/lean4:v4.35.0` and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The differing toolchains exclude
the dependency form under spec A17.2. This is a leaf proof port, with no pin
or package change. Retire it when the receiving repository's own pinned
Mathlib contains the corresponding general chord-integral variation bound
and the metric-speed consumer validates by direct reuse after its removal.

The public receiving bridge uses a supplied almost-everywhere metric-speed
limit and the already canonical absolutely continuous variation primitive.
It proves integrability, derivative identity and exact subinterval variation
for that same speed. The source's broader metric-derivative existence
infrastructure is not imported or reimplemented. This citation makes no
research originality claim for the classical variation identity.
