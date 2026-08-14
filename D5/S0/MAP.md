# D5 S0 Map

## Split history

- 2026-08-14 (SL-003): `Carrier/` reached its 12-Lean-file limit. The
  branch-new `IntegerPowerNorm` module opened the `Carrier/Powers/` bucket;
  all existing `Carrier/` paths remain unmoved.
- 2026-08-14 (SL-003): `Diagonal/` reached its 12-Lean-file limit. The
  branch-new `Probability/EquivariantEscape.lean` module opened the split-only
  `Diagonal/Probability/` bucket; all existing `Diagonal/` paths remain unmoved.
- 2026-08-14 (SL-003): `Asymptotics/` was at its 12-Lean-file limit. The
  branch-new `Interference/FiniteAutocorrelation.lean` module opened the first
  split-only `Asymptotics/Interference/` bucket; all existing `Asymptotics/`
  paths remain unmoved.
- 2026-08-14 (SL-003): with `Asymptotics/` still at its 12-Lean-file limit, the
  branch-new `MetricGeometry/GreenClassDiameter.lean` module opened its second
  split-only bucket; all existing `Asymptotics/` paths remain unmoved.
- 2026-08-15 (SL-003): with `Asymptotics/` still at its 12-Lean-file limit, the
  source-complete `WeightedProbability/SkewedCaptureBounds.lean` deposit opened
  its third split-only bucket; all existing `Asymptotics/` paths remain unmoved.

## Buckets

- `Asymptotics/`: asymptotic bounds for finite-listing weights and exclusion of
  nonzero limiting phases.
- `Asymptotics/Interference/`: exact finite autocorrelation identities for
  interference profiles.
- `Asymptotics/MetricGeometry/`: metric and measure laws for finite and limiting
  Green classes.
- `Asymptotics/WeightedProbability/`: exact finite product-distribution laws
  for weighted twisted-diagonal capture and escape events.
- `Carrier/`: the golden integer carrier, conjugation, norm, and units.
- `Carrier/Powers/`: integer powers of distinguished golden units and their norm
  transport.
- `Conventions/`: canonical W-digit and notation conventions.
- `Diagonal/`: finite diagonal constructions and exact escape counts.
- `Diagonal/Probability/`: uniform probability laws for finite diagonal and
  equivariant escape events.
- `History/`: finite marker and event histories with faithful encodings.
- `Rewriting/`: terminating rewrite relations, confluence, and normal forms.
