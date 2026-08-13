# D5 S0 Map

## Split history

- 2026-08-14 (SL-003): `Carrier/` reached its 12-Lean-file limit. The
  branch-new `IntegerPowerNorm` module opened the `Carrier/Powers/` bucket;
  all existing `Carrier/` paths remain unmoved.
- 2026-08-14 (SL-003): `Diagonal/` reached its 12-Lean-file limit. The
  branch-new `Probability/EquivariantEscape.lean` module opened the split-only
  `Diagonal/Probability/` bucket; all existing `Diagonal/` paths remain unmoved.

## Buckets

- `Carrier/`: the golden integer carrier, conjugation, norm, and units.
- `Carrier/Powers/`: integer powers of distinguished golden units and their norm
  transport.
- `Conventions/`: canonical W-digit and notation conventions.
- `Diagonal/`: finite diagonal constructions and exact escape counts.
- `Diagonal/Probability/`: uniform probability laws for finite diagonal and
  equivariant escape events.
- `History/`: finite marker and event histories with faithful encodings.
- `Rewriting/`: terminating rewrite relations, confluence, and normal forms.
