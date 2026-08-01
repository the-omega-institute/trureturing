# D5 S3 Map

## Split history

- 2026-07-18 (SL-003): `Weil/` reached 13 Lean files when batch-9 added
  `ZeroGeometry.lean`. The branch-new module opened the `Zeros/` bucket; all 12
  paths already present in `origin/dev` remain in place.
- 2026-08-01 (SL-003): `Blueprint/D5/S3/Arith` was at its 12-file limit.
  The branch-new `SumTwoSquares` module opened the `PrimeForms/` bucket; all
  existing `Arith/` paths remain in place.

## Buckets

- `Constants/`: canonical real constants and registered reference centers.
- `Fourier/`: entire extensions of the Weil Fourier-Laplace transform.
- `Quantum/`: finite-dimensional operator-algebra and probability structures.
- `PrimeForms/`: representations of prime numbers by integral quadratic forms.
- `Weil/`: classical zeta conventions, test functions, and explicit-formula machinery.
- `Zeros/`: zeta-zero geometry, symmetry, and local critical-line balance.
