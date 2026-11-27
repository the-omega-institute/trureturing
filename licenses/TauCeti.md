# Tau Ceti source attribution

The homogeneous Hoffman error bound and its live prerequisites are adopted from
[The Tau Ceti contributors, TauCeti](https://github.com/TauCetiProject/TauCeti/tree/557dcf0fc5cc930bb3dd80a7f1aff6d8f2288647),
commit `557dcf0fc5cc930bb3dd80a7f1aff6d8f2288647`.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
The complete Apache License 2.0 is retained in
[the license text](../docs/reports/TauCeti-Apache-2.0.txt).
The immutable source tree has no separate NOTICE file.

| Local source | Upstream source |
| --- | --- |
| `src/OmegaMath/Geometry/Convex/Cone/ErrorBound.lean` | `TauCeti/Geometry/Convex/Cone/ErrorBound.lean` |
| `src/OmegaMath/Geometry/Convex/Cone/Alternative.lean` | `TauCeti/Geometry/Convex/Cone/Alternative.lean` |
| `src/OmegaMath/LinearAlgebra/LinearMap/PseudoInverse.lean` | `TauCeti/LinearAlgebra/LinearMap/PseudoInverse.lean` |

Modifications comprise local module imports, the official Mathlib backend marker,
Lean 4.35 compatibility, and omission of unused Gordan, Stiemke and integer results.
The original proof ownership and mathematical assumptions are preserved.
These are existing mathematical results, with no claim of mathematical novelty.

Retirement condition: when this repository's pinned Mathlib revision supplies
an equivalent homogeneous error-bound theorem with the same ordered-field,
finite-family and finite-dimensional hypotheses, remove the corresponding port
and directly use that pinned declaration. Remove prerequisites when no live
consumer remains. Compatibility is checked against this repository's actual pin.
