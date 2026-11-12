# Finite-dimensional multilinear continuity

The private `D5.S3.Quantum.AsynchronousMassRigidity.continuous_of_finiteDimensional`
in `D5/S3/Quantum/Analysis/AsynchronousMassRigidity.lean` is a transplant of
`MultilinearMap.continuous_of_finiteDimensional` from
[TauCeti/Topology/Algebra/Module/FiniteDimension.lean](https://github.com/TauCetiProject/TauCeti/blob/66f3330c1cbabafd0f5b3ea4a646c43e23105ee2/TauCeti/Topology/Algebra/Module/FiniteDimension.lean).
Its full general statement and proof are retained. Its namespace and visibility
are adapted to the owning module. Both extrema in `constant_on_normalized_cube`
use it directly; it supplies no independent mathematical novelty claim.

Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors.

The complete immutable supplier tree contains `LICENSE` and no `NOTICE`.
The full [Apache-2.0 license](TauCeti-LICENSE.txt) is retained with SHA256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`.
The source file retains its copyright, license and authorship notice.

The supplier pins `leanprover/lean4:v4.35.0-rc3` and Mathlib
`f6090c7095e1e56b3464c1daba5f24631f1290d2`. The consuming repository pins
`leanprover/lean4:v4.35.0` and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
The transplanted proof uses only the consuming repository's resolved imports;
no supplier package dependency or global pin change is required.

Retire the transplant when an equivalent finite-dimensional multilinear
continuity declaration is present in the Mathlib revision resolved by this
repository's own `lake-manifest.json`, replacing both extrema's calls with
direct applications of that declaration. The check is against the resolved
local Mathlib source and compiled type, including every field, topology,
finite-dimensionality and codomain hypothesis.
