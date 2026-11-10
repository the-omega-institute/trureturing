# State approximation supplier attribution

The supplier code is distributed under the accompanying complete Apache-2.0 licenses.
Original copyright and authorship notices remain in each Lean source.
Modified files use ordinary D5 import paths. The selected declarations support the original-state GNS construction, scalar commutant, strong self-adjoint density and bounded functional-calculus truncation. Unused uniqueness, conjugation, generated-algebra, compactness and finite-dimensional operator results are omitted. Source elaboration dependencies are retained alongside the proof dependencies; this selection makes no novelty claim.
TauCeti InvariantSubspace uses Module.End.mul_apply for pointwise endomorphism multiplication.

Physicslib4: https://github.com/physicslib/physicslib4 at 2337279e729998740898c4be8f6c7d24f3e641e1.
LICENSE SHA256 cfc7749b96f63bd31c3c42b5c471bf756814053e847c10f3eb003417bc523d30; Git blob d645695673349e3947e8e5ae42332d0ac3164cd7.
The complete immutable tree has 472 entries, truncated=false, with LICENSE as its sole license-related path; no NOTICE.

TauCeti: immutable revision 23caf7311c77a86c3a20d58a0b596b6da705bd94.
LICENSE SHA256 b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1; Git blob 8dada3edaf50dbc082c9a125058f25def75e625a.
The complete immutable tree has 34411 entries, truncated=false, with license_tree_matches=[LICENSE]; no NOTICE.
Tree SHA256 d14d33a1af0321a91613ad8ce2a5cd37fdbb64e87cc3e2152811645e56daa783.

Each transplanted result is retired when the actual repository-pinned mathlib contains an equivalent statement and all consumers use that result directly.

## Source correspondence

- `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.lean` corresponds to `TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.lean`.
- `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/LocallyConvex/PointwiseConvergence.lean` corresponds to `TauCeti/Analysis/LocallyConvex/PointwiseConvergence.lean`.
- `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density.lean` corresponds to `TauCeti/Analysis/VonNeumannAlgebra/Density.lean`.
- `D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/CauchySchwarz.lean` corresponds to `Physicslib4/GNS/CauchySchwarz.lean`.
- `D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/ExtremeState.lean` corresponds to `Physicslib4/GNS/ExtremeState.lean`.
- `D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/Irreducibility.lean` corresponds to `Physicslib4/GNS/Irreducibility.lean`.

The Density source also contains selected declarations from TauCeti/Topology/Algebra/Module/Spaces/PointwiseConvergenceCLM.lean, TauCeti/Analysis/InnerProductSpace/Amplification.lean and TauCeti/Analysis/InnerProductSpace/InvariantSubspace.lean. Their original attribution headers are retained in the source.
The Irreducibility source also contains selected declarations from Physicslib4/GNS/Basic.lean and Physicslib4/GNS/Construction.lean, with their original attribution headers. The global declaration names are preserved.
The Density source also contains the selected weak-operator comparison and bicommutant declarations from TauCeti/Analysis/LocallyConvex/WeakOperatorTopology.lean and TauCeti/Analysis/VonNeumannAlgebra/Bicommutant.lean, retaining their original attribution headers.
