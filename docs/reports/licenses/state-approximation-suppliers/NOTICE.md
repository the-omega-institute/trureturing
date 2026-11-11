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

- `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.lean` contains the retained block from `TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.lean`.
- `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density.lean` contains the retained blocks from `TauCeti/Analysis/LocallyConvex/PointwiseConvergence.lean`, `TauCeti/Topology/Algebra/Module/Spaces/PointwiseConvergenceCLM.lean`, `TauCeti/Analysis/InnerProductSpace/Amplification.lean`, `TauCeti/Analysis/InnerProductSpace/InvariantSubspace.lean`, `TauCeti/Analysis/VonNeumannAlgebra/Density.lean`, `TauCeti/Analysis/LocallyConvex/WeakOperatorTopology.lean` and `TauCeti/Analysis/VonNeumannAlgebra/Bicommutant.lean`.
- `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.lean` contains the retained blocks from `Physicslib4/GNS/Basic.lean`, `Physicslib4/GNS/Construction.lean`, `Physicslib4/GNS/Irreducibility.lean` and `Physicslib4/GNS/ExtremeState.lean`.

Each block retains its original attribution header and immutable supplier revision. The global declaration names are preserved. The complete licenses are [TauCeti-LICENSE.txt](TauCeti-LICENSE.txt) and [Physicslib4-LICENSE.txt](Physicslib4-LICENSE.txt).

The five rows for `omega_expand_add`, `omega_expand_smul_add`, `omega_star_swap_conj` and `cauchy_schwarz_inequality` from `Physicslib4/GNS/CauchySchwarz.lean`, and `isPositive_inner_nonneg` from `Physicslib4/GNS/Irreducibility.lean`, are historical supplier correspondences with no retained current host.
