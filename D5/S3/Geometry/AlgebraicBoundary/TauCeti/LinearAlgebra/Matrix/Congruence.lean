/- GID: D5/S3/Geometry/AlgebraicBoundary/TauCeti/LinearAlgebra/Matrix/Congruence
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/TauCeti/LinearAlgebra/Matrix/Congruence
   mirror-E: none(waiver:external-source-adaptation)
   anchors: []
   utility: none
   digest: Pinned TauCeti real algebraic dependency for entire boundary recovery. -/

/- Source: TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/LinearAlgebra/Matrix/Congruence.lean.
Adaptation: ordinary D5 import routes; selected declarations retain their original proofs.
License: docs/reports/licenses/TauCeti-LICENSE.txt. Original copyright notices follow.
Retire each transplanted declaration when the actual pinned mathlib supplies an equivalent
statement, and replace its consumers by direct imports and applications of that pinned owner.
This adaptation contributes no independent mathematical novelty or escape credit. -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Traces and determinant pencils under rectangular congruence

For a rectangular matrix `M`, congruence `A ↦ M * A * Mᵀ` can be moved across a trace pairing
or a determinant pencil `det (1 + c • (B * _))` by congruating the test matrix `B` with the
transpose instead. These identities transport Wishart trace transforms along congruence.

The retained source supplies the useful proof dependencies. Further exact applications,
including their assumptions and boundary cases, are developed in the owning Blueprint.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley, 1982, chapters 2–3.
-/

public section

namespace Matrix

end Matrix
