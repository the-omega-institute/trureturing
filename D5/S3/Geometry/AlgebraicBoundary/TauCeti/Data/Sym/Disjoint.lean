/- GID: D5/S3/Geometry/AlgebraicBoundary/TauCeti/Data/Sym/Disjoint
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/TauCeti/Data/Sym/Disjoint
   mirror-E: none(waiver:external-source-adaptation)
   anchors: []
   utility: none
   digest: Pinned TauCeti real algebraic dependency for entire boundary recovery. -/

/- Source: TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/Data/Sym/Disjoint.lean.
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

public import Mathlib.Data.Multiset.Filter
public import D5.S3.Geometry.AlgebraicBoundary.TauCeti.Data.Sym.Basic
import Mathlib.Data.List.FinRange

/-!
# Tuples mapped into pairwise disjoint ranges

An ordered tuple mapped pointwise into pairwise disjoint ranges is determined by the unordered
tuple it presents. This file proves that injectivity statement and characterizes the range by
counting how many points lie in each component range. The corresponding topological open embedding
is in `TauCeti/Topology/Sym/Disjoint.lean`.

The retained source supplies the useful proof dependencies. Further exact applications,
including their assumptions and boundary cases, are developed in the owning Blueprint.

-/

public section

namespace TauCeti

namespace Sym

variable {α : Type*} {n : ℕ}

/-! ### Tuples mapped into pairwise disjoint ranges -/


end Sym

end TauCeti
