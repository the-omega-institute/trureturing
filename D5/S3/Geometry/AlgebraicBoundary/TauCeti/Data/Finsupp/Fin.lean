/- GID: D5/S3/Geometry/AlgebraicBoundary/TauCeti/Data/Finsupp/Fin
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/TauCeti/Data/Finsupp/Fin
   mirror-E: none(waiver:external-source-adaptation)
   anchors: []
   utility: none
   digest: Pinned TauCeti real algebraic dependency for entire boundary recovery. -/

/- Source: TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/Data/Finsupp/Fin.lean.
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

public import Mathlib.Data.Finsupp.Fin
public import Mathlib.Data.Finsupp.Lex
public import Mathlib.Order.Fin.Tuple

/-!
# `Finsupp.cons`, `Finsupp.snoc` and their lexicographic comparison

`Finsupp.cons x s : Fin (n + 1) →₀ M` puts `x` in front of `s`. Adding two of them adds heads and
tails separately. The lexicographic order compares the entries at `0` first, so two of them are
compared by their heads, and then by their tails.

Dually, `Finsupp.snoc s x : Fin (n + 1) →₀ M` appends `x` after `s`, and `Finsupp.init t` forgets
the last entry of `t`; these are the `Finsupp` versions of `Fin.snoc` and `Fin.init`. Adding two
such vectors adds initial parts and last entries separately. Two such vectors are compared
lexicographically by their initial parts first, and then by their last entries.
-/

public section

namespace Finsupp

variable {n : ℕ} {M : Type*}

section Snoc

variable [Zero M]

end Snoc

end Finsupp
