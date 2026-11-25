/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude

public import OmegaMath.Algebra.Group.Operations

@[expose] public section

namespace Omega

/-- A difference in an additive group vanishes exactly when its terms are equal. -/
theorem sub_eq_zero {A : Type u} (G : AddGroup A) (laws : G.Laws) {a b : A} :
    Iff (Eq (G.sub a b) G.zero) (Eq a b) :=
  Iff.intro
    (fun vanishes => (AddGroup.subAddCancel laws a b).symm.trans
      ((congrArg (fun value => G.add value b) vanishes).trans (laws.right.left b)))
    (fun equal => Eq.subst (fun value => Eq (G.sub a value) G.zero) equal
      (AddGroup.addNegCancel laws a))

/-- A difference in an additive group is nonzero exactly when its terms differ. -/
theorem sub_ne_zero {A : Type u} (G : AddGroup A) (laws : G.Laws) {a b : A} :
    Iff (Not (Eq (G.sub a b) G.zero)) (Not (Eq a b)) :=
  Iff.intro
    (fun nonzero equal => nonzero ((sub_eq_zero G laws).mpr equal))
    (fun different vanishes => different ((sub_eq_zero G laws).mp vanishes))

end Omega
