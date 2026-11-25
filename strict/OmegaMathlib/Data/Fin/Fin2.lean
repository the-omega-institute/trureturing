/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module
prelude
public import OmegaInit.Prelude

/-! The inductively presented finite ordinals from `Mathlib.Data.Fin.Fin2`. -/

@[expose] public section

namespace Omega

/-- Inductively presented natural numbers below a bound. -/
inductive Fin2 : Nat → Type where
  | fz {n} : Fin2 (Nat.succ n)
  | fs {n} : Fin2 n → Fin2 (Nat.succ n)

end Omega

-- Generated standard references (portable.py --regenerate-facades).
public section
namespace OmegaMathlib
export _root_.Omega (Fin2)
end OmegaMathlib
namespace OmegaMathlib.Fin2
export _root_.Omega.Fin2 (fs fz rec recOn)
end OmegaMathlib.Fin2
end
-- End generated standard references.
