/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude

public import OmegaInit.Data.Function

/-!
Cantor's diagonal argument from `Mathlib.Logic.Function.Basic`.
-/

namespace Omega.Function

/-- No function from a type to its predicates is surjective. -/
public theorem cantor_surjective {α : Type u} (f : α → α → Prop) :
    Not (Surjective f) :=
  fun surjective =>
    let diagonal := fun a => Not (f a a)
    (surjective diagonal).elim fun a ha =>
      have pointwise := congrArg (fun predicate : α → Prop => predicate a) ha
      have refute : Not (f a a) := fun haa =>
        (Eq.subst (motive := fun p : Prop => p) pointwise haa) haa
      refute (Eq.subst (motive := fun p : Prop => p) pointwise.symm refute)

end Omega.Function
