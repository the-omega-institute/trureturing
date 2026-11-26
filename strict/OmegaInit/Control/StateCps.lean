/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import OmegaInit.Prelude

noncomputable section

@[expose] public section

namespace Omega

/-- State-passing computations expressed with a result continuation. -/
def StateCpsT (σ : Type u) (m : Type u → Type v) (α : Type u) :=
  (δ : Type u) → σ → (α → σ → m δ) → m δ

def StateCpsT.runK {α σ : Type u} {m : Type u → Type v} {β : Type u}
    (x : StateCpsT σ m α) (s : σ) (k : α → σ → m β) : m β := x β s k

end Omega
