/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module
prelude
public import OmegaInit.Control.Id

noncomputable section

@[expose] public section

namespace Omega

abbrev ReaderM (ρ : Type u) := ReaderT ρ Id

end Omega
