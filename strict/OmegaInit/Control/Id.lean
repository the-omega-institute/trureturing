/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module
prelude
public import OmegaInit.Control.MonadAttach

noncomputable section

@[expose] public section

namespace Omega

def Id (type : Type u) : Type u := type

protected def Id.run {α : Type u} (x : Id α) : α := x

end Omega

port_definition Id.instMonad with_native_code
port_definition Id.hasBind with_native_code
port_definition Id.instMonadLiftTOfPure with_native_code

port_definition Id.instOfNat._aux_1 with_native_code
port_definition Id.instOfNat with_native_code
port_proof Id.instMonadAttach._proof_1 by_reflexivity
port_definition Id.instMonadAttach with_native_code

port_definition ForIn.toArray with_native_code
port_definition ForIn.toList with_native_code
