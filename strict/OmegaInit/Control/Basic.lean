/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import OmegaInit.Core

@[expose] public section

port_native_records Alternative, ToBool, ForM
namespace Omega
export ForM (forM)
end Omega

port_definition instForInOfForIn' with_native_code
attribute [instance 500, default_instance] Omega.instForInOfForIn'
port_definition Functor.mapRev with_native_code
port_definition Functor.discard with_native_code
port_definition instOrElseOfAlternative with_native_code
port_definition Bind.kleisliLeft with_native_code
port_definition Bind.kleisliRight with_native_code
port_definition Bind.bindLeft with_native_code
port_definition ForInStep.value.match_1 with_native_code
port_definition ForInStep.value with_native_code
port_definition optional with_native_code
port_definition guard with_native_code
port_definition instToBoolBool with_native_code

port_native_records MonadControl, MonadControlT
port_definition instMonadControlTOfPure with_native_code
port_definition instMonadControlTOfMonadControl with_native_code
port_definition controlAt with_native_code
port_definition control with_native_code
