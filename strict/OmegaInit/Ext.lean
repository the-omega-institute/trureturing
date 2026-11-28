/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Mario Carneiro
-/
module
prelude
public import OmegaInit.Core

port_proof PUnit.ext_iff
port_proof Unit.ext by_reflexivity

public section
namespace PUnit
export _root_.Omega.PUnit (ext_iff)
end PUnit
namespace Unit
export _root_.Omega.Unit (ext)
end Unit

port_alternative_proof Thunk.ext from OmegaChecks.InitPort.Alternatives.Logic
port_proof Thunk.ext_iff

namespace Thunk
export _root_.Omega.Thunk (ext ext_iff)
end Thunk
