/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import OmegaInit.Prelude

port_proof cond.eq_1 by_reflexivity
port_proof cond.eq_2 by_reflexivity

public section
namespace Omega.cond
export _root_.cond (eq_1 eq_2)
end Omega.cond
