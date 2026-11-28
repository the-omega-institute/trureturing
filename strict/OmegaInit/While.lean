/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import OmegaInit.Core
public import OmegaInit.Classical
public import OmegaInit.SizeOf

port_definition repeatM.body.match_1 with_native_code
port_definition repeatM.body with_native_code
port_native_records Lean.Loop
port_definition Lean.Loop.ctorIdx with_native_code
port_definition Lean.Loop.noConfusionType
port_definition Lean.Loop.noConfusion
port_definition Lean.Loop.forIn.match_1 with_native_code
namespace Omega.Lean.Loop

@[expose] public def _sizeOf_1 (loop : Omega.Lean.Loop) : Nat :=
  match loop with
  | .mk => 1

public instance _sizeOf_inst : Omega.SizeOf Omega.Lean.Loop :=
  Omega.SizeOf.mk _sizeOf_1

end Omega.Lean.Loop

port_proof Lean.Loop.mk.sizeOf_spec by_reflexivity

/- At the identity monad, repeatM on an always-continuing step supplies an
element of any nonempty type, as proved by choiceFromRepeatM.

Lean.Loop.forIn and Lean.instForInLoopUnitOfMonad must obey the pinned
fixed-point equation when a fixed point exists. On the exception computation
in OmegaChecks.InitBoundaries.WhileChoice, this behavior yields Classical.choice
through choiceFromLoop and choiceFromInstance.

Classical.choice.congr_simp and Exists.choose.congr_simp have equality endpoints
that apply their selectors to a nonempty type or an existential proof.
OmegaChecks.InitBoundaries.ChoiceOperands checks the pinned selector applications. -/
