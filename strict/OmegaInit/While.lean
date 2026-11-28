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
port_definition Lean.Loop._sizeOf_1
port_definition Lean.Loop._sizeOf_inst
attribute [instance] Omega.Lean.Loop._sizeOf_inst
port_proof Lean.Loop.mk.sizeOf_spec by_reflexivity

/- At the identity monad, repeatM on an always-continuing step supplies an
element of any nonempty type, as proved by choiceFromRepeatM.

Lean.Loop.forIn and Lean.instForInLoopUnitOfMonad must obey the pinned
fixed-point equation when a fixed point exists. On the exception computation
in OmegaChecks.InitBoundaries.WhileChoice, this behavior yields Classical.choice
through choiceFromLoop and choiceFromInstance. The statements
repeatM.Internal.eq_of_monadTail and Lean.Loop.forIn_eq_of_monadTail use
these operations at their original public types.

Classical.choice.congr_simp and Exists.choose.congr_simp have equality endpoints
that apply their selectors to a nonempty type or an existential proof.
OmegaChecks.InitBoundaries.ChoiceOperands checks the pinned selector applications. -/
