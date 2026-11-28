/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
module
prelude
public import OmegaInit.Control.Basic
public import OmegaInit.Data.List.Basic
public import OmegaInit.Data.Nat.Bitwise.Basic
import all OmegaInit.Data.Nat.Bitwise.Basic

port_definition List.mapM.match_1 with_native_code
port_definition List.mapM.loop._f
port_definition List.mapM.loop
port_structural_code List.mapM.loop on_arg 6
port_definition List.mapM with_native_code
port_definition List.forM.match_1 with_native_code
port_definition List.forM._f
port_definition List.forM
port_structural_code List.forM on_arg 4
port_definition List.mapA._f
port_definition List.mapA
port_structural_code List.mapA on_arg 6
port_definition List.forA._f
port_definition List.forA
port_structural_code List.forA on_arg 4

port_definition List.zipWithM._sparseCasesOn_1
port_definition List.zipWithM.match_1 with_native_code
port_definition List.zipWithM.loop._f
port_definition List.zipWithM.loop
port_structural_code List.zipWithM.loop on_arg 7
port_definition List.zipWithM with_native_code

port_definition List.filterAuxM._f
port_definition List.filterAuxM
port_structural_code List.filterAuxM on_arg 5
port_definition List.filterM with_native_code
port_definition List.filterRevM with_native_code
port_definition List.filterMapM.match_1 with_native_code
port_definition List.filterMapM.loop._f
port_definition List.filterMapM.loop
port_structural_code List.filterMapM.loop on_arg 6
port_definition List.filterMapM with_native_code
port_definition List.flatMapM.match_1 with_native_code
port_definition List.flatMapM.loop._f
port_definition List.flatMapM.loop
port_definition List.flatMapM

port_definition List.foldlM.match_1 with_native_code
port_definition List.foldlM._f
port_definition List.foldlM
port_structural_code List.foldlM on_arg 7
port_proof List.foldlM_nil by_reflexivity
port_proof List.foldlM_cons by_reflexivity
port_definition List.foldrM with_native_code
port_proof List.foldrM_nil by_reflexivity

port_definition List.firstM._f
port_definition List.firstM
port_structural_code List.firstM on_arg 6
port_definition List.anyM._f
port_alternative_definition List.anyM from OmegaChecks.InitPort.Alternatives.BoolSearch with_recursor_code
port_definition List.allM._f
port_alternative_definition List.allM from OmegaChecks.InitPort.Alternatives.BoolSearch with_recursor_code

port_definition List.findM?._f
port_alternative_definition List.findM? from OmegaChecks.InitPort.Alternatives.BoolSearch with_recursor_code
port_definition List.findSomeM?._f
port_definition List.findSomeM?
port_structural_code List.findSomeM? on_arg 6
port_definition List.findSomeM?_cons.match_1 with_native_code
port_proof List.findSomeM?_nil by_reflexivity
port_proof List.findSomeM?_cons by_reflexivity

port_definition List.forIn'.loop.match_1 with_native_code
port_definition List.forIn'.loop.match_3 with_native_code
port_definition List.forIn'.loop.match_5 with_native_code
port_proof List.forIn'._proof_1
port_proof List.forIn'._proof_2
port_proof List.forIn'._proof_3
port_definition List.forIn'.loop._f
port_definition List.forIn'.loop
port_structural_code List.forIn'.loop on_arg 7
port_definition List.forIn' with_native_code
port_definition List.instForIn'InferInstanceMembershipOfMonad with_native_code
port_proof List.forIn'_eq_forIn' by_reflexivity
port_proof List.forIn'_nil by_reflexivity
port_proof List.forIn_nil by_reflexivity
port_definition List.instForMOfMonad with_native_code
port_proof List.forM_eq_forM by_reflexivity
port_proof List.forM_nil by_reflexivity
port_proof List.forM_cons by_reflexivity
port_definition List.instFunctor with_native_code
attribute [instance] Omega.List.instForIn'InferInstanceMembershipOfMonad Omega.List.instForMOfMonad Omega.List.instFunctor

/- Open: the pinned proof of List.findM?_eq_findSomeM? uses bind_map_left and
function extensionality. Even on [()] its statement equates the reader that branches directly on the Boolean
with the reader that first tags the result with Option. -/
