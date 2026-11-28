/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
module
prelude
public import OmegaInit.Data.Option.Basic

port_definition Option.instMembership with_native_code
port_proof Option.pbind._proof_1 by_reflexivity
port_definition Option.forM.match_1 with_native_code
port_definition Option.forM with_native_code
port_definition Option.instForMOfMonad with_native_code
port_definition Option.instForIn'InferInstanceMembershipOfMonad.match_1 with_native_code
port_definition Option.instForIn'InferInstanceMembershipOfMonad.match_3 with_native_code
port_definition Option.instForIn'InferInstanceMembershipOfMonad with_native_code

attribute [instance] Omega.Option.instMembership Omega.Option.instForMOfMonad Omega.Option.instForIn'InferInstanceMembershipOfMonad
