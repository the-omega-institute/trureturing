/-
Copyright (c) 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
module
prelude
import all OmegaInit.Prelude
public import OmegaInit.Data.Fin.Basic

port_definition Fin.foldl.match_1
public theorem Omega.Fin.foldl._proof_1 (n : Nat) : Omega.NeZero (Nat.add n 1) :=
  @Omega.instNeZeroNatHAdd_1 n 1 (@Omega.Nat.instNeZeroSucc Nat.zero)
port_definition Fin.foldl._f
port_definition Fin.foldl
port_structural_code Fin.foldl on_arg 2
port_proof Fin.foldl.eq_1
port_proof Fin.foldl.eq_2
port_proof Fin.foldl_zero
port_proof Fin.foldl_succ

/- The four function equations below are characterized in
OmegaChecks.InitInventory.TransformerLaws.FiniteFold. At a common universe u
each is equivalent to extensionality for maps T → T for every T : Type u.

Fin.foldlM_succ_last at length one equates binding a callback to pure with
binding pure to the callback. Its equivalence is iffLeftSuccessor.

Fin.foldrM_succ at length one gives the same equality for a callback run from
the right. Its equivalence is iffRightSuccessor.

Fin.foldlM_add at lengths one and zero equates one final bind to pure with two.
Its equivalence is iffLeftAddition.

Fin.foldrM_add at lengths zero and one equates one final bind to pure with two
in the right fold. Its equivalence is iffRightAddition.

For a fixed accumulator α and lawful monad m, all four equations follow
at arbitrary universe levels from extensionality for the maps α → m α. -/
