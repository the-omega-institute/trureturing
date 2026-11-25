/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury G. Kudryashov
-/
module
prelude
public import OmegaInit.Data.Sum.Basic

port_proof Sum.bnot_isLeft
port_proof Sum.bnot_isRight
port_proof Sum.elim_comp_inl by_reflexivity
port_proof Sum.elim_comp_inr by_reflexivity
port_proof Sum.elim_map
port_proof Sum.exists
port_proof Sum.forall
port_proof Sum.getLeft?_map
port_proof Sum.getLeft?_swap
port_proof Sum.getRight?_map
port_proof Sum.getRight?_swap
port_proof Sum.isLeft_map
port_proof Sum.isLeft_swap
port_proof Sum.isRight_map
port_proof Sum.isRight_swap
port_proof Sum.map_map
port_proof Sum.swap_swap
port_proof Sum.getLeft?.eq_1 by_reflexivity
port_proof Sum.getLeft?.eq_2 by_reflexivity
port_proof Sum.getRight?.eq_1 by_reflexivity
port_proof Sum.getRight?.eq_2 by_reflexivity
port_proof Sum.isLeft.eq_1 by_reflexivity
port_proof Sum.isLeft.eq_2 by_reflexivity
port_proof Sum.isRight.eq_1 by_reflexivity
port_proof Sum.isRight.eq_2 by_reflexivity
