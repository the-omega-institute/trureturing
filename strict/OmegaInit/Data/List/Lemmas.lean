/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro,
  Kim Morrison
-/
module
prelude
public import OmegaInit.Core
public import OmegaInit.Data.List.Basic

port_proof List.exists_cons_of_ne_nil
port_proof List.head?_singleton by_reflexivity
port_proof List.tailD_eq_tail?
port_proof List.tail_eq_tailD by_reflexivity
port_proof absurd.congr_simp by_reflexivity
port_proof List.headD.eq_1 by_reflexivity
port_proof List.headD.eq_2 by_reflexivity
