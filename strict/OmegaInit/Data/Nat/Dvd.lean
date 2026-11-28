/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module
prelude
public import OmegaInit.Data.Nat.Div.Basic
public import OmegaInit.SimpLemmas
import OmegaInit.Data.Nat.Basic

port_proof Nat.dvd_zero by_constructive_casts

public section
namespace Nat
export _root_.Omega.Nat (dvd_zero)
end Nat

port_private_declaration Nat.dvd_add_iff_right.match_1_3
port_private_declaration Nat.dvd_add.match_1_1
port_proof Nat.dvd_add by_constructive_casts
port_private_declaration Nat.dvd_add_iff_right.match_1_1
port_proof Nat.dvd_add_iff_right
port_proof Nat.dvd_add_iff_left
port_proof Nat.dvd_sub_iff_left
port_proof Nat.dvd_refl by_constructive_casts
port_private_declaration Nat.le_of_dvd.match_1_1
port_private_declaration Nat.le_of_dvd.match_1_3
port_proof Nat.le_of_dvd by_constructive_casts
port_private_declaration Nat.eq_zero_of_zero_dvd.match_1_1
port_proof Nat.eq_zero_of_zero_dvd
port_private_declaration Nat.dvd_antisymm.match_1_1
port_proof Nat.dvd_antisymm
port_proof Nat.one_dvd
port_proof Nat.eq_one_of_dvd_one
port_proof Nat.dvd_one
port_proof Nat.dvd_mul_right
port_proof Nat.dvd_of_mod_eq_zero
port_private_declaration Nat.mod_eq_zero_of_dvd.match_1_1
port_proof Nat.mod_eq_zero_of_dvd
port_proof Nat.dvd_iff_mod_eq_zero
port_proof Nat.pos_of_dvd_of_pos
port_proof Nat.dvd_mul_left
port_private_declaration Nat.dvd_of_mul_dvd_mul_left.match_1_1
port_proof Nat.dvd_of_mul_dvd_mul_left
port_private_declaration Nat.dvd_sub_iff_right.match_1_3
port_private_declaration Nat.dvd_sub_iff_right.match_1_1
port_proof Nat.dvd_sub
port_proof Nat.dvd_sub_iff_right by_constructive_casts
port_private_declaration Nat.dvd_trans.match_1_1
port_proof Nat.dvd_trans by_constructive_casts
port_proof Nat.dvd_mod_iff
port_proof Nat.mul_div_cancel'
port_proof Nat.div_mul_cancel
port_proof Nat.dvd_mul_right_of_dvd
port_private_declaration Nat.mul_dvd_mul.match_1_1
port_proof Nat.mul_dvd_mul by_constructive_casts
port_proof Nat.mul_dvd_mul_left
port_private_declaration Nat.mul_div_assoc.match_1_1
port_proof Nat.mul_div_assoc
port_proof Nat.dvd_of_mul_dvd_mul_right
port_proof Nat.decidable_dvd._proof_1
port_proof Nat.zero_dvd
port_private_declaration Nat.mod_mod_of_dvd.match_1_1
port_proof Nat.mod_mod_of_dvd
port_definition Nat.decidable_dvd with_native_code
attribute [instance] Omega.Nat.decidable_dvd
port_proof Nat.dvd_mul_left_of_dvd
port_proof Nat.mul_dvd_mul_right
port_proof Nat.emod_pos_of_not_dvd by_constructive_casts

/- The public equality in Nat.dvd_eq_true_of_mod_eq_zero identifies a divisibility
   proposition with True. At m = 1 and n = 0 its premise computes to true and its
   conclusion is (∃ k : Nat, 0 = 1 * k) = True.
   Nat.dvd_eq_false_of_mod_ne_zero at m = 0 and n = 1 similarly requires
   (∃ k : Nat, 1 = 0 * k) = False. The constructive divisibility decision and
   dvd_iff_mod_eq_zero above establish the two truth values. Both proposition
   equalities remain open. -/

public section
namespace Nat
export _root_.Omega.Nat (decidable_dvd div_mul_cancel dvd_add dvd_add_iff_left dvd_add_iff_right dvd_antisymm dvd_iff_mod_eq_zero dvd_mod_iff dvd_mul_left dvd_mul_left_of_dvd dvd_mul_right dvd_mul_right_of_dvd dvd_of_mod_eq_zero dvd_of_mul_dvd_mul_left dvd_of_mul_dvd_mul_right dvd_one dvd_refl dvd_sub dvd_sub_iff_left dvd_sub_iff_right dvd_trans emod_pos_of_not_dvd eq_one_of_dvd_one eq_zero_of_zero_dvd le_of_dvd mod_eq_zero_of_dvd mod_mod_of_dvd mul_div_assoc mul_div_cancel' mul_dvd_mul mul_dvd_mul_left mul_dvd_mul_right one_dvd pos_of_dvd_of_pos zero_dvd)
end Nat
