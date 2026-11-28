/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Robert Y. Lewis, Keeley Hoek, Mario Carneiro
-/
module

prelude
public import OmegaInit.Data.Nat.Bitwise.Basic
public import OmegaInit.Data.Nat.Basic
import OmegaInit.Data.Nat.Div.Basic

port_proof Fin.ofNat._proof_1
port_definition Fin.ofNat with_native_code
port_proof Fin.Internal.ofNat_eq_ofNat
port_proof Fin.add._proof_3
port_definition Fin.add.match_1 with_native_code
port_definition Fin.add with_native_code
port_proof Fin.addNat._proof_1
port_definition Fin.addNat with_native_code
port_proof Fin.cast._proof_1
port_definition Fin.cast with_native_code
port_proof Fin.castLE._proof_1
port_definition Fin.castLE with_native_code
port_definition Fin.castAdd with_native_code
port_definition Fin.castLT with_native_code
port_definition Fin.castSucc with_native_code
port_definition Fin.coeToNat with_native_code
port_proof Fin.pos
port_proof Fin.neg._proof_1
port_definition Fin.neg with_native_code
port_proof Fin.coe_neg
port_proof Fin.div._proof_1
port_definition Fin.div with_native_code
port_definition Fin.elim0.match_1 with_native_code
port_definition Fin.elim0
port_structural_code Fin.elim0 on_arg 2 using
  fun {α} i => False.casesOn (fun _ => α) (Omega.Nat.not_lt_zero i.val i.isLt)

port_proof Fin.exists_iff
port_definition Fin.instAdd with_native_code
port_proof Fin.land._proof_1
port_definition Fin.land with_native_code
port_definition Fin.instAndOp with_native_code
port_definition Fin.instDiv with_native_code
port_definition Fin.instOfNat with_native_code
port_definition Fin.instInhabited with_native_code
port_proof Fin.mod._proof_1
port_definition Fin.mod with_native_code
port_definition Fin.instMod with_native_code
port_proof Fin.mul._proof_1
port_definition Fin.mul with_native_code
port_definition Fin.instMul with_native_code
port_proof Fin.lor._proof_1
port_definition Fin.lor with_native_code
port_definition Fin.instOrOp with_native_code
port_proof Fin.shiftLeft._proof_1
port_definition Fin.shiftLeft with_native_code
port_definition Fin.instShiftLeft with_native_code
port_proof Fin.shiftRight._proof_1
port_definition Fin.shiftRight with_native_code
port_definition Fin.instShiftRight with_native_code
port_proof Fin.sub._proof_1
port_definition Fin.sub with_native_code
port_definition Fin.instSub with_native_code
port_proof Fin.xor._proof_1
port_definition Fin.xor with_native_code
port_definition Fin.instXorOp with_native_code
port_definition Fin.last with_native_code
port_definition Fin.modn.match_1 with_native_code
port_definition Fin.modn with_native_code
port_proof Fin.modn.eq_1
port_proof Fin.modn_lt
port_proof Fin.natAdd._proof_1
port_definition Fin.natAdd with_native_code
port_proof Fin.ne_of_val_ne
port_proof Fin.neg_def
port_proof Fin.subNat._proof_1
port_definition Fin.subNat with_native_code
port_proof Fin.pred._proof_1
port_proof Fin.pred._proof_2
port_definition Fin.pred with_native_code
port_proof Fin.rev._proof_1
port_definition Fin.rev with_native_code
port_definition Fin.succ.match_1 with_native_code
port_definition Fin.succ with_native_code
port_definition Fin.toNat with_native_code
port_proof Fin.toNat_eq_val
port_proof Fin.val_add_one_le_of_gt
port_proof Fin.val_add_one_le_of_lt
port_proof Fin.val_inj
port_proof Fin.val_congr
port_proof Fin.val_le_of_ge
port_proof Fin.val_le_of_le
port_proof Fin.val_lt_of_le
port_proof Fin.val_ne_of_ne
port_proof Fin.val_neg'
port_proof Fin.zero_eta

port_private_declaration Fin.mlt.match_1_1
port_private_declaration Fin.mlt
port_private_declaration Fin.modn_lt.match_1_1
port_private_declaration Fin.exists_iff.match_1_1
port_private_declaration Fin.exists_iff.match_1_3
port_private_declaration Fin.modn.match_1.eq_1
port_private_declaration Fin.modn.match_1.splitter

attribute [instance] Omega.Fin.coeToNat
attribute [instance] Omega.Fin.instAdd
attribute [instance] Omega.Fin.instSub
attribute [instance] Omega.Fin.instMul
attribute [instance] Omega.Fin.instMod
attribute [instance] Omega.Fin.instDiv
attribute [instance] Omega.Fin.instAndOp
attribute [instance] Omega.Fin.instOrOp
attribute [instance] Omega.Fin.instXorOp
attribute [instance] Omega.Fin.instShiftLeft
attribute [instance] Omega.Fin.instShiftRight
attribute [instance] Omega.Fin.instOfNat
attribute [instance] Omega.Fin.neg
attribute [instance] Omega.Fin.instInhabited
