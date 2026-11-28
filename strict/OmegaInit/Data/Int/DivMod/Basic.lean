/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/
module
prelude
public import OmegaInit.Data.Int.Basic
import OmegaInit.Data.Nat.Div.Basic

port_definition Int.ediv.match_1
port_definition Int.ediv with_native_code
port_definition Int.emod.match_1
port_definition Int.emod with_native_code
port_definition Int.instDiv with_native_code
port_definition Int.instMod with_native_code
attribute [instance] Omega.Int.instDiv Omega.Int.instMod

port_proof Int.natCast_ediv
port_proof Int.ofNat_ediv_ofNat
port_proof Int.ofNat_ediv_negSucc
port_proof Int.negSucc_ediv_ofNat_succ
port_proof Int.negSucc_ediv_negSucc
port_proof Int.negSucc_emod_ofNat
port_proof Int.negSucc_emod_negSucc

port_definition Int.tdiv.match_1
port_definition Int.tdiv with_native_code
port_definition Int.tmod with_native_code
port_proof Int.ofNat_tdiv

port_definition Int.fdiv.match_1
port_definition Int.fdiv with_native_code
port_proof Int.fdiv.eq_1
port_proof Int.fdiv.eq_2
port_proof Int.fdiv.eq_3
port_proof Int.fdiv.eq_4
port_proof Int.fdiv.eq_5
port_proof Int.fdiv.eq_6
port_definition Int.fmod.match_1
port_definition Int.fmod with_native_code

namespace Omega.Int
private theorem ofNatFdiv (m n : Nat) : Eq (ofNat (Nat.div m n)) (fdiv (ofNat m) (ofNat n)) :=
  Nat.casesOn (motive := fun m => Eq (ofNat (Nat.div m n)) (fdiv (ofNat m) (ofNat n))) m
    (congrArg ofNat (Nat.zero_div n)) (fun _ => Omega.rfl)
end Omega.Int
port_proof Int.ofNat_fdiv using Omega.Int.ofNatFdiv

port_definition Int.bmod with_native_code
port_definition Int.bdiv with_native_code
port_definition Int.divExact with_native_code
port_proof Int.divExact_eq_ediv
