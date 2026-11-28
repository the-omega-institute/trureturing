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

port_definition Option.pbind.match_1 with_native_code
port_definition Option.pbind with_native_code
port_proof Option.pmap._proof_1
port_definition Option.pmap.match_1 with_native_code
port_definition Option.pmap with_native_code
port_definition Option.pfilter.match_1 with_native_code
port_definition Option.pfilter with_native_code
port_definition Option.pelim.match_1 with_native_code
port_definition Option.pelim with_native_code
port_proof Option.mem_def by_reflexivity

namespace Omega.Option

private theorem someInjImpl {α : Type u} {a b : α} : Iff (Eq (some a) (some b)) (Eq a b) :=
  Iff.intro (fun h => congrArg (fun o : Option α => Option.getD o b) h) (congrArg Option.some)

private theorem eqNoneOfIsNoneImpl {α : Type u} {o : Option α} : Eq o.isNone Bool.true → Eq o none :=
  Option.casesOn (motive := fun x => Eq x.isNone Bool.true → Eq x none) o (fun _ => rfl)
    (fun _ h => False.elim (Bool.decEq._proof_1 Bool.false Bool.true (isNone_some.symm.trans h)))

end Omega.Option

port_proof Option.eq_none_of_isNone using Omega.Option.eqNoneOfIsNoneImpl
port_proof Option.some_inj using Omega.Option.someInjImpl
port_definition Option.instDecidableMemOfDecidableEq with_native_code

namespace Omega.Option

private theorem isNoneIffEqNoneImpl {α : Type u} {o : Option α} : Iff (Eq o.isNone Bool.true) (Eq o none) :=
  Iff.intro eq_none_of_isNone (fun h => Eq.trans (congrArg Option.isNone h) isNone_none)

end Omega.Option

port_proof Option.isNone_iff_eq_none using Omega.Option.isNoneIffEqNoneImpl
port_proof Option.eq_of_eq_some

attribute [instance] Omega.Option.instMembership Omega.Option.instDecidableMemOfDecidableEq
  Omega.Option.instForMOfMonad Omega.Option.instForIn'InferInstanceMembershipOfMonad
