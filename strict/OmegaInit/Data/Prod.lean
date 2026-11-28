/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
module
prelude
public import OmegaInit.Core

port_proof Prod.forall
port_proof Prod.exists
port_proof Prod.map_id by_reflexivity
port_proof Prod.map_id' by_reflexivity
port_proof Prod.map_comp_map by_reflexivity
port_proof Prod.map_map by_reflexivity
port_definition Prod.swap with_native_code
port_proof Prod.swap_swap by_reflexivity
port_proof Prod.fst_swap by_reflexivity
port_proof Prod.snd_swap by_reflexivity
port_proof Prod.swap_prod_mk by_reflexivity
port_proof Prod.swap_swap_eq by_reflexivity
port_proof Prod.map_comp_swap by_reflexivity

public section
namespace Omega.Prod

@[instance] theorem instReflBEq {α : Type u_1} {β : Type u_2} [BEq α] [BEq β] [ReflBEq α] [ReflBEq β] :
    ReflBEq (Prod α β) :=
  ⟨fun {a} => congr (congrArg Bool.and (@ReflBEq.rfl α _ _ a.fst)) (@ReflBEq.rfl β _ _ a.snd)⟩

private theorem andParts (x y : Bool) : Eq (Bool.and x y) Bool.true → And (Eq x Bool.true) (Eq y Bool.true) :=
  Bool.rec (motive := fun b => Eq (Bool.and b y) Bool.true → And (Eq b Bool.true) (Eq y Bool.true))
    (fun h => False.elim (Bool.ne_true_of_eq_false (b := Bool.false) Omega.rfl h))
    (fun h => ⟨Omega.rfl, h⟩) x

@[instance] theorem instLawfulBEq {α : Type u_1} {β : Type u_2} [BEq α] [BEq β] [LawfulBEq α] [LawfulBEq β] :
    LawfulBEq (Prod α β) :=
  ⟨fun {_ _} h =>
    congr (congrArg Prod.mk (LawfulBEq.eq_of_beq (andParts _ _ h).left))
      (LawfulBEq.eq_of_beq (andParts _ _ h).right)⟩

theorem swap_inj {α : Type u} {β : Type v} {p q : Prod α β} :
    Iff (Eq (swap p) (swap q)) (Eq p q) :=
  ⟨congrArg swap, congrArg swap⟩

end Omega.Prod
