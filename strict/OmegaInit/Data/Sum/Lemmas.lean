/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury G. Kudryashov
-/
module
prelude
public import OmegaInit.Data.Sum.Basic
public import OmegaInit.WF
public import OmegaInit.SimpLemmas

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

port_proof Sum.LiftRel.mono
port_proof Sum.LiftRel.mono_left
port_proof Sum.LiftRel.mono_right
port_proof Sum.LiftRel.swap
port_proof Sum.liftRel_swap_iff
port_proof Sum.LiftRel.lex
port_proof Sum.liftRel_subrelation_lex
port_proof Sum.Lex.mono
port_proof Sum.Lex.mono_left
port_proof Sum.Lex.mono_right
port_proof Sum.lex_acc_inl
port_proof Sum.lex_acc_inr
port_proof Sum.lex_wf
port_proof Sum.inl_ne_inr
port_proof Sum.inr_ne_inl
port_proof Sum.inl.inj_iff
port_proof Sum.inr.inj_iff
port_proof Sum.inl_getLeft
port_proof Sum.inr_getRight
port_proof Sum.eq_left_getLeft_of_isLeft
port_proof Sum.eq_right_getRight_of_isRight
port_proof Sum.getLeft_eq_iff by_constructive_casts
port_proof Sum.getRight_eq_iff by_constructive_casts
port_proof Sum.getLeft?_eq_some_iff by_constructive_casts
port_proof Sum.getRight?_eq_some_iff by_constructive_casts
port_proof Sum.getLeft?_eq_none_iff by_constructive_casts
port_proof Sum.getRight?_eq_none_iff by_constructive_casts
port_proof Sum.isLeft_eq_false by_constructive_casts
port_proof Sum.isRight_eq_false by_constructive_casts
port_proof Sum.isLeft_iff by_constructive_casts
port_proof Sum.isRight_iff by_constructive_casts
namespace Omega.Sum

public theorem not_isLeft {α : Type u} {β : Type v} {x : Sum α β} :
    Iff (Not (Eq x.isLeft Bool.true)) (Eq x.isRight Bool.true) :=
  Iff.intro (fun h => isLeft_eq_false.mp (Bool.eq_false_of_ne_true h))
    (fun h => Bool.ne_true_of_eq_false (isLeft_eq_false.mpr h))

public theorem not_isRight {α : Type u} {β : Type v} {x : Sum α β} :
    Iff (Not (Eq x.isRight Bool.true)) (Eq x.isLeft Bool.true) :=
  Iff.intro (fun h => isRight_eq_false.mp (Bool.eq_false_of_ne_true h))
    (fun h => Bool.ne_true_of_eq_false (isRight_eq_false.mpr h))

public theorem elim_eq_iff {α : Type u} {γ : Sort v} {β : Type w}
    {u u' : α → γ} {v v' : β → γ} :
    Iff (Eq (Sum.elim u v) (Sum.elim u' v')) (And (Eq u u') (Eq v v')) :=
  Iff.intro
    (fun law => And.intro
      (congrArg (fun (f : Sum α β → γ) (a : α) => f (Sum.inl a)) law)
      (congrArg (fun (f : Sum α β → γ) (b : β) => f (Sum.inr b)) law))
    (fun h => Eq.trans (congrArg (fun f => Sum.elim f v) h.left)
      (congrArg (fun f => Sum.elim u' f) h.right))

end Omega.Sum
