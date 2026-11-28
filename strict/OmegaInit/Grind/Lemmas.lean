/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import OmegaInit.GetElem
public import OmegaInit.SimpLemmas

port_proof Lean.Grind.eqNDRec_heq
port_proof Lean.Grind.eqRecOn_heq
port_proof Lean.Grind.eqRec_heq
port_proof Lean.Grind.eval_congr₁
port_proof Lean.Grind.eval_congr₂
port_proof Lean.Grind.heq_congr
port_proof Lean.Grind.rfl_true by_reflexivity

port_proof Lean.Grind.Bool.and_eq_of_eq_false_left by_finite_cases
port_proof Lean.Grind.Bool.and_eq_of_eq_false_right by_finite_cases
port_proof Lean.Grind.Bool.and_eq_of_eq_true_left by_finite_cases
port_proof Lean.Grind.Bool.and_eq_of_eq_true_right by_finite_cases
port_proof Lean.Grind.Bool.eq_false_of_or_eq_false_left by_finite_cases
port_proof Lean.Grind.Bool.eq_false_of_or_eq_false_right by_finite_cases
port_proof Lean.Grind.Bool.eq_true_of_and_eq_true_left by_finite_cases
port_proof Lean.Grind.Bool.eq_true_of_and_eq_true_right by_finite_cases
port_proof Lean.Grind.Bool.or_eq_of_eq_false_left by_finite_cases
port_proof Lean.Grind.Bool.or_eq_of_eq_false_right by_finite_cases
port_proof Lean.Grind.Bool.or_eq_of_eq_true_left by_finite_cases
port_proof Lean.Grind.Bool.or_eq_of_eq_true_right by_finite_cases
port_proof Lean.Grind.Bool.eq_false_of_not_eq_true' using Omega.Bool.eq_false_of_ne_true
port_proof Lean.Grind.Bool.eq_true_of_not_eq_false' using Omega.Bool.eq_true_of_ne_false

namespace Omega.Lean.Grind.Bool
public section

theorem not_eq_of_eq_true {a : Bool} (h : Eq a Bool.true) : Eq (Omega.Bool.not a) Bool.false :=
  congrArg Omega.Bool.not h

theorem not_eq_of_eq_false {a : Bool} (h : Eq a Bool.false) : Eq (Omega.Bool.not a) Bool.true :=
  congrArg Omega.Bool.not h

theorem eq_false_of_not_eq_true {a : Bool} (h : Eq (Omega.Bool.not a) Bool.true) : Eq a Bool.false :=
  Omega.Bool.eq_false_of_ne_true (fun eq => Omega.Bool.ne_false_of_eq_true h (not_eq_of_eq_true eq))

theorem eq_true_of_not_eq_false {a : Bool} (h : Eq (Omega.Bool.not a) Bool.false) : Eq a Bool.true :=
  Omega.Bool.eq_true_of_ne_false (fun eq => Omega.Bool.ne_true_of_eq_false h (not_eq_of_eq_false eq))

theorem false_of_not_eq_self {a : Bool} (h : Eq (Omega.Bool.not a) a) : False :=
  Bool.casesOn (motive := fun a => Eq (Omega.Bool.not a) a → False) a
    (Omega.Bool.ne_false_of_eq_true Omega.rfl) (Omega.Bool.ne_true_of_eq_false Omega.rfl) h

end
end Omega.Lean.Grind.Bool

port_definition Lean.Grind.intro_with_eq with_native_code
port_definition Lean.Grind.intro_with_eq' with_native_code
port_proof Lean.Grind.getElem_congr
port_proof Lean.Grind.eq_of_beq_eq_true using Omega.LawfulBEq.eq_of_beq

namespace Omega.Lean.Grind
public section

theorem eq_congr {α : Sort u} {a₁ b₁ a₂ b₂ : α} (h₁ : Eq a₁ a₂) (h₂ : Eq b₁ b₂) :
    Eq (Eq a₁ b₁) (Eq a₂ b₂) :=
  (congrArg (fun x => Eq x b₁) h₁).trans (congrArg (Eq a₂) h₂)

theorem ne_of_ne_of_eq_left {α : Sort u} {a b c : α} (h₁ : Eq a b) (h₂ : Ne b c) : Ne a c :=
  fun eq => h₂ (h₁.symm.trans eq)

theorem ne_of_ne_of_eq_right {α : Sort u} {a b c : α} (h₁ : Eq a c) (h₂ : Ne b c) : Ne b a :=
  fun eq => h₂ (eq.trans h₁)

theorem false_of_not_eq_self {a : Prop} (h : Eq (Not a) a) : False :=
  let neg : Not a := fun ha => (Eq.mpr h ha) ha
  neg (Eq.mp h neg)

private theorem decideTrue {p : Prop} {d : Decidable p} (h : Eq p True) :
    Eq (@Decidable.decide p d) Bool.true :=
  Decidable.falseTrueCases (motive := fun d => Eq (@Decidable.decide p d) Bool.true)
    (fun neg => False.elim (neg (of_eq_true h))) (fun _ => Omega.rfl) d

private theorem decideFalse {p : Prop} {d : Decidable p} (h : Eq p False) :
    Eq (@Decidable.decide p d) Bool.false := @Omega.decide_eq_false p d (of_eq_false h)

end
end Omega.Lean.Grind

port_proof Lean.Grind.decide_eq_true using Omega.Lean.Grind.decideTrue
port_proof Lean.Grind.decide_eq_false using Omega.Lean.Grind.decideFalse
