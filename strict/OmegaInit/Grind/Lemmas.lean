/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import OmegaInit.Prelude

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
