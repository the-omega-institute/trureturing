/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module
prelude
public import OmegaInit.Data.Nat.Basic

port_proof Nat.min_eq_min by_reflexivity
port_proof Nat.max_eq_max by_reflexivity
port_proof Nat.min_eq_left
port_proof Nat.max_eq_right

namespace Omega.Nat

public protected theorem min_eq_right {a b : Nat} (h : Nat.le b a) : Eq (Nat.min a b) b :=
  (Nat.lt_or_ge b a).elim (fun lt => ite_eq_right (Nat.not_le_of_lt lt))
    (fun le => (Nat.min_eq_left le).trans (Nat.le_antisymm le h))

public protected theorem max_eq_left {a b : Nat} (h : Nat.le b a) : Eq (Nat.max a b) a :=
  (Nat.lt_or_ge b a).elim (fun lt => ite_eq_right (Nat.not_le_of_lt lt))
    (fun le => (Nat.max_eq_right le).trans (Nat.le_antisymm h le))

public protected theorem min_comm (a b : Nat) : Eq (Nat.min a b) (Nat.min b a) :=
  (Nat.le_total a b).elim
    (fun h => (Nat.min_eq_left h).trans (Nat.min_eq_right h).symm)
    (fun h => (Nat.min_eq_right h).trans (Nat.min_eq_left h).symm)

public protected theorem max_comm (a b : Nat) : Eq (Nat.max a b) (Nat.max b a) :=
  (Nat.le_total a b).elim
    (fun h => (Nat.max_eq_right h).trans (Nat.max_eq_left h).symm)
    (fun h => (Nat.max_eq_left h).trans (Nat.max_eq_right h).symm)

private theorem mapMin (f : Nat → Nat) (mono : ∀ {a b}, Nat.le a b → Nat.le (f a) (f b)) (a b : Nat) :
    Eq (Nat.min (f a) (f b)) (f (Nat.min a b)) :=
  (Nat.le_total a b).elim
    (fun h => (Nat.min_eq_left (mono h)).trans (congrArg f (Nat.min_eq_left h)).symm)
    (fun h => (Nat.min_eq_right (mono h)).trans (congrArg f (Nat.min_eq_right h)).symm)

private theorem mapMax (f : Nat → Nat) (mono : ∀ {a b}, Nat.le a b → Nat.le (f a) (f b)) (a b : Nat) :
    Eq (Nat.max (f a) (f b)) (f (Nat.max a b)) :=
  (Nat.le_total a b).elim
    (fun h => (Nat.max_eq_right (mono h)).trans (congrArg f (Nat.max_eq_right h)).symm)
    (fun h => (Nat.max_eq_left (mono h)).trans (congrArg f (Nat.max_eq_left h)).symm)

end Omega.Nat

port_proof Nat.instCommutativeMin
port_proof Nat.instCommutativeMax

attribute [instance] Omega.Nat.instCommutativeMin Omega.Nat.instCommutativeMax

namespace Omega.Nat

public protected theorem add_min_add_left (a b c : Nat) :
    Eq (Nat.min (Nat.add a b) (Nat.add a c)) (Nat.add a (Nat.min b c)) :=
  mapMin (Nat.add a) (fun h => Nat.add_le_add_left h a) b c

public protected theorem add_min_add_right (a b c : Nat) :
    Eq (Nat.min (Nat.add a c) (Nat.add b c)) (Nat.add (Nat.min a b) c) :=
  mapMin (fun n => Nat.add n c) (fun h => Nat.add_le_add_right h c) a b

public protected theorem mul_min_mul_left (a b c : Nat) :
    Eq (Nat.min (Nat.mul a b) (Nat.mul a c)) (Nat.mul a (Nat.min b c)) :=
  mapMin (Nat.mul a) (fun h => Nat.mul_le_mul_left a h) b c

public protected theorem mul_min_mul_right (a b c : Nat) :
    Eq (Nat.min (Nat.mul a c) (Nat.mul b c)) (Nat.mul (Nat.min a b) c) :=
  mapMin (fun n => Nat.mul n c) (fun h => Nat.mul_le_mul_right c h) a b

public protected theorem add_max_add_left (a b c : Nat) :
    Eq (Nat.max (Nat.add a b) (Nat.add a c)) (Nat.add a (Nat.max b c)) :=
  mapMax (Nat.add a) (fun h => Nat.add_le_add_left h a) b c

public protected theorem add_max_add_right (a b c : Nat) :
    Eq (Nat.max (Nat.add a c) (Nat.add b c)) (Nat.add (Nat.max a b) c) :=
  mapMax (fun n => Nat.add n c) (fun h => Nat.add_le_add_right h c) a b

public protected theorem mul_max_mul_left (a b c : Nat) :
    Eq (Nat.max (Nat.mul a b) (Nat.mul a c)) (Nat.mul a (Nat.max b c)) :=
  mapMax (Nat.mul a) (fun h => Nat.mul_le_mul_left a h) b c

public protected theorem mul_max_mul_right (a b c : Nat) :
    Eq (Nat.max (Nat.mul a c) (Nat.mul b c)) (Nat.mul (Nat.max a b) c) :=
  mapMax (fun n => Nat.mul n c) (fun h => Nat.mul_le_mul_right c h) a b

end Omega.Nat

namespace Omega.Nat

public protected theorem zero_min (a : Nat) : Eq (Nat.min zero a) zero := Nat.min_eq_left (zero_le a)
public protected theorem min_zero (a : Nat) : Eq (Nat.min a zero) zero := Nat.min_eq_right (zero_le a)
public protected theorem zero_max (a : Nat) : Eq (Nat.max zero a) a := Nat.max_eq_right (zero_le a)
public protected theorem max_zero (a : Nat) : Eq (Nat.max a zero) a := Nat.max_eq_left (zero_le a)

public protected theorem min_le_right (a b : Nat) : Nat.le (Nat.min a b) b :=
  (Nat.le_total a b).elim
    (fun h => Eq.subst (motive := fun n => Nat.le n b) (Nat.min_eq_left h).symm h)
    (fun h => Eq.subst (motive := fun n => Nat.le n b) (Nat.min_eq_right h).symm (Nat.le_refl b))

public protected theorem le_max_left (a b : Nat) : Nat.le a (Nat.max a b) :=
  (Nat.le_total a b).elim
    (fun h => Eq.subst (motive := Nat.le a) (Nat.max_eq_right h).symm h)
    (fun h => Eq.subst (motive := Nat.le a) (Nat.max_eq_left h).symm (Nat.le_refl a))

end Omega.Nat

port_proof Nat.min_le_left
port_proof Nat.le_min_of_le_of_le
port_proof Nat.le_min
port_proof Nat.lt_min
port_proof Nat.le_max_right
port_proof Nat.max_le_of_le_of_le
port_proof Nat.max_le
namespace Omega.Nat

public protected theorem max_lt {a b c : Nat} : Iff (Nat.lt (Nat.max a b) c) (And (Nat.lt a c) (Nat.lt b c)) :=
  Iff.intro
    (fun h => And.intro (Nat.le_trans (succ_le_succ (Nat.le_max_left a b)) h)
      (Nat.le_trans (succ_le_succ (Nat.le_max_right a b)) h))
    (fun bounds => (Nat.le_total a b).elim
      (fun h => Eq.subst (motive := fun n => Nat.lt n c) (Nat.max_eq_right h).symm bounds.right)
      (fun h => Eq.subst (motive := fun n => Nat.lt n c) (Nat.max_eq_left h).symm bounds.left))

end Omega.Nat
