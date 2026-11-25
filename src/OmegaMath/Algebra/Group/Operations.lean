/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude

public import OmegaInit.Core

/-!
Omega original.

An additive group presented by its operations and left group laws.
-/

noncomputable section

@[expose] public section

namespace Omega

/-- The operations of an additive group. -/
structure AddGroup (A : Type u) where
  zeroAt : True → A
  add : A → A → A
  neg : A → A

namespace AddGroup

variable {A : Type u} (G : AddGroup A)

def ofOperations (zero : A) (add : A → A → A) (neg : A → A) : AddGroup A :=
  ⟨fun _ => zero, add, neg⟩

def zero : A := G.zeroAt True.intro

def sub (a b : A) : A := G.add a (G.neg b)

/-- Associativity, left identity, and left inverse. -/
def Laws : Prop :=
  And (∀ a b c, Eq (G.add (G.add a b) c) (G.add a (G.add b c)))
    (And (∀ a, Eq (G.add G.zero a) a)
      (∀ a, Eq (G.add (G.neg a) a) G.zero))

variable {G}

private theorem cancelLeft (laws : G.Laws) {a b c : A} (same : Eq (G.add a b) (G.add a c)) : Eq b c :=
  have remove (value : A) : Eq (G.add (G.neg a) (G.add a value)) value :=
    (laws.left (G.neg a) a value).symm.trans
      ((congrArg (fun total => G.add total value) (laws.right.right a)).trans
        (laws.right.left value))
  (remove b).symm.trans ((congrArg (G.add (G.neg a)) same).trans (remove c))

private theorem addZero (laws : G.Laws) (a : A) : Eq (G.add a G.zero) a :=
  cancelLeft laws (a := G.neg a)
    ((laws.left (G.neg a) a G.zero).symm.trans
      ((congrArg (fun total => G.add total G.zero) (laws.right.right a)).trans
        ((laws.right.left G.zero).trans (laws.right.right a).symm)))

theorem addNegCancel (laws : G.Laws) (a : A) : Eq (G.add a (G.neg a)) G.zero :=
  cancelLeft laws (a := G.neg a)
    ((laws.left (G.neg a) a (G.neg a)).symm.trans
      ((congrArg (fun total => G.add total (G.neg a)) (laws.right.right a)).trans
        ((laws.right.left (G.neg a)).trans (addZero laws (G.neg a)).symm)))

theorem subAddCancel (laws : G.Laws) (a b : A) : Eq (G.add (G.sub a b) b) a :=
  (laws.left a (G.neg b) b).trans
    ((congrArg (G.add a) (laws.right.right b)).trans (addZero laws a))

end AddGroup
end Omega
