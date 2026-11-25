/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude

public import OmegaInit.Core

/-!
Omega original.

Order comparison with diagonal upper bounds gives a functional-calculus
inequality in a corner. The diagonal bound may depend on the perturbation;
only the first corner has a prescribed limit. The second diagonal component
therefore needs no uniform bound or limiting value.
-/

@[expose] public section

namespace Omega.CornerCompression

/-- Two ordered carriers with a corner, a diagonal embedding, and a functional
calculus. `Small` indexes the positive perturbations of the first corner. -/
structure System (A : Type u) (B : Type v) (S : Type w) (F : Type x) where
  le : A → A → Prop
  leDouble : B → B → Prop
  positive : A → Prop
  positiveDouble : B → Prop
  small : S → Prop
  continuous : F → Prop
  apply : F → A → A
  applyDouble : F → B → B
  corner : B → A
  shift : A → S → A
  diagonal : A → A → B

/-- Structural properties of the corner and diagonal operations. The last
property is closedness of order under the indicated first-corner limit. -/
structure System.Laws {A : Type u} {B : Type v} {S : Type w} {F : Type x}
    (s : System A B S F) : Prop where
  corner_mono : ∀ {X Y}, s.leDouble X Y → s.le (s.corner X) (s.corner Y)
  corner_positive : ∀ {X}, s.positiveDouble X → s.positive (s.corner X)
  diagonal_calculus : ∀ f, s.continuous f → ∀ a b,
    s.positive a → s.positive b →
    Eq (s.corner (s.applyDouble f (s.diagonal a b))) (s.apply f a)
  sandwich : ∀ X, s.positiveDouble X → ∀ ε, s.small ε →
    Exists (fun b => And (s.positive (s.shift (s.corner X) ε))
      (And (s.positive b)
        (And (s.positiveDouble (s.diagonal (s.shift (s.corner X) ε) b))
          (s.leDouble X (s.diagonal (s.shift (s.corner X) ε) b)))))
  limit_closed : ∀ f, s.continuous f → ∀ a, s.positive a → ∀ z,
    (∀ ε, s.small ε → s.le z (s.apply f (s.shift a ε))) → s.le z (s.apply f a)

/-- Monotonicity on the doubled carrier controls the functional calculus in a
corner, using diagonal comparisons at every positive perturbation. -/
theorem corner_calculus_le {A : Type u} {B : Type v} {S : Type w} {F : Type x}
    (s : System A B S F) (laws : s.Laws) (f : F) (hf : s.continuous f)
    (monotone : ∀ X Y, s.positiveDouble X → s.positiveDouble Y →
      s.leDouble X Y → s.leDouble (s.applyDouble f X) (s.applyDouble f Y))
    (X : B) (hX : s.positiveDouble X) :
    s.le (s.corner (s.applyDouble f X)) (s.apply f (s.corner X)) :=
  laws.limit_closed f hf (s.corner X) (laws.corner_positive hX)
    (s.corner (s.applyDouble f X))
    (fun ε hε => Exists.elim (laws.sandwich X hX ε hε)
      (fun b properties =>
        Eq.subst (motive := fun y => s.le (s.corner (s.applyDouble f X)) y)
          (laws.diagonal_calculus f hf (s.shift (s.corner X) ε) b
            properties.left properties.right.left)
          (laws.corner_mono (monotone X (s.diagonal (s.shift (s.corner X) ε) b)
            hX properties.right.right.left properties.right.right.right))))

end Omega.CornerCompression
