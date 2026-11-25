/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaMath.Harmonic.HurwitzFreeGroup

/-!
Omega original.

The relative quaternion of two reduced words is scalar only when the words
are identical. Removing a common initial letter removes a factor of five
from the relative product.
-/

noncomputable section

@[expose] public section

namespace Omega.Hurwitz.FreeGroup

private theorem Word.cons_ne_nil (g : Generator) (tail : Word) : Not (Eq (Word.cons g tail) .nil) :=
  fun h => Eq.subst (Word.rec (motive := fun _ => Prop) False (fun _ _ _ => True)) h True.intro

private theorem opposite_conj (g : Generator) :
    Eq (generatorQuat g.opposite) (generatorQuat g).conj :=
  Generator.rec Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl g

private theorem opposite_reversed (g h : Generator) :
    Eq (h.opposite.isOpposite g.opposite) (g.isOpposite h) :=
  let check := fun (g h : Generator) => Eq (h.opposite.isOpposite g.opposite) (g.isOpposite h)
  (Generator.rec (motive := fun g => ∀ h, check g h)
    (Generator.rec (motive := check .iPos) Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl)
    (Generator.rec (motive := check .iNeg) Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl)
    (Generator.rec (motive := check .jPos) Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl)
    (Generator.rec (motive := check .jNeg) Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl)
    (Generator.rec (motive := check .kPos) Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl)
    (Generator.rec (motive := check .kNeg) Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl) g) h

private theorem head_comparison (g h : Generator) :
    Or (Eq g h) (Eq (g.opposite.isOpposite h) .false) :=
  let check := fun (g h : Generator) => Or (Eq g h) (Eq (g.opposite.isOpposite h) .false)
  (Generator.rec (motive := fun g => ∀ h, check g h)
    (Generator.rec (motive := check .iPos)
      (Or.inl Eq.refl) (Or.inr Eq.refl) (Or.inr Eq.refl) (Or.inr Eq.refl) (Or.inr Eq.refl) (Or.inr Eq.refl))
    (Generator.rec (motive := check .iNeg)
      (Or.inr Eq.refl) (Or.inl Eq.refl) (Or.inr Eq.refl) (Or.inr Eq.refl) (Or.inr Eq.refl) (Or.inr Eq.refl))
    (Generator.rec (motive := check .jPos)
      (Or.inr Eq.refl) (Or.inr Eq.refl) (Or.inl Eq.refl) (Or.inr Eq.refl) (Or.inr Eq.refl) (Or.inr Eq.refl))
    (Generator.rec (motive := check .jNeg)
      (Or.inr Eq.refl) (Or.inr Eq.refl) (Or.inr Eq.refl) (Or.inl Eq.refl) (Or.inr Eq.refl) (Or.inr Eq.refl))
    (Generator.rec (motive := check .kPos)
      (Or.inr Eq.refl) (Or.inr Eq.refl) (Or.inr Eq.refl) (Or.inr Eq.refl) (Or.inl Eq.refl) (Or.inr Eq.refl))
    (Generator.rec (motive := check .kNeg)
      (Or.inr Eq.refl) (Or.inr Eq.refl) (Or.inr Eq.refl) (Or.inr Eq.refl) (Or.inr Eq.refl) (Or.inl Eq.refl))
    g) h

private def reverseOppositeAppend (u v : Word) : Word :=
  Word.rec (motive := fun _ => Word → Word) (fun v => v)
    (fun g _ ih v => ih (.cons g.opposite v)) u v

private theorem reverseOppositeAppend_eval (u : Word) :
    ∀ v, Eq (evalQuat (reverseOppositeAppend u v)) ((evalQuat u).conj.mul (evalQuat v)) :=
  Word.rec (motive := fun u =>
    ∀ v, Eq (evalQuat (reverseOppositeAppend u v)) ((evalQuat u).conj.mul (evalQuat v)))
    (fun v => ((Quaternion.scalar_mul Int.one (evalQuat v)).trans
      (Quaternion.scale_one (evalQuat v))).symm)
    (fun g tail ih v =>
      let p := evalQuat tail
      let q := evalQuat v
      let a := generatorQuat g
      (ih (.cons g.opposite v)).trans
        ((congrArg p.conj.mul (congrArg (fun x : Quaternion => x.mul q) (opposite_conj g))).trans
          ((Quaternion.mul_assoc p.conj a.conj q).symm.trans
            (congrArg (fun x : Quaternion => x.mul q) (Quaternion.conj_mul a p).symm)))) u

private def CanJoin (u v : Word) : Prop :=
  Word.rec (motive := fun _ => Prop) True (fun g _ _ => v.AllowsPrepend g.opposite) u

private theorem reversed_boundary (g : Generator) (u v : Word) (h : u.AllowsPrepend g) :
    CanJoin u (.cons g.opposite v) :=
  let check := fun (u : Word) => u.AllowsPrepend g → CanJoin u (.cons g.opposite v)
  (Word.rec (motive := check) (fun _ => True.intro)
    (fun k _ _ h => (opposite_reversed g k).trans h) u) h

private theorem reverseOppositeAppend_reduced (u : Word) :
    ∀ v, IsReduced u → IsReduced v → CanJoin u v → IsReduced (reverseOppositeAppend u v) :=
  Word.rec (motive := fun u =>
    ∀ v, IsReduced u → IsReduced v → CanJoin u v → IsReduced (reverseOppositeAppend u v))
    (fun _ _ hv _ => hv)
    (fun g u ih v hu hv join =>
      ih (.cons g.opposite v) hu.right (And.intro join hv) (reversed_boundary g u v hu.left)) u

private theorem reverseOppositeAppend_ne_nil_right (u : Word) :
    ∀ v : Word, Not (Eq v Word.nil) → Not (Eq (reverseOppositeAppend u v) Word.nil) :=
  Word.rec (motive := fun u => ∀ v : Word, Not (Eq v Word.nil) → Not (Eq (reverseOppositeAppend u v) Word.nil))
    (fun _ hv => hv)
    (fun g _ ih v _ => ih (.cons g.opposite v) (Word.cons_ne_nil g.opposite v)) u

private theorem joined_not_scalar (u v : Word) (hu : IsReduced u) (hv : IsReduced v)
    (join : CanJoin u v) (ne : Not (Eq (reverseOppositeAppend u v) .nil))
    (k : Int) : Not (Eq ((evalQuat u).conj.mul (evalQuat v)) (Quaternion.scalar k)) :=
  fun scalar => reduced_word_ne_scalar (reverseOppositeAppend u v)
    (reverseOppositeAppend_reduced u v hu hv join) ne k
    ((reverseOppositeAppend_eval u v).trans scalar)

private theorem common_head_factor (g : Generator) (p q : Quaternion) :
    Eq (((generatorQuat g).mul p).conj.mul ((generatorQuat g).mul q))
      (Quaternion.scale (Int.ofNat five) (p.conj.mul q)) :=
  let a := generatorQuat g
  let f := Int.ofNat five
  have square : Eq (a.conj.mul a) (Quaternion.scalar f) :=
    (Quaternion.conj_mul_eq_normSq a).trans
      (congrArg (fun n => Quaternion.scalar (Int.ofNat n)) (generator_normSq g))
  (congrArg (fun b : Quaternion => b.mul (a.mul q)) (Quaternion.conj_mul a p)).trans
    ((Quaternion.mul_assoc p.conj a.conj (a.mul q)).trans
      ((congrArg p.conj.mul (Quaternion.mul_assoc a.conj a q).symm).trans
        ((congrArg (fun b : Quaternion => p.conj.mul (b.mul q)) square).trans
          ((congrArg p.conj.mul (Quaternion.scalar_mul f q)).trans
            (Quaternion.scale_mul_right f p.conj q)))))

private theorem scalar_of_scale_five {q : Quaternion} {k : Int}
    (h : Eq (Quaternion.scale (Int.ofNat five) q) (Quaternion.scalar k)) :
    Eq q (Quaternion.scalar q.w) :=
  let recover := fun (t : Int) (e : Eq ((Int.ofNat five).mul t) Int.zero) =>
    (Int.mul_eq_zero.mp e).elim
      (fun zero => False.elim (Int.ofNat_succ_ne_zero five.pred zero)) (fun h => h)
  Quaternion.ext Eq.refl (recover q.x (congrArg Quaternion.x h))
    (recover q.y (congrArg Quaternion.y h)) (recover q.z (congrArg Quaternion.z h))

/-- Distinct reduced words have a nonscalar relative quaternion. -/
theorem reduced_words_eq_of_relative_scalar (u v : Word) (hu : IsReduced u) (hv : IsReduced v)
    (k : Int) (scalar : Eq ((evalQuat u).conj.mul (evalQuat v)) (Quaternion.scalar k)) :
    Eq u v :=
  let statement := fun (u v : Word) => IsReduced u → IsReduced v →
    ∀ k : Int, Eq ((evalQuat u).conj.mul (evalQuat v)) (Quaternion.scalar k) → Eq u v
  (Word.rec (motive := fun u => ∀ v, statement u v)
    (Word.rec (motive := statement .nil)
      (fun _ _ _ _ => Eq.refl)
      (fun g v _ hu hv k scalar => False.elim
        (joined_not_scalar .nil (.cons g v) hu hv True.intro (Word.cons_ne_nil g v) k scalar)))
    (fun g u ih => Word.rec (motive := statement (.cons g u))
      (fun hu hv k scalar => False.elim
        (joined_not_scalar (.cons g u) .nil hu hv True.intro
          (reverseOppositeAppend_ne_nil_right u (.cons g.opposite .nil)
            (Word.cons_ne_nil g.opposite .nil)) k scalar))
      (fun h v _ hu hv k scalar =>
        (head_comparison g h).elim
          (fun same =>
            have solve : statement (.cons g u) (.cons g v) :=
              fun hu hv _ scalar =>
                let p := evalQuat u
                let q := evalQuat v
                have inner := scalar_of_scale_five ((common_head_factor g p q).symm.trans scalar)
                congrArg (Word.cons g) (ih v hu.right hv.right (p.conj.mul q).w inner)
            Eq.subst (fun h => statement (.cons g u) (.cons h v)) same solve hu hv k scalar)
          (fun allowed => False.elim
            (joined_not_scalar (.cons g u) (.cons h v) hu hv allowed
              (reverseOppositeAppend_ne_nil_right (.cons g u) (.cons h v) (Word.cons_ne_nil h v))
              k scalar)))) u) v hu hv k scalar

end Omega.Hurwitz.FreeGroup
