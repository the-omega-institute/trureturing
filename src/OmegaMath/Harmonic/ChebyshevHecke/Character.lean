/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaMath.Harmonic.ChebyshevHecke.Recurrence

/-!
Omega original.

The trace of a diagonal action on a symmetric power is a two-variable
geometric sum. Its recurrence relates it to the Chebyshev character.
-/

noncomputable section
@[expose] public section

namespace Omega.Chebyshev

variable {A : Type} {relation : A → A → Prop} (r : CommRingOps A relation)

def power (a : A) (n : Nat) : A :=
  Nat.rec r.one (fun _ p => r.mul a p) n

/-- Sum of the monomial eigenvalues (a^{n-k}b^k) for (0le kle n). -/
def symmetricCharacter (a b : A) (n : Nat) : A :=
  Nat.rec r.one (fun k h => r.add (r.mul a h) (power r b k.succ)) n

open Polynomial

theorem symmetric_character_step (law : r.Laws) (a b : A) (n : Nat) :
    r.eqv (symmetricCharacter r a b n.succ.succ)
      (r.sub (r.mul (r.add a b) (symmetricCharacter r a b n.succ))
        (r.mul (r.mul a b) (symmetricCharacter r a b n))) :=
  let previous := (e0.mul e2).add e3
  prove r law (.cons a (.cons b (.cons (symmetricCharacter r a b n)
      (.cons (power r b n.succ) (Variables.nil r)))))
    ((e0.mul previous).add (e1.mul e3))
    (((e0.add e1).mul previous).sub ((e0.mul e1).mul e2)) Eq.refl

theorem symmetric_character_eq_U (law : r.Laws) (a b c : A)
    (sum : r.eqv (r.add a b) (r.mul r.two c)) (product : r.eqv (r.mul a b) r.one)
    (n : Nat) :
    r.eqv (symmetricCharacter r a b n) (U r c n) :=
  let h := symmetricCharacter r a b
  let u := U r c
  let t := r.mul r.two c
  have base : r.eqv (h Nat.zero) (u Nat.zero) := law.symm (U_zero r law c)
  have next : r.eqv (h Nat.zero.succ) (u Nat.zero.succ) :=
    law.trans (law.add_congr (law.mul_one a) (law.mul_one b))
      (law.trans sum (law.symm (U_one r law c)))
  (Nat.rec (motive := fun k => And (r.eqv (h k) (u k)) (r.eqv (h k.succ) (u k.succ)))
    (And.intro base next)
    (fun k ih => And.intro ih.right
      (law.trans (symmetric_character_step r law a b k)
        (law.trans (law.sub_congr (law.mul_congr sum ih.right) (law.mul_congr product ih.left))
          (law.trans (law.sub_congr (law.refl (r.mul t (u k.succ))) (law.one_mul (u k)))
            (law.symm (U_step r law c k)))))) n).left

theorem symmetric_character_even (law : r.Laws) (a b c : A)
    (sum : r.eqv (r.add a b) (r.mul r.two c)) (product : r.eqv (r.mul a b) r.one)
    (n : Nat) :
    r.eqv (symmetricCharacter r a b (n.add n)) (E r (r.square c) n) :=
  law.trans (symmetric_character_eq_U r law a b c sum product (n.add n))
    (law.symm (even_character r law c n))

end Omega.Chebyshev
