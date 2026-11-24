/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaMath.Ternion.Heap.Spinor

/-!
Omega original.

The signed quaternion heap recurrence and its exact rational squared norm at every beat.
-/

noncomputable section

@[expose] public section

namespace Omega.Geometry.Cayley3D

structure SpinorPair where
  current : PythSpinor
  next : PythSpinor

def heapPair (a b : PythSpinor) (n : Nat) : SpinorPair :=
  Nat.rec ⟨a, b⟩ (fun _ t => ⟨t.next, t.next.triad t.current t.next⟩) n

def heapAt (a b : PythSpinor) (n : Nat) : PythSpinor :=
  (heapPair a b n).current

theorem heap_step (a b : PythSpinor) (n : Nat) :
    Eq (heapAt a b n.succ.succ)
      ((heapAt a b n.succ).triad (heapAt a b n) (heapAt a b n.succ)) :=
  Eq.refl

def spinorNormSq (p : PythSpinor) : IntRatio :=
  IntRatio.value (Int.ofNat p.num.normSq) (p.radius.mul p.radius)

theorem heap_norm_preserved (a b : PythSpinor) (n : Nat) :
    IntRatio.Equivalent (spinorNormSq (heapAt a b n)) (IntRatio.ofInt Int.one) :=
  let p := heapAt a b n
  let r := p.radius
  have positive := Nat.succ_ne_zero p.radiusPred
  Eq.subst (fun q => IntRatio.Equivalent (IntRatio.value (Int.ofNat q) (r.mul r)) (IntRatio.ofInt Int.one))
    p.normSq_eq.symm (IntRatio.value_self (r.mul r) (Ternion.nat_mul_ne_zero positive positive))

end Omega.Geometry.Cayley3D
