/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude

public import OmegaMath.Data.SnocList

/-!
Omega original.

On a finite site enumeration, toggling by an odd coloring fixed under a relabeling
reverses parity and gives a pointwise involution on the fixed colorings.
-/

noncomputable section

@[expose] public section

namespace Omega.BooleanColoringParity

variable {Site : Type u}

/-- Reverse a Boolean parity. -/
def flip (b : Bool) : Bool := Bool.rec .true .false b

/-- Exclusive or of two site values or parities. -/
def xor (a b : Bool) : Bool := Bool.rec a (flip a) b

/-- Fold the site values with XOR, starting with even parity. -/
def parity (sites : SnocList Site) (c : Site → Bool) : Bool :=
  SnocList.rec (motive := fun _ => Bool) .false
    (fun _ last earlier => xor earlier (c (last True.intro))) sites

/-- Toggle each site where the mask is true. -/
def toggle (mask c : Site → Bool) : Site → Bool := fun x => xor (c x) (mask x)

/-- The coloring is unchanged at each site by the relabeling. -/
def Fixed (relabel : Site → Site) (c : Site → Bool) : Prop :=
  ∀ x, Eq (c (relabel x)) (c x)

private theorem xor_interchange (a b c d : Bool) :
    Eq (xor (xor a b) (xor c d)) (xor (xor a c) (xor b d)) :=
  Bool.rec
    (Bool.rec
      (Bool.rec (Bool.rec rfl rfl d) (Bool.rec rfl rfl d) c)
      (Bool.rec (Bool.rec rfl rfl d) (Bool.rec rfl rfl d) c) b)
    (Bool.rec
      (Bool.rec (Bool.rec rfl rfl d) (Bool.rec rfl rfl d) c)
      (Bool.rec (Bool.rec rfl rfl d) (Bool.rec rfl rfl d) c) b)
    a

/-- The parity fold takes pointwise XOR to XOR of the parities. -/
theorem parity_toggle (sites : SnocList Site) (mask c : Site → Bool) :
    Eq (parity sites (toggle mask c)) (xor (parity sites c) (parity sites mask)) :=
  SnocList.rec (motive := fun sites =>
      Eq (parity sites (toggle mask c)) (xor (parity sites c) (parity sites mask)))
    rfl
    (fun earlier last ih =>
      let x := last True.intro
      (congrArg (fun b => xor b (xor (c x) (mask x))) ih).trans
        (xor_interchange (parity earlier c) (parity earlier mask) (c x) (mask x)))
    sites

private theorem xor_twice (a b : Bool) : Eq (xor (xor a b) b) a :=
  Bool.rec (Bool.rec rfl rfl b) (Bool.rec rfl rfl b) a

/-- Toggling with the same mask twice restores the value at every site. -/
theorem toggle_twice (mask c : Site → Bool) (x : Site) :
    Eq (toggle mask (toggle mask c) x) (c x) :=
  xor_twice (c x) (mask x)

/-- Toggling two fixed colorings pointwise gives a fixed coloring. -/
theorem fixed_toggle {relabel : Site → Site} {mask c : Site → Bool}
    (maskFixed : Fixed relabel mask) (cFixed : Fixed relabel c) :
    Fixed relabel (toggle mask c) :=
  fun x => (congrArg (fun b => xor b (mask (relabel x))) (cFixed x)).trans
    (congrArg (xor (c x)) (maskFixed x))

/-- An odd fixed mask gives a parity-reversing pointwise involution on fixed colorings. -/
theorem odd_fixed_toggle (sites : SnocList Site) {relabel : Site → Site}
    {mask c : Site → Bool} (maskOdd : Eq (parity sites mask) .true)
    (maskFixed : Fixed relabel mask) (cFixed : Fixed relabel c) :
    And (Eq (parity sites (toggle mask c)) (flip (parity sites c)))
      (And (Fixed relabel (toggle mask c)) (∀ x, Eq (toggle mask (toggle mask c) x) (c x))) :=
  And.intro ((parity_toggle sites mask c).trans (congrArg (xor (parity sites c)) maskOdd))
    (And.intro (fixed_toggle maskFixed cFixed) (toggle_twice mask c))

end Omega.BooleanColoringParity
