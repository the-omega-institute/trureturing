/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel, Adomas Baliuka
-/
module
prelude
public import OmegaInit.Data.Nat.Power2.Basic
import all OmegaInit.Data.Nat.Power2.Basic
import OmegaInit.Data.Nat.Lemmas
import all OmegaInit.WF

namespace Omega.Nat

private abbrev candidate (n k : Nat) := And (Nat.le n k) (isPowerOfTwo k)
private abbrev smallest (n p : Nat) := ∀ k, candidate n k → Nat.le p k
private abbrev answer (n p : Nat) := And (candidate n p) (smallest n p)

private theorem doubleBelow {a b : Nat} (ha : isPowerOfTwo a) (hb : isPowerOfTwo b) (hlt : Nat.lt a b) :
    Nat.le (Nat.mul a 2) b :=
  ha.elim fun i hi => hb.elim fun j hj =>
    let less : Nat.lt (Nat.pow 2 i) (Nat.pow 2 j) :=
      Eq.subst (motive := Nat.lt (Nat.pow 2 i)) hj (Eq.subst (motive := fun a => Nat.lt a b) hi hlt)
    let indices : Nat.lt i j := Nat.lt_of_not_ge fun h =>
      Nat.not_le_of_lt less (Nat.pow_le_pow_right Nat.zero_lt_two h)
    let result : Nat.le (Nat.mul (Nat.pow 2 i) 2) (Nat.pow 2 j) := Nat.pow_le_pow_right Nat.zero_lt_two indices
    Eq.subst (motive := Nat.le (Nat.mul a 2)) hj.symm
      (Eq.subst (motive := fun a => Nat.le (Nat.mul a 2) (Nat.pow 2 j)) hi.symm result)

private abbrev PowerState := PSigma (fun p : Nat => Nat.lt 0 p)
private abbrev dist (n : Nat) (x : PowerState) : Nat := PSigma.casesOn x (fun p _ => Nat.sub n p)
private abbrev step (n : Nat) (x : PowerState) :
    ((y : PowerState) → Nat.lt (dist n y) (dist n x) → Nat) → Nat :=
  PSigma.casesOn (motive := fun x => ((y : PowerState) → Nat.lt (dist n y) (dist n x) → Nat) → Nat) x
    (fun p hp call => @dite Nat (Nat.lt p n) (Nat.decLt p n)
      (fun h => call ⟨Nat.mul p 2, Nat.mul_pos hp Nat.zero_lt_two⟩ (nextPowerOfTwo_dec hp h))
      (fun _ => p))

private noncomputable abbrev run (n fuel p : Nat) (hp : Nat.lt 0 p) (h : Nat.lt (Nat.sub n p) fuel) :=
  WellFounded.Nat.fix.go (motive := fun _ => Nat) (dist n) (step n) fuel ⟨p, hp⟩ h

private theorem checkedRun (n fuel : Nat) :
    ∀ p hp h, isPowerOfTwo p → smallest n p → answer n (run n fuel p hp h) :=
  Nat.rec (motive := fun t => ∀ p hp h, isPowerOfTwo p → smallest n p → answer n (run n t p hp h))
    (fun p _ h _ _ => False.elim (Nat.not_succ_le_zero (Nat.sub n p) h))
    (fun _ ih p hp h power low =>
      Decidable.byCases (p := Nat.lt p n) (dec := Nat.decLt p n)
        (fun lt =>
          let smaller := Nat.lt_of_lt_of_le (nextPowerOfTwo_dec hp lt) (Nat.le_of_lt_succ h)
          let result := ih (Nat.mul p 2) (Nat.mul_pos hp Nat.zero_lt_two) smaller
            (isPowerOfTwo_mul_two_of_isPowerOfTwo power)
            (fun _ hk => doubleBelow power hk.right (Nat.lt_of_lt_of_le lt hk.left))
          Eq.subst (motive := answer n) (dite_eq_left lt).symm result)
        (fun notLt =>
          let result : answer n p := ⟨⟨Nat.le_of_not_gt notLt, power⟩, low⟩
          Eq.subst (motive := answer n) (dite_eq_right notLt).symm result)) fuel

attribute [local semireducible] Nat.nextPowerOfTwo.go

private theorem certified (n : Nat) : answer n (nextPowerOfTwo n) :=
  let size := WellFounded.Nat.eager (Nat.succ (Nat.sub n 1))
  let bound : Nat.lt (Nat.sub n 1) size :=
    Eq.subst (motive := Nat.lt (Nat.sub n 1)) (WellFounded.Nat.eager_eq _).symm (Nat.lt_succ_self _)
  checkedRun n size 1 Nat.zero_lt_one bound isPowerOfTwo_one (fun _ hk => pos_of_isPowerOfTwo hk.right)

private theorem leastIff {n m : Nat} :
    Iff (Eq (nextPowerOfTwo n) m)
      (And (Nat.le n m) (And (isPowerOfTwo m) (∀ k, Nat.le n k → isPowerOfTwo k → Nat.le m k))) :=
  let spec := certified n
  Iff.intro
    (fun eq => Eq.subst (motive := fun x => And (Nat.le n x)
        (And (isPowerOfTwo x) (∀ k, Nat.le n k → isPowerOfTwo k → Nat.le x k))) eq
      ⟨spec.left.left, spec.left.right, fun k hk hp => spec.right k ⟨hk, hp⟩⟩)
    (fun hm => Nat.le_antisymm (spec.right m ⟨hm.left, hm.right.left⟩)
      (hm.right.right _ spec.left.left spec.left.right))

private theorem selfPower {n : Nat} (h : isPowerOfTwo n) : Eq (nextPowerOfTwo n) n :=
  Nat.le_antisymm ((certified n).right n ⟨Nat.le_refl n, h⟩) (certified n).left.left

private theorem notZero : Not (isPowerOfTwo 0) := fun h => Nat.lt_irrefl 0 (pos_of_isPowerOfTwo h)

end Omega.Nat

port_proof Nat.not_isPowerOfTwo_zero using Omega.Nat.notZero
port_proof Nat.nextPowerOfTwo_eq_iff using Omega.Nat.leastIff
port_proof Nat.le_nextPowerOfTwo
port_proof Nat.nextPowerOfTwo_le
port_proof Nat.nextPowerOfTwo_eq_self using Omega.Nat.selfPower
port_proof Nat.isPowerOfTwo_nextPowerOfTwo

public section
namespace Nat
export _root_.Omega.Nat (isPowerOfTwo_nextPowerOfTwo le_nextPowerOfTwo nextPowerOfTwo_eq_iff
  nextPowerOfTwo_eq_self nextPowerOfTwo_le not_isPowerOfTwo_zero)
end Nat

/- The generated proposition equalities have the following dependencies.
Nat.not_isPowerOfTwo_zero._simp_1 and the private Nat.nextPowerOfTwo_eq_iff._simp_1_4
and Nat.nextPowerOfTwo_eq_iff._simp_1_11 use eq_false.
Nat.le_nextPowerOfTwo._simp_1, Nat.isPowerOfTwo_nextPowerOfTwo._simp_1, and the private
Nat.nextPowerOfTwo_eq_iff._simp_1_5 use eq_true.
The private Nat.nextPowerOfTwo_eq_iff._simp_1_6 and Nat.nextPowerOfTwo_eq_iff._simp_1_10
use propext. -/
