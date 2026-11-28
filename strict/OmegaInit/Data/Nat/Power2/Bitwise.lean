/-
Copyright (c) 2026 George Rennie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Rennie
-/
module
prelude
public import OmegaInit.Data.Nat.Power2.Basic
public import OmegaInit.Data.Nat.Log2
public import OmegaInit.PropLemmas
import OmegaInit.Data.Nat.Power2.Lemmas
import OmegaInit.Data.Nat.Bitwise.Lemmas
import OmegaInit.Data.Nat.Lemmas
import OmegaInit.Data.Bool

namespace Omega.Nat
private abbrev mask (n : Nat) := Nat.land n (Nat.sub n 1)

private theorem highBit {n : Nat} (nz : Not (Eq n 0)) (nonexact : Not (Eq n (Nat.pow 2 (log2 n)))) :
    Eq (testBit (mask n) (log2 n)) Bool.true :=
  let k := log2 n
  let bounds := (log2_eq_iff nz).mp rfl
  let lower : Nat.lt (Nat.pow 2 k) n := Nat.lt_of_not_ge fun h => nonexact (Nat.le_antisymm h bounds.left)
  let predBound : Nat.le (Nat.pow 2 k) (Nat.sub n 1) :=
    Nat.le_of_succ_le_succ (Eq.subst (motive := Nat.le (Nat.succ (Nat.pow 2 k)))
      (Nat.sub_add_cancel (Nat.pos_of_ne_zero nz)).symm lower)
  let next := testBit_of_two_pow_le_and_two_pow_add_one_gt predBound
    (Nat.lt_of_le_of_lt (Nat.sub_le n 1) bounds.right)
  (testBit_and n (Nat.sub n 1) k).trans
    ((congrArg (fun b => Bool.and b (testBit (Nat.sub n 1) k)) (testBit_log2 nz)).trans next)

private theorem high {n : Nat} (nz : Not (Eq n 0)) (notPow : Not (isPowerOfTwo n)) :
    Eq (testBit (mask n) (log2 n)) Bool.true := highBit nz (fun e => notPow ⟨_, e⟩)

private theorem zeroMask (k : Nat) : Eq (mask (Nat.pow 2 k)) 0 :=
  Decidable.byCases (dec := Nat.decEq (mask (Nat.pow 2 k)) 0) (fun h => h) (fun nonzero =>
    (exists_testBit_of_ne_zero nonzero).elim fun i hi =>
      let x := Nat.pow 2 k
      let bit := (Bool.and_eq_true_iff.mp ((testBit_and x (Nat.sub x 1) i).symm.trans hi))
      Decidable.byCases (dec := Nat.decEq k i)
        (fun eq =>
          let below := Nat.sub_lt (Nat.two_pow_pos k) Nat.zero_lt_one
          let lower := testBit_lt_two_pow (i := k) below
          let neither := Eq.subst (motive := fun i => Eq (testBit (Nat.sub x 1) i) Bool.false) eq lower
          False.elim (Bool.ne_false_of_eq_true bit.right neither))
        (fun distinct => False.elim (Bool.ne_false_of_eq_true bit.left (testBit_two_pow_of_ne distinct))))

private theorem maskIff {n : Nat} (nz : Not (Eq n 0)) : Iff (Eq (mask n) 0) (isPowerOfTwo n) :=
  Iff.intro
    (fun empty => Decidable.byCases (dec := Nat.decEq n (Nat.pow 2 (log2 n)))
      (fun yes => Exists.intro (log2 n) yes)
      (fun no =>
        let here := highBit nz no
        let off := (congrArg (fun v => testBit v (log2 n)) empty).trans (zero_testBit (log2 n))
        False.elim (Bool.ne_false_of_eq_true here off)))
    (fun power => power.elim fun k eq => Eq.subst (motive := fun n => Eq (mask n) 0) eq.symm (zeroMask k))

private theorem nonzeroMaskIff {n : Nat} : Iff (And (Not (Eq n 0)) (Eq (mask n) 0)) (isPowerOfTwo n) :=
  Iff.intro (fun h => (maskIff h.left).mp h.right)
    (fun h => let nz := Nat.ne_of_gt (pos_of_isPowerOfTwo h)
              And.intro nz ((maskIff nz).mpr h))

end Omega.Nat
port_proof Nat.and_sub_one_testBit_log2 using Omega.Nat.high
port_proof Nat.and_sub_one_eq_zero_iff_isPowerOfTwo using Omega.Nat.maskIff
port_proof Nat.ne_zero_and_sub_one_eq_zero_iff_isPowerOfTwo using Omega.Nat.nonzeroMaskIff
port_definition Nat.instDecidableIsPowerOfTwo with_native_code
attribute [instance] Omega.Nat.instDecidableIsPowerOfTwo

public section
namespace Nat
export _root_.Omega.Nat (and_sub_one_eq_zero_iff_isPowerOfTwo and_sub_one_testBit_log2
  instDecidableIsPowerOfTwo ne_zero_and_sub_one_eq_zero_iff_isPowerOfTwo)
end Nat

/- The private Nat.ne_zero_and_sub_one_eq_zero_iff_isPowerOfTwo._simp_1_3 needs eq_false
to rewrite a refuted proposition to False. -/
