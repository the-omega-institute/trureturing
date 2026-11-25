/-
Copyright (c) The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import D5.S3.Quantum.AURICOmega.RationalUnitTripleGram
import OmegaChecks.NatCorrespondence
import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.Ring

/-! Hamilton arithmetic on the integral representative used by the rational Gram construction. -/

open scoped Quaternion
open D5.S3.Quantum.AURICOmega.RationalUnitTripleGram (integerQuaternionEquiv)
open D5.S3.Quantum.AURICOmega.OmegaShadowBridge
  (toStdNat toStdInt toStdInt_add toStdInt_neg toStdInt_mul)
open OmegaChecks.NatCorrespondence (fromStd toStd_fromStd fromStd_toStd)

noncomputable section
namespace OmegaChecks.QuaternionCorrespondence

private def encode : ℤ → Omega.Int
  | .ofNat n => .ofNat (fromStd n)
  | .negSucc n => .negSucc (fromStd n)

private theorem encode_decode (x : Omega.Int) : encode (toStdInt x) = x := by
  induction x using Omega.Int.rec with
  | ofNat n => exact congrArg Omega.Int.ofNat (fromStd_toStd n)
  | negSucc n => exact congrArg Omega.Int.negSucc (fromStd_toStd n)

private theorem decode_encode (x : ℤ) : toStdInt (encode x) = x := by
  cases x with
  | ofNat n => exact congrArg Int.ofNat (toStd_fromStd n)
  | negSucc n => exact congrArg Int.negSucc (toStd_fromStd n)

/-- Interpret the four-coordinate representation over the pinned integers. -/
private def hamilton : Omega.Quaternion ≃ ℍ[ℤ] where
  toFun x := let q := integerQuaternionEquiv x
             ⟨toStdInt q.re, toStdInt q.imI, toStdInt q.imJ, toStdInt q.imK⟩
  invFun q := ⟨encode q.re, encode q.imI, encode q.imJ, encode q.imK⟩
  left_inv q := by
    apply integerQuaternionEquiv.injective
    apply QuaternionAlgebra.ext <;> exact encode_decode _
  right_inv q := Quaternion.ext _ _ (decode_encode _) (decode_encode _) (decode_encode _) (decode_encode _)

private theorem readSub (x y : Omega.Int) : toStdInt (x.sub y) = toStdInt x - toStdInt y := by
  change toStdInt (x.add y.neg) = _
  rw [toStdInt_add, toStdInt_neg, sub_eq_add_neg]

example : hamilton Omega.Quaternion.zero = 0 := rfl
example : hamilton Omega.Quaternion.one = 1 := rfl
example (k : Omega.Int) : hamilton (Omega.Quaternion.scalar k) = (toStdInt k : ℍ[ℤ]) := rfl

example (q : Omega.Quaternion) (k : Omega.Int) : hamilton (q.scale k) = toStdInt k • hamilton q := by
  apply Quaternion.ext <;> exact toStdInt_mul _ _

example (q r : Omega.Quaternion) : hamilton (q.add r) = hamilton q + hamilton r := by
  apply Quaternion.ext <;> exact toStdInt_add _ _

example (q : Omega.Quaternion) : hamilton q.neg = -hamilton q := by
  apply Quaternion.ext <;> exact toStdInt_neg _

example (q r : Omega.Quaternion) : hamilton (q.sub r) = hamilton q - hamilton r := by
  apply Quaternion.ext <;> exact readSub _ _

example (q : Omega.Quaternion) : hamilton q.conj = star (hamilton q) := by
  apply Quaternion.ext <;> simp only [Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star,
    Quaternion.imK_star] <;> first | rfl | exact toStdInt_neg _

example (q r : Omega.Quaternion) : hamilton (q.mul r) = hamilton q * hamilton r := by
  apply Quaternion.ext <;> simp only [hamilton, integerQuaternionEquiv, Equiv.coe_fn_mk,
    Omega.Quaternion.mul, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
    toStdInt_add, toStdInt_mul, readSub]

private theorem dot_re (q r : Omega.Quaternion) : toStdInt (q.dot r) = (star (hamilton q) * hamilton r).re := by
  simp only [Omega.Quaternion.dot, toStdInt_add, toStdInt_mul, Quaternion.re_mul, Quaternion.re_star,
    Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star, hamilton, integerQuaternionEquiv,
    Equiv.coe_fn_mk]
  ring

example (q : Omega.Quaternion) : (toStdNat q.normSq : ℤ) = Quaternion.normSq (hamilton q) := by
  have h : Omega.Int.ofNat q.normSq = q.dot q := Omega.Eq.rec rfl (Omega.Quaternion.normSq_cast q)
  change toStdInt (Omega.Int.ofNat q.normSq) = _
  rw [h, dot_re, Quaternion.star_mul_self, Quaternion.re_coe]

example (q : Omega.Quaternion) : q.Nonzero ↔ hamilton q ≠ 0 := by
  have eqv : Omega.Eq q Omega.Quaternion.zero ↔ q = Omega.Quaternion.zero :=
    ⟨fun h => Omega.Eq.rec rfl h, fun h => h ▸ Omega.rfl⟩
  constructor
  · intro h hzero
    exact Omega.False.elim ((Omega.Quaternion.nonzero_iff_ne_zero q).mp h
      (eqv.mpr (hamilton.injective hzero)))
  · intro h
    exact (Omega.Quaternion.nonzero_iff_ne_zero q).mpr (fun hz => False.elim (h (congrArg hamilton (eqv.mp hz))))

end OmegaChecks.QuaternionCorrespondence
