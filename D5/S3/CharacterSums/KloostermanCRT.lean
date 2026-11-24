/- GID: D5/S3/CharacterSums/KloostermanCRT
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact coprime factorization of the standard-character Kloosterman unit sum. -/

import D5.S3.CharacterSums.PrimePowerKloostermanStationaryPhase
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Cast.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace D5.S3.CharacterSums.KloostermanCRT

open D5.S3.CharacterSums.PrimePowerKloostermanStationaryPhase (phase kloosterman)

variable {m n : ℕ}

/-- The inverse of `n` modulo `m`, as a unit. -/
def crtLeftInv (h : m.Coprime n) : (ZMod m)ˣ :=
  (ZMod.unitOfCoprime n h.symm)⁻¹

/-- The inverse of `m` modulo `n`, as a unit. -/
def crtRightInv (h : m.Coprime n) : (ZMod n)ˣ :=
  (ZMod.unitOfCoprime m h)⁻¹

/-- The product of the two reductions on units induced by the CRT ring equivalence. -/
def crtUnits (h : m.Coprime n) : (ZMod (m * n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits

private theorem coe_crtUnits_fst (h : m.Coprime n) (x : (ZMod (m * n))ˣ) :
    ((crtUnits h x).1 : ZMod m) = (ZMod.chineseRemainder h (x : ZMod (m * n))).1 :=
  rfl

private theorem coe_crtUnits_snd (h : m.Coprime n) (x : (ZMod (m * n))ˣ) :
    ((crtUnits h x).2 : ZMod n) = (ZMod.chineseRemainder h (x : ZMod (m * n))).2 :=
  rfl

private theorem stdAddChar_natCast {q : ℕ} [NeZero q] (j : ℕ) :
    ZMod.stdAddChar (j : ZMod q) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) / (q : ℂ)) := by
  simpa only [Int.cast_natCast] using (ZMod.stdAddChar_coe (N := q) (j : ℤ))

private theorem stdAddChar_mul_natCast {d q : ℕ} [NeZero d] [NeZero q]
    (k : ℕ) (hq : q = k * d) (x : ZMod d) :
    ZMod.stdAddChar ((k : ZMod q) * (x.val : ZMod q)) = ZMod.stdAddChar x := by
  have hk : (k : ℂ) ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    intro hk
    exact NeZero.ne q (by simp [hq, hk])
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hqC : (q : ℂ) = (k : ℂ) * (d : ℂ) := by rw [hq, Nat.cast_mul]
  calc
    _ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((k * x.val : ℕ) : ℂ) / (q : ℂ)) := by
      rw [← Nat.cast_mul, stdAddChar_natCast]
    _ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x.val : ℂ) / (d : ℂ)) := by
      apply congrArg Complex.exp
      simp only [hqC, Nat.cast_mul]
      field_simp [hk, hd]
    _ = _ := by rw [← stdAddChar_natCast, ZMod.natCast_zmod_val]

variable [NeZero m] [NeZero n]

/-- The standard character splits at the two CRT coordinates, each scaled by
the inverse of the complementary modulus. -/
theorem stdAddChar_crt (h : m.Coprime n) (t : ZMod (m * n)) :
    ZMod.stdAddChar t =
      ZMod.stdAddChar ((crtLeftInv h : ZMod m) * (ZMod.chineseRemainder h t).1) *
      ZMod.stdAddChar ((crtRightInv h : ZMod n) * (ZMod.chineseRemainder h t).2) := by
  let e := ZMod.chineseRemainder h
  let u : ZMod m := (crtLeftInv h : ZMod m) * (e t).1
  let v : ZMod n := (crtRightInv h : ZMod n) * (e t).2
  have hr : (n : ZMod m) * (crtLeftInv h : ZMod m) = 1 :=
    (ZMod.unitOfCoprime n h.symm).mul_inv
  have hs : (m : ZMod n) * (crtRightInv h : ZMod n) = 1 :=
    (ZMod.unitOfCoprime m h).mul_inv
  have hu : (n : ZMod m) * u = (e t).1 := by
    dsimp only [u]
    rw [← mul_assoc, hr, one_mul]
  have hv : (m : ZMod n) * v = (e t).2 := by
    dsimp only [v]
    rw [← mul_assoc, hs, one_mul]
  have hlift : t = (n : ZMod (m * n)) * (u.val : ZMod (m * n)) +
      (m : ZMod (m * n)) * (v.val : ZMod (m * n)) := by
    apply e.injective
    apply Prod.ext
    · simp only [map_add, map_mul, map_natCast, Prod.fst_add, Prod.fst_mul,
        Prod.fst_natCast, ZMod.natCast_zmod_val, ZMod.natCast_self, zero_mul, add_zero, hu]
    · simp only [map_add, map_mul, map_natCast, Prod.snd_add, Prod.snd_mul,
        Prod.snd_natCast, ZMod.natCast_zmod_val, ZMod.natCast_self, zero_mul, zero_add, hv]
  calc
    ZMod.stdAddChar t = ZMod.stdAddChar ((n : ZMod (m * n)) * (u.val : ZMod (m * n)) +
        (m : ZMod (m * n)) * (v.val : ZMod (m * n))) :=
      congrArg (ZMod.stdAddChar (N := m * n)) hlift
    _ = ZMod.stdAddChar u * ZMod.stdAddChar v := by
      rw [AddChar.map_add_eq_mul,
        stdAddChar_mul_natCast (q := m * n) n (Nat.mul_comm m n) u,
        stdAddChar_mul_natCast (q := m * n) m rfl v]

private theorem phase_crt (h : m.Coprime n) (a : ZMod (m * n))
    (b x : (ZMod (m * n))ˣ) :
    phase a (b : ZMod (m * n)) (x : ZMod (m * n)) =
      phase ((crtLeftInv h : ZMod m) * (ZMod.chineseRemainder h a).1)
          (↑(crtLeftInv h * (crtUnits h b).1)) (↑(crtUnits h x).1) *
        phase ((crtRightInv h : ZMod n) * (ZMod.chineseRemainder h a).2)
          (↑(crtRightInv h * (crtUnits h b).2)) (↑(crtUnits h x).2) := by
  simp only [phase, ZMod.inv_coe_unit, stdAddChar_crt h, map_add, map_mul, Prod.fst_add,
    Prod.snd_add, Prod.fst_mul, Prod.snd_mul, ← coe_crtUnits_fst h, ← coe_crtUnits_snd h,
    map_inv, Prod.fst_inv, Prod.snd_inv, Units.val_mul, mul_add, mul_assoc]

/-- The exact unnormalized Kloosterman sum factors at positive coprime moduli.
Both local second coefficients are products in the corresponding unit group. -/
theorem kloosterman_crt (h : m.Coprime n) (a : ZMod (m * n)) (b : (ZMod (m * n))ˣ) :
    kloosterman a b =
      kloosterman ((crtLeftInv h : ZMod m) * (ZMod.chineseRemainder h a).1)
          (crtLeftInv h * (crtUnits h b).1) *
        kloosterman ((crtRightInv h : ZMod n) * (ZMod.chineseRemainder h a).2)
          (crtRightInv h * (crtUnits h b).2) := by
  let f : (ZMod m)ˣ → ℂ := fun x =>
    phase ((crtLeftInv h : ZMod m) * (ZMod.chineseRemainder h a).1)
      (↑(crtLeftInv h * (crtUnits h b).1)) (x : ZMod m)
  let g : (ZMod n)ˣ → ℂ := fun x =>
    phase ((crtRightInv h : ZMod n) * (ZMod.chineseRemainder h a).2)
      (↑(crtRightInv h * (crtUnits h b).2)) (x : ZMod n)
  calc
    kloosterman a b = ∑ x : (ZMod m)ˣ × (ZMod n)ˣ, f x.1 * g x.2 :=
      Fintype.sum_equiv (crtUnits h).toEquiv
        (fun x => phase a (b : ZMod (m * n)) (x : ZMod (m * n)))
        (fun x => f x.1 * g x.2) (phase_crt h a b)
    _ = ∑ x : (ZMod m)ˣ, ∑ y : (ZMod n)ˣ, f x * g y :=
      Fintype.sum_prod_type (fun x => f x.1 * g x.2)
    _ = (∑ x : (ZMod m)ˣ, f x) * (∑ y : (ZMod n)ˣ, g y) :=
      (Fintype.sum_mul_sum f g).symm
    _ = _ := rfl

end D5.S3.CharacterSums.KloostermanCRT
