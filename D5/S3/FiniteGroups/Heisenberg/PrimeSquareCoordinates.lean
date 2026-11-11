/- GID: D5/S3/FiniteGroups/Heisenberg/PrimeSquareCoordinates
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/Heisenberg/PrimeSquareCoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Residue coordinates for prime-square integers and dual numbers. -/

import D5.S3.FiniteGroups.Heisenberg.DeterminantCharts
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.DualNumber

/-! # The two coefficient rings -/

namespace D5.S3.FiniteGroups.Heisenberg

variable (p : ℕ) [Fact p.Prime]

abbrev PrimeSquare := ZMod (p * p)
abbrev PrimeDual := DualNumber (ZMod p)

def squareCode : PrimeSquare p ≃ ZMod p × ZMod p where
  toFun x := ((x.val : ZMod p), ((x.val / p : ℕ) : ZMod p))
  invFun x := (x.1.val + p * x.2.val : ℕ)
  left_inv x := by
    have hd : x.val / p < p := (Nat.div_lt_iff_lt_mul (NeZero.pos p)).mpr (ZMod.val_lt x)
    change (((x.val : ZMod p).val + p * ((x.val / p : ℕ) : ZMod p).val : ℕ) : PrimeSquare p) = x
    rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hd, Nat.mod_add_div,
      ZMod.natCast_zmod_val]
  right_inv x := by
    have hlt : x.1.val + p * x.2.val < p * p := by
      have ha := ZMod.val_lt x.1
      have hb := ZMod.val_lt x.2
      nlinarith
    apply Prod.ext
    · change ((((x.1.val + p * x.2.val : ℕ) : PrimeSquare p).val : ℕ) : ZMod p) = x.1
      rw [ZMod.val_cast_of_lt hlt]
      simp
    · change (((((x.1.val + p * x.2.val : ℕ) : PrimeSquare p).val / p : ℕ)) : ZMod p) = x.2
      rw [ZMod.val_cast_of_lt hlt, Nat.add_mul_div_left _ _ (NeZero.pos p),
        Nat.div_eq_of_lt (ZMod.val_lt x.1), zero_add, ZMod.natCast_zmod_val]

private theorem square_res_val (x : PrimeSquare p) :
    ZMod.castHom (dvd_mul_right p p) (ZMod p) x = (x.val : ZMod p) := by
  exact ZMod.cast_eq_val x

private theorem square_unit_iff (x : PrimeSquare p) :
    IsUnit x ↔ ZMod.castHom (dvd_mul_right p p) (ZMod p) x ≠ 0 := by
  rw [square_res_val]
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  rw [ZMod.isUnit_iff_coprime, Nat.coprime_mul_iff_right, and_self,
    Nat.coprime_comm, (Fact.out : p.Prime).coprime_iff_not_dvd,
    ne_eq, ZMod.natCast_eq_zero_iff]

private theorem square_mul_mod (n : ℕ) :
    (p : PrimeSquare p) * (n : PrimeSquare p) =
      (p : PrimeSquare p) * (n % p : ℕ) := by
  have hp2 : (p : PrimeSquare p) * (p : PrimeSquare p) = 0 := by
    rw [← Nat.cast_mul, ZMod.natCast_self]
  calc
    (p : PrimeSquare p) * n = p * ((n % p + p * (n / p) : ℕ) : PrimeSquare p) := by
      rw [Nat.mod_add_div]
    _ = p * (n % p : ℕ) := by push_cast; rw [mul_add, ← mul_assoc, hp2]; simp

def squareCoordinates : ResidueCoordinates (PrimeSquare p) (ZMod p) where
  code := squareCode p
  res := ZMod.castHom (dvd_mul_right p p) (ZMod p)
  res_code := square_res_val p
  code_zero := by simp [squareCode]
  unit_iff := square_unit_iff p
  nil_mul a x := by
    change (((0 : ZMod p).val + p * a.val : ℕ) : PrimeSquare p) * x =
      (((0 : ZMod p).val + p * (a * ZMod.castHom (dvd_mul_right p p) (ZMod p) x).val : ℕ) : PrimeSquare p)
    simp only [ZMod.val_zero, zero_add, Nat.cast_mul]
    rw [square_res_val]
    calc
      (p : PrimeSquare p) * (a.val : PrimeSquare p) * x =
          (p : PrimeSquare p) * ((a.val * x.val : ℕ) : PrimeSquare p) := by
        rw [Nat.cast_mul, ZMod.natCast_zmod_val, mul_assoc]
      _ = (p : PrimeSquare p) * ((a.val * x.val) % p : ℕ) := square_mul_mod p _
      _ = (p : PrimeSquare p) * (a * (x.val : ZMod p)).val := by
        congr 1
        simp only [ZMod.val_mul, ZMod.val_natCast, Nat.mul_mod, Nat.mod_mod]

def dualCoordinates : ResidueCoordinates (PrimeDual p) (ZMod p) where
  code := Equiv.refl _
  res :=
    { toFun := TrivSqZeroExt.fst
      map_one' := rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl }
  res_code := fun _ => rfl
  code_zero := rfl
  unit_iff x := TrivSqZeroExt.isUnit_iff_isUnit_fst.trans isUnit_iff_ne_zero
  nil_mul a x := by
    apply TrivSqZeroExt.ext
    · change 0 * x.fst = 0; exact zero_mul _
    · change 0 * x.snd + a * x.fst = a * x.fst; simp

end D5.S3.FiniteGroups.Heisenberg
