/- GID: D5/S3/Arith/CharacterSums/PascadiQuadraticDirection
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiQuadraticDirection
   mirror-E: none(waiver:quadratic-direction-resultant)
   anchors: []
   utility: none
   digest: Collinear leading data give a sixth-power quadratic resultant gap. -/

import D5.S3.Arith.CharacterSums.PascadiPrimeCubeSingularCover

/-! A common integer direction in the linear and quadratic leading entries
removes the irrelevant baseline factor before the height comparison. The
cofactor argument was suggested by Pro; the explicit resultant factorization
and its unit-cancellation identity were independently derived by Codex. -/

open Polynomial

namespace D5.S3.Arith.CharacterSums.PrimeCube

noncomputable section

private def directionBracket (a b c : Fin 3 → ℤ) : ℤ :=
  a 0*b 1*c 2+a 1*b 2*c 0+a 2*b 0*c 1-
    a 0*b 2*c 1-a 1*b 0*c 2-a 2*b 1*c 0

/-- The cofactor quadric for the three actual coefficient rows. -/
def directionResidual (l q r k : Fin 3 → ℤ) (d n : ℤ) : ℤ :=
  -directionBracket r l k*directionBracket q r l+
    d*directionBracket q l k*directionBracket q r k-
    n*(directionBracket q l k)^2

private def directionFactor (l q r k : Fin 3 → ℤ) (d n : ℤ) : ℤ :=
  d^2*k 0*q 0-d*l 0*r 0+n*(l 0)^2

private theorem direction_pair_eq {R : Type*} [CommRing R]
    (l q r k : Fin 3 → R) (d n : R) (i : Fin 3) :
    pair l (fun j => d*k j) q r (fun j => n*k j) i =
      quadratic (l 0*q i-l i*q 0)
        (l 0*r i+d*k 0*q i-l i*r 0-d*k i*q 0)
        (n*(l 0*k i-l i*k 0)+d*(k 0*r i-k i*r 0)) := by
  unfold pair linear quadratic
  simp only [map_add, map_sub, map_mul]
  ring

private theorem direction_resultant_identity (l q r k : Fin 3 → ℤ) (d n : ℤ) :
    (pair l (fun i => d*k i) q r (fun i => n*k i) 1).resultant
      (pair l (fun i => d*k i) q r (fun i => n*k i) 2) 2 2 =
      -directionFactor l q r k d n*directionResidual l q r k d n := by
  rw [quadratic_resultant_formula]
  simp only [direction_pair_eq]
  simp only [quadratic, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  norm_num
  unfold directionFactor directionResidual directionBracket
  ring

private theorem direction_factor_identity (l q r k : Fin 3 → ℤ) (d n b : ℤ) :
    (l 0*k 1-l 1*k 0)*directionFactor l q r k d n =
      (pair l (fun i => d*k i) q r (fun i => n*k i) 1).coeff 2*
          (l 0+b*(d*k 0))^2-
        (d*k 0)*(l 0+b*(d*k 0))*
          (pair l (fun i => d*k i) q r (fun i => n*k i) 1).derivative.eval b+
        (d*k 0)^2*(pair l (fun i => d*k i) q r (fun i => n*k i) 1).eval b := by
  simp only [direction_pair_eq]
  simp only [quadratic, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C,
    derivative_add, derivative_C, derivative_C_mul_X, derivative_C_mul_X_sq,
    eval_add, eval_C, eval_mul, eval_X, eval_pow, directionFactor]
  norm_num
  ring

private theorem direction_factor_unit (l q r k : Fin 3 → ℤ) (d n : ℤ)
    (p : ℕ) [Fact p.Prime] (b : ℤ)
    (hlead : ((pair l (fun i => d*k i) q r (fun i => n*k i) 1).coeff 2 :
      ZMod p) ≠ 0)
    (hL : IsUnit ((l 0+b*(d*k 0) : ℤ) : ZMod p))
    (hv : (p : ℤ) ∣ (pair l (fun i => d*k i) q r (fun i => n*k i) 1).eval b)
    (hd : (p : ℤ) ∣
      (pair l (fun i => d*k i) q r (fun i => n*k i) 1).derivative.eval b) :
    IsUnit ((directionFactor l q r k d n : ℤ) : ZMod p) := by
  have hvalue : (((pair l (fun i => d*k i) q r (fun i => n*k i) 1).eval b : ℤ) :
      ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hv
  have hderiv : (((pair l (fun i => d*k i) q r (fun i => n*k i) 1).derivative.eval b : ℤ) :
      ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd
  have heq := congrArg (Int.castRingHom (ZMod p)) (direction_factor_identity l q r k d n b)
  have hprod : (((l 0*k 1-l 1*k 0 : ℤ) : ZMod p))*
      ((directionFactor l q r k d n : ℤ) : ZMod p) =
      (((pair l (fun i => d*k i) q r (fun i => n*k i) 1).coeff 2 : ℤ) : ZMod p)*
        (((l 0+b*(d*k 0) : ℤ) : ZMod p))^2 := by
    simpa only [map_mul, map_sub, map_add, map_pow, Int.coe_castRingHom,
      Int.cast_mul, Int.cast_sub, Int.cast_add, Int.cast_pow,
      hvalue, hderiv, mul_zero, zero_mul, sub_zero, add_zero] using heq
  apply isUnit_iff_ne_zero.mpr
  intro hz
  rw [hz, mul_zero] at hprod
  exact mul_ne_zero hlead (pow_ne_zero 2 hL.ne_zero) hprod.symm

private theorem direction_residual_dvd_fifth (l q r k : Fin 3 → ℤ) (d n : ℤ)
    (p : ℕ) [Fact p.Prime] (b : ℤ)
    (h₁ : (pair l (fun i => d*k i) q r (fun i => n*k i) 1).natDegree = 2)
    (h₂ : (pair l (fun i => d*k i) q r (fun i => n*k i) 2).natDegree = 2)
    (hv₁ : (p : ℤ)^3 ∣ (pair l (fun i => d*k i) q r (fun i => n*k i) 1).eval b)
    (hv₂ : (p : ℤ)^3 ∣ (pair l (fun i => d*k i) q r (fun i => n*k i) 2).eval b)
    (hd₁ : (p : ℤ) ∣ (pair l (fun i => d*k i) q r (fun i => n*k i) 1).derivative.eval b)
    (hd₂ : (p : ℤ) ∣ (pair l (fun i => d*k i) q r (fun i => n*k i) 2).derivative.eval b)
    (hlead : ((pair l (fun i => d*k i) q r (fun i => n*k i) 1).coeff 2 : ZMod p) ≠ 0)
    (hL : IsUnit ((l 0+b*(d*k 0) : ℤ) : ZMod p)) :
    (p : ℤ)^5 ∣ directionResidual l q r k d n := by
  have hv : (p : ℤ) ∣
      (pair l (fun i => d*k i) q r (fun i => n*k i) 1).eval b := by
    simpa only [pow_one] using
      (pow_dvd_pow (p : ℤ) (by decide : 1 ≤ 3)).trans hv₁
  have hunit := direction_factor_unit l q r k d n p b hlead hL hv hd₁
  have hcop : IsCoprime (p : ℤ) (directionFactor l q r k d n) :=
    (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).coprime_iff_not_dvd.mpr
      (by simpa only [← ZMod.intCast_zmod_eq_zero_iff_dvd] using hunit.ne_zero)
  have hdiv := quadratic_resultant_dvd_fifth _ _ b (p : ℤ) h₁ h₂ hv₁ hv₂ hd₁ hd₂
  rw [h₁, h₂, direction_resultant_identity] at hdiv
  have hmul : (p : ℤ)^5 ∣ directionResidual l q r k d n*directionFactor l q r k d n := by
    have hpos : (p : ℤ)^5 ∣
        directionFactor l q r k d n*directionResidual l q r k d n := by
      apply dvd_neg.mp
      simpa only [neg_mul] using hdiv
    simpa only [mul_comm] using hpos
  exact (hcop.pow_left (m := 5)).dvd_of_dvd_mul_right hmul

private theorem direction_bracket_bound (a b c : Fin 3 → ℤ) (A B C : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (ha : ∀ i, |(a i : ℝ)| ≤ A) (hb : ∀ i, |(b i : ℝ)| ≤ B)
    (hc : ∀ i, |(c i : ℝ)| ≤ C) :
    |(directionBracket a b c : ℝ)| ≤ 6*A*B*C := by
  have ht (i j k : Fin 3) : |(a i : ℝ)*(b j : ℝ)*(c k : ℝ)| ≤ A*B*C := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (ha i) (hb j) (abs_nonneg _) hA) (hc k)
      (abs_nonneg _) (mul_nonneg hA hB)
  have h₁ := abs_le.mp (ht 0 1 2)
  have h₂ := abs_le.mp (ht 1 2 0)
  have h₃ := abs_le.mp (ht 2 0 1)
  have h₄ := abs_le.mp (ht 0 2 1)
  have h₅ := abs_le.mp (ht 1 0 2)
  have h₆ := abs_le.mp (ht 2 1 0)
  simp only [directionBracket, Int.cast_add, Int.cast_sub, Int.cast_mul]
  apply abs_le.mpr
  constructor <;> linarith

private theorem direction_residual_height (l q r k : Fin 3 → ℤ) (d n : ℤ)
    (I J D : ℝ) (hI : 0 ≤ I) (hJ : 0 ≤ J) (hD : 0 ≤ D)
    (hq : ∀ i, |(q i : ℝ)| ≤ I^2)
    (hr : ∀ i, |(r i : ℝ)| ≤ 2*I*J)
    (hl : ∀ i, |(l i : ℝ)| ≤ 3*I)
    (hk : ∀ i, |(k i : ℝ)| ≤ D)
    (hd : |(d : ℝ)| *D ≤ 3*J) (hn : |(n : ℝ)| *D ≤ J^2)
    (hDupper : D ≤ 3*J^2) :
    |(directionResidual l q r k d n : ℝ)| ≤ 6804*I^6*J^4 := by
  have hA : |(directionBracket r l k : ℝ)| ≤ 36*I^2*J*D := by
    convert direction_bracket_bound r l k (2*I*J) (3*I) D
      (by positivity) (by positivity) hD hr hl hk using 1 <;> ring
  have hB : |(directionBracket q l k : ℝ)| ≤ 18*I^3*D := by
    convert direction_bracket_bound q l k (I^2) (3*I) D
      (by positivity) (by positivity) hD hq hl hk using 1 <;> ring
  have hC : |(directionBracket q r k : ℝ)| ≤ 12*I^3*J*D := by
    convert direction_bracket_bound q r k (I^2) (2*I*J) D
      (by positivity) (by positivity) hD hq hr hk using 1 <;> ring
  have hE : |(directionBracket q r l : ℝ)| ≤ 36*I^4*J := by
    convert direction_bracket_bound q r l (I^2) (2*I*J) (3*I)
      (by positivity) (by positivity) (by positivity) hq hr hl using 1 <;> ring
  have hAE := mul_le_mul hA hE (abs_nonneg _) (by positivity : 0 ≤ 36*I^2*J*D)
  have hdBC := mul_le_mul
    (mul_le_mul_of_nonneg_left hB (abs_nonneg (d : ℝ))) hC (abs_nonneg _)
    (by positivity : 0 ≤ |(d : ℝ)| *(18*I^3*D))
  have hnBB := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (abs_nonneg _) hB 2) (abs_nonneg (n : ℝ))
  have habs : |(directionResidual l q r k d n : ℝ)| ≤
      |(directionBracket r l k : ℝ)| *|(directionBracket q r l : ℝ)| +
      |(d : ℝ)| *|(directionBracket q l k : ℝ)| *|(directionBracket q r k : ℝ)| +
      |(n : ℝ)| *|(directionBracket q l k : ℝ)| ^2 := by
    simp only [directionResidual, Int.cast_add, Int.cast_sub, Int.cast_mul,
      Int.cast_neg, Int.cast_pow]
    have ht (a b c : ℝ) : |a + b - c| ≤ |a| + |b| + |c| := by
      exact (abs_sub (a + b) c).trans
        (add_le_add (abs_add_le a b) (le_refl |c|))
    have hh := ht
      (-(directionBracket r l k : ℝ)*(directionBracket q r l : ℝ))
      ((d : ℝ)*(directionBracket q l k : ℝ)*(directionBracket q r k : ℝ))
      ((n : ℝ)*(directionBracket q l k : ℝ)^2)
    rw [show |(n : ℝ)*(directionBracket q l k : ℝ)^2| =
      |(n : ℝ)| * |(directionBracket q l k : ℝ)|^2 by rw [abs_mul, abs_pow]] at hh
    simpa only [abs_mul, abs_neg] using hh
  have hsum := habs.trans (add_le_add (add_le_add hAE hdBC) hnBB)
  have hd' := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 216*I^6*J*D)
  have hn' := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ 324*I^6*D)
  have hD' := mul_le_mul_of_nonneg_left hDupper (by positivity : 0 ≤ 2268*I^6*J^2)
  nlinarith only [hsum, hd', hn', hD']

/-- Collinear leading data need only a sixth-power cofactor height gap.
No primitive-direction or nonzero-coordinate assumption is required; the
nonzero quadratic reduction makes the discarded baseline factor a unit. -/
theorem quadratic_direction_resultant_zero (l q r k : Fin 3 → ℤ) (d n : ℤ)
    (p : ℕ) [Fact p.Prime] (b : ℤ) (I J D : ℝ)
    (hI : 0 ≤ I) (hJ : 0 ≤ J) (hD : 0 ≤ D)
    (hq : ∀ i, |(q i : ℝ)| ≤ I^2)
    (hr : ∀ i, |(r i : ℝ)| ≤ 2*I*J)
    (hl : ∀ i, |(l i : ℝ)| ≤ 3*I)
    (hk : ∀ i, |(k i : ℝ)| ≤ D)
    (hd : |(d : ℝ)| *D ≤ 3*J) (hn : |(n : ℝ)| *D ≤ J^2)
    (hDupper : D ≤ 3*J^2)
    (h₁ : (pair l (fun i => d*k i) q r (fun i => n*k i) 1).natDegree = 2)
    (h₂ : (pair l (fun i => d*k i) q r (fun i => n*k i) 2).natDegree = 2)
    (hv₁ : (p : ℤ)^3 ∣ (pair l (fun i => d*k i) q r (fun i => n*k i) 1).eval b)
    (hv₂ : (p : ℤ)^3 ∣ (pair l (fun i => d*k i) q r (fun i => n*k i) 2).eval b)
    (hd₁ : (p : ℤ) ∣ (pair l (fun i => d*k i) q r (fun i => n*k i) 1).derivative.eval b)
    (hd₂ : (p : ℤ) ∣ (pair l (fun i => d*k i) q r (fun i => n*k i) 2).derivative.eval b)
    (hlead : ((pair l (fun i => d*k i) q r (fun i => n*k i) 1).coeff 2 : ZMod p) ≠ 0)
    (hL : IsUnit ((l 0+b*(d*k 0) : ℤ) : ZMod p))
    (hgap : 6804*I^6*J^4 < (p : ℝ)^5) :
    (pair l (fun i => d*k i) q r (fun i => n*k i) 1).resultant
      (pair l (fun i => d*k i) q r (fun i => n*k i) 2) 2 2 = 0 := by
  have hdiv := direction_residual_dvd_fifth l q r k d n p b
    h₁ h₂ hv₁ hv₂ hd₁ hd₂ hlead hL
  have hbound := direction_residual_height l q r k d n I J D hI hJ hD hq hr hl hk hd hn hDupper
  have hz : directionResidual l q r k d n = 0 := by
    by_contra hne
    have hle : (p : ℝ)^5 ≤ |(directionResidual l q r k d n : ℝ)| := by
      exact_mod_cast Int.le_abs_of_dvd hne hdiv
    exact (not_lt_of_ge hle) (hbound.trans_lt hgap)
  rw [direction_resultant_identity, hz, mul_zero]

end

end D5.S3.Arith.CharacterSums.PrimeCube
