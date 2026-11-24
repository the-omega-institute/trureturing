/- GID: D5/S3/VertexAlgebra/Characters/ActualLeechOrbifoldFaberLogarithm
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Characters/ActualLeechOrbifoldFaberLogarithm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The formal logarithmic denominator identity from the native Faber–Hecke expansion. -/

import D5.S3.VertexAlgebra.Characters.ActualLeechOrbifoldFaberPolynomial
import Mathlib.RingTheory.PowerSeries.Log

/-! The Faber generating function follows from a coefficientwise telescoping
identity for the native character. Its positive bidegree coefficients give
the logarithmic side of the Koike–Norton–Zagier product. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Nat

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldFaberLogarithm

open PowerSeries
open ActualLeechOrbifoldFaberPolynomial
  (normalizedCharacter characterLaurent characterLaurent_eq faberPolynomial
    eq_faberPolynomial_of_polar faberPolynomial_eval₂_characterLaurent_eq_hecke)
open ActualLeechOrbifoldHeckeExpansion (heckeCoeff)

local notation "c" => ActualLeechOrbifoldHeckeExpansion.coeff
local notation "ι" => HahnSeries.ofPowerSeries ℤ ℂ
local notation "qPole" => (HahnSeries.single (-1 : ℤ) (1 : ℂ))

section Logarithm

variable {A B : Type*} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]

omit [Algebra ℚ A] in
private theorem hasSubst_sub_one {F : PowerSeries A} (hF : constantCoeff F = 1) :
    HasSubst (F - 1) :=
  HasSubst.of_constantCoeff_zero' (by simp [hF])

/-- The logarithmic derivative of a constant-one formal series. -/
theorem derivative_logOf_mul {F : PowerSeries A} (hF : constantCoeff F = 1) :
    derivative (logOf F) * F = derivative F := by
  have hs := hasSubst_sub_one hF
  have hsubst := congrArg (subst (F - 1)) (derivative_log_mul_one_add_X (A := A))
  rw [subst_mul hs, subst_add hs, subst_X hs, ← coe_substAlgHom hs, map_one] at hsubst
  rw [coe_substAlgHom hs, show (1 + (F - 1) : PowerSeries A) = F by ring] at hsubst
  rw [logOf_eq, derivative_subst hs, map_sub, derivative_one, sub_zero]
  calc
    _ = ((derivative (log A)).subst (F - 1) * F) * derivative F := by ring
    _ = derivative F := by rw [hsubst, one_mul]

/-- The formal logarithm sends multiplication of constant-one series to addition. -/
theorem logOf_mul {F G : PowerSeries A} (hF : constantCoeff F = 1)
    (hG : constantCoeff G = 1) : logOf (F * G) = logOf F + logOf G := by
  have hFG : constantCoeff (F * G) = 1 := by simp [hF, hG]
  let : HasUniqueDiv A := .of_module_rat A
  apply derivative.ext
  · apply (isUnit_iff_constantCoeff.mpr (by simp [hFG]) :
        IsUnit (F * G)).mul_right_cancel
    rw [derivative_logOf_mul hFG, Derivation.leibniz, map_add, add_mul]
    simp only [smul_eq_mul]
    calc
      _ = (derivative (logOf F) * F) * G + (derivative (logOf G) * G) * F := by
        rw [derivative_logOf_mul hF, derivative_logOf_mul hG]
        ring
      _ = _ := by ring
  · simp [constantCoeff_logOf hF, constantCoeff_logOf hG, constantCoeff_logOf hFG]

/-- Constant-one formal logarithms commute with coefficient ring homomorphisms. -/
theorem map_logOf (f : A →+* B) {F : PowerSeries A} (hF : constantCoeff F = 1) :
    (logOf F).map f = logOf (F.map f) := by
  unfold logOf
  change MvPowerSeries.map f ((log A).subst (F - 1)) = _
  rw [PowerSeries.map_subst (h := f) (hasSubst_sub_one hF) (log A)]
  change ((log A).map f).subst ((F - 1).map f) = _
  rw [map_log, map_sub, map_one]

private theorem logOf_one : logOf (1 : PowerSeries A) = 0 := by
  rw [logOf_eq, sub_self, subst_zero_of_constantCoeff_zero constantCoeff_log]

private theorem neg_natCast_mul_coeff_logOf_one_sub (a : A) {n : ℕ} (hn : 0 < n) :
    -(n : A) * coeff n (logOf (1 - C a * X : PowerSeries A)) = a ^ n := by
  have hlog : logOf (1 - C a * X : PowerSeries A) = rescale a (rescale (-1) (log A)) := by
    rw [logOf_eq, rescale_rescale, rescale_eq_subst, neg_one_mul, smul_eq_C_mul, map_neg]
    congr 1
    ring
  have hRat : (-(n : ℚ)) * ((-1 : ℚ) ^ n * ((-1 : ℚ) ^ (n + 1) / (n : ℚ))) = 1 := by
    have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [pow_succ, ← mul_div_assoc, ← mul_assoc, ← mul_pow]
    norm_num
    field_simp
  have hA := congrArg (algebraMap ℚ A) hRat
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast] at hA
  rw [hlog, coeff_rescale, coeff_rescale, coeff_log, ite_eq_right hn.ne']
  rw [mul_left_comm, hA, mul_one]

end Logarithm

private theorem constantCoeff_map_eq {A B : Type*} [Semiring A] [Semiring B]
    (f : A →+* B) (F : PowerSeries A) :
    constantCoeff (F.map f) = f (constantCoeff F) := rfl

/-- The ordinary series (p(J(p)-u)), in the outer variable (p). -/
def characterDifference {A : Type*} [CommRing A] (f : ℂ →+* A) (u : A) :
    PowerSeries A :=
  normalizedCharacter.map f - X * C u

@[simp]
theorem constantCoeff_characterDifference {A : Type*} [CommRing A]
    (f : ℂ →+* A) (u : A) : constantCoeff (characterDifference f u) = 1 := by
  simp [characterDifference, normalizedCharacter, constantCoeff_map_eq]

private theorem coeff_characterDifference_succ {A : Type*} [CommRing A]
    (f : ℂ →+* A) (u : A) (i : ℕ) :
    coeff (i + 1) (characterDifference f u) = f (c i) - if i = 0 then u else 0 := by
  simp [characterDifference, normalizedCharacter, coeff_succ_X_mul, coeff_X, ite_mul]

private def characterTail (i : ℕ) : PowerSeries ℂ :=
  mk fun j => c (i + j)

private theorem characterTail_step (i : ℕ) :
    characterTail i = X * characterTail (i + 1) + C (c i) := by
  ext j
  cases j with
  | zero =>
    rw [coeff_zero_eq_constantCoeff_apply]
    simp [characterTail]
  | succ j =>
    simp only [characterTail, coeff_mk, map_add, coeff_succ_X_mul, coeff_succ_C, add_zero]
    congr 1
    omega

/-- The positive quadrant of the Monster denominator, with (p) outermost. -/
def denominator : PowerSeries (PowerSeries ℂ) :=
  1 - X * mk (fun i => X * characterTail (i + 1))

@[simp]
theorem constantCoeff_denominator : constantCoeff denominator = 1 := by
  simp [denominator]

private theorem coeff_denominator_succ (i : ℕ) :
    coeff (i + 1) denominator = -(X * characterTail (i + 1)) := by
  simp [denominator, coeff_succ_X_mul]

/-- The coefficient of (p^{i+1}q^{j+1}) in the denominator. -/
theorem coeff_coeff_denominator_succ (i j : ℕ) :
    coeff (j + 1) (coeff (i + 1) denominator) = -c (i + j + 1) := by
  rw [coeff_denominator_succ, map_neg, coeff_succ_X_mul]
  simp [characterTail, Nat.add_right_comm]

private theorem qPole_mul_image_X (F : PowerSeries ℂ) :
    qPole * ι (X * F) = ι F := by
  rw [map_mul, HahnSeries.ofPowerSeries_X, ← mul_assoc, HahnSeries.single_mul_single]
  simp

/-- In Laurent coefficients, (p(J(p)-J(q))=(1-p/q)D(p,q)).
At each outer coefficient the adjacent (q)-tails telescope. -/
theorem characterDifference_factorization :
    characterDifference HahnSeries.C characterLaurent =
      (1 - C qPole * X) * denominator.map ι := by
  apply PowerSeries.ext
  intro i
  cases i with
  | zero =>
    simp [constantCoeff_map_eq]
  | succ i =>
    rw [coeff_characterDifference_succ, sub_mul, one_mul, mul_assoc, map_sub,
      coeff_map, coeff_denominator_succ, map_neg, coeff_C_mul, coeff_succ_X_mul, coeff_map]
    cases i with
    | zero =>
      rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_denominator, RingHom.map_one ι, mul_one,
        characterLaurent_eq]
      have htail : mk c = X * characterTail 1 := by
        simpa [characterTail] using characterTail_step 0
      rw [htail]
      simp only [ActualLeechOrbifoldHeckeExpansion.coeff_zero, map_zero, ite_true]
      ring
    | succ i =>
      rw [coeff_denominator_succ, map_neg ι]
      have hmul : qPole * (-ι (X * characterTail (i + 1))) = -ι (characterTail (i + 1)) := by
        calc
          _ = -(qPole * ι (X * characterTail (i + 1))) := by ring
          _ = _ := congrArg Neg.neg (qPole_mul_image_X _)
      rw [hmul, characterTail_step (i + 1), map_add, HahnSeries.ofPowerSeries_C]
      simp only [Nat.succ_ne_zero, ite_false, sub_zero]
      ring

/-- The polynomial (-n[p^n]log(p(J(p)-T))), with (T) the polynomial variable. -/
def logarithmicFaberPolynomial (n : ℕ) : Polynomial ℂ :=
  -(n : Polynomial ℂ) *
    coeff n (logOf (characterDifference Polynomial.C Polynomial.X))

local notation "evalJ" =>
  Polynomial.eval₂RingHom (HahnSeries.C : ℂ →+* LaurentSeries ℂ) characterLaurent

/-- Taking the logarithmic Faber coefficient commutes with evaluation at (J(q)). -/
theorem eval_logarithmicFaberPolynomial (n : ℕ) :
    (logarithmicFaberPolynomial n).eval₂ HahnSeries.C characterLaurent =
      -(n : LaurentSeries ℂ) * coeff n (logOf (characterDifference HahnSeries.C characterLaurent)) := by
  have hmap :
      (characterDifference Polynomial.C Polynomial.X).map evalJ =
        characterDifference HahnSeries.C characterLaurent := by
    rw [characterDifference, characterDifference, map_sub, map_mul, map_X, map_C]
    change normalizedCharacter.map ((evalJ).comp Polynomial.C) - X * C (evalJ Polynomial.X) = _
    have hX : evalJ Polynomial.X = characterLaurent := Polynomial.eval₂_X _ _
    rw [Polynomial.eval₂RingHom_comp_C, hX]
  have hlog := map_logOf evalJ (constantCoeff_characterDifference Polynomial.C Polynomial.X)
  rw [hmap] at hlog
  change evalJ (logarithmicFaberPolynomial n) = _
  rw [logarithmicFaberPolynomial, map_mul, map_neg, map_natCast]
  have hcoeff := congrArg (coeff (R := LaurentSeries ℂ) n) hlog
  rw [coeff_map] at hcoeff
  rw [hcoeff]

/-- The inner constant term of the negative formal logarithm vanishes in every
outer degree, expressing its strictly positive (q)-order. -/
theorem constantCoeff_coeff_neg_logOf_denominator (n : ℕ) :
    constantCoeff (coeff n (-logOf denominator)) = 0 := by
  have hmap : denominator.map (constantCoeff (R := ℂ)) = 1 := by
    apply PowerSeries.ext
    intro i
    cases i with
    | zero => simp
    | succ i => simp [coeff_denominator_succ]
  rw [← coeff_map, map_neg, map_logOf _ constantCoeff_denominator, hmap, logOf_one, neg_zero,
    map_zero]

/-- The outer constant term of the negative formal logarithm vanishes. -/
theorem constantCoeff_neg_logOf_denominator : constantCoeff (-logOf denominator) = 0 := by
  rw [map_neg, constantCoeff_logOf constantCoeff_denominator, neg_zero]

private theorem hahn_C_natCast (n : ℕ) :
    (HahnSeries.C (n : ℂ) : LaurentSeries ℂ) = n :=
  map_natCast (HahnSeries.C : ℂ →+* LaurentSeries ℂ) n

private theorem eval_logarithmicFaberPolynomial_eq {n : ℕ} (hn : 0 < n) :
    (logarithmicFaberPolynomial n).eval₂ HahnSeries.C characterLaurent =
      HahnSeries.single (-(n : ℤ)) 1 +
        HahnSeries.C (n : ℂ) * ι (coeff n (-logOf denominator)) := by
  have hlinear : constantCoeff (1 - C qPole * X : PowerSeries (LaurentSeries ℂ)) = 1 := by simp
  have hmap : constantCoeff (denominator.map ι) = 1 := by simp [constantCoeff_map_eq]
  rw [eval_logarithmicFaberPolynomial, characterDifference_factorization, logOf_mul hlinear hmap,
    map_add, mul_add, neg_natCast_mul_coeff_logOf_one_sub qPole hn, ← map_logOf ι
      constantCoeff_denominator, coeff_map, HahnSeries.single_pow]
  simp

/-- The polynomial extracted from the formal logarithm is the independently
constructed native Faber polynomial. -/
theorem logarithmicFaberPolynomial_eq_faberPolynomial {n : ℕ} (hn : 0 < n) :
    logarithmicFaberPolynomial n = faberPolynomial n := by
  apply eq_faberPolynomial_of_polar
  intro m
  rw [eval_logarithmicFaberPolynomial_eq hn, HahnSeries.coeff_add,
    HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  have hq : (ι (coeff n (-logOf denominator))).coeff (-(m : ℤ)) = 0 := by
    cases m with
    | zero =>
      change (ι (coeff n (-logOf denominator))).coeff ((0 : ℕ) : ℤ) = 0
      rw [HahnSeries.ofPowerSeries_apply_coeff, coeff_zero_eq_constantCoeff_apply,
        constantCoeff_coeff_neg_logOf_denominator]
    | succ m => rw [PowerSeries.coeff_coe, ite_eq_left (by omega)]
  rw [hq, mul_zero, add_zero, HahnSeries.coeff_single]
  simp

/-- The Laurent series of the (n)-th outer coefficient of (-log D)
is the normalized Faber value with its pole removed. -/
theorem coeff_neg_logOf_denominator_eq_faber {n : ℕ} (hn : 0 < n) :
    ι (coeff n (-logOf denominator)) =
      ((faberPolynomial n).eval₂ HahnSeries.C characterLaurent -
        HahnSeries.single (-(n : ℤ)) 1) / (n : LaurentSeries ℂ) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hn' : (n : LaurentSeries ℂ) ≠ 0 := hahn_C_natCast n ▸ HahnSeries.C_ne_zero hnC
  rw [← logarithmicFaberPolynomial_eq_faberPolynomial hn, eval_logarithmicFaberPolynomial_eq hn,
    add_sub_cancel_left, hahn_C_natCast]
  field_simp

/-- The exact coefficient of (p^n q^m) in the negative logarithm of the
native denominator, obtained from the independently proved Faber–Hecke identity. -/
theorem coeff_coeff_neg_logOf_denominator {n : ℕ} (hn : 0 < n) (m : ℕ) :
    coeff m (coeff n (-logOf denominator)) =
      ∑ a ∈ (n.gcd m).divisors, c ((n / a) * (m / a)) / (a : ℂ) := by
  have h := eval_logarithmicFaberPolynomial_eq hn
  rw [logarithmicFaberPolynomial_eq_faberPolynomial hn,
    faberPolynomial_eval₂_characterLaurent_eq_hecke hn, add_right_inj] at h
  have hm := congrArg (fun F : LaurentSeries ℂ => F.coeff (m : ℤ)) h
  rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul,
    HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, coeff_mk] at hm
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  apply mul_left_cancel₀ hnC
  rw [← hm, heckeCoeff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hd : a ∣ n := (Nat.dvd_of_mem_divisors ha).trans (Nat.gcd_dvd_left n m)
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ne_zero_of_dvd_ne_zero hn.ne' hd
  have hmul : ((n / a : ℕ) : ℂ) * (a : ℂ) = (n : ℂ) := by
    exact_mod_cast Nat.div_mul_cancel hd
  rw [← hmul]
  field_simp

end D5.S3.VertexAlgebra.ActualLeechOrbifoldFaberLogarithm
