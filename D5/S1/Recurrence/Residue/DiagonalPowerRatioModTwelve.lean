/- GID: D5/S1/Recurrence/Residue/DiagonalPowerRatioModTwelve
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/DiagonalPowerRatioModTwelve
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Ternary extraction and binary square-zero lifting prove both A397241 congruences. -/

import D5.S1.Recurrence.Residue.DiagonalPowerRatioAllOdd
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
The coefficient sequence and its normalized generating series are owned by
`DiagonalPowerRatioAllOdd`; its `generating_equation` and `generating_unique`
remain the defining equation and uniqueness theorem over the integers.

Write G = mk 1, D = 1-X, and B = (1-2X^3)G. The same candidate works modulo
three and four. The diagonal residual has next-coefficient multiplier
n^2-(n-1)(n+1)=1, so uniqueness can be applied directly in either residue ring.
The frozen comparison lemmas are private; only their leading-coefficient
argument is repeated here to obtain the needed modular comparison.

Modulo three, B^3 = B(X^3). Extracting the three residue classes reduces the
residual to H(n) = [X^n](1+X)G B^n. Its recurrence is H(3n)=H(n), with the
other two residue classes zero. Strong induction gives H(n)=0 for n>0.

Modulo four, E=2(XG+X^6) has E^2=2E=0 and B^2=B(X^2)(1+E). Thus a pair of
polynomial numerators P,Q represents [X^n](P+nQ)G^2 B^n. Clearing to G^4,
which equals G(X^2)^2, gives five states closed under even/odd extraction.
The symbolic transition identities hold for every n. The zero state and a
terminal state start a strong induction; the initial residual is zero for
n>1. These are unbounded coefficient identities, not numerical regressions.

The two series identities identify the frozen coefficients with -1 above
degree two. Their remainders combine to 11 modulo 12; both literature
conjectures are then projections of that common theorem.
-/

set_option maxHeartbeats 1200000

open PowerSeries
namespace D5.S1.Recurrence.Residue.DiagonalPowerRatioModTwelve
open D5.S1.Recurrence.Residue.DiagonalPowerRatioAllOdd

private noncomputable def geom {R : Type*} [CommRing R] : PowerSeries R := mk 1
private noncomputable def den {R : Type*} [CommRing R] : PowerSeries R := 1 - X
private noncomputable def candidate {R : Type*} [CommRing R] : PowerSeries R :=
  (1 - 2 * X ^ 3) * geom
private theorem geom_den {R : Type*} [CommRing R] :
    (geom : PowerSeries R) * den = 1 := mk_one_mul_one_sub_eq_one R

private theorem leading_mul {R : Type*} [CommRing R] {n : ℕ} {U : PowerSeries R}
    (h : X ^ n ∣ U) (V : PowerSeries R) :
    coeff n (U * V) = coeff n U * constantCoeff V := by
  obtain ⟨W, rfl⟩ := h
  rw [mul_assoc]
  have hc (T : PowerSeries R) : coeff n (X ^ n * T) = constantCoeff T := by
    simpa only [zero_add, coeff_zero_eq_constantCoeff] using coeff_X_pow_mul T n 0
  rw [hc, hc, map_mul]

private theorem diagonal_multiplier {R : Type*} [CommRing R] {n : ℕ}
    {A B : PowerSeries R} (hA : constantCoeff A = 1) (hB : constantCoeff B = 1)
    (h : ∀ k < n, coeff k A = coeff k B) (m : ℕ) :
    coeff n (A ^ m) - coeff n (B ^ m) =
      (m : R) * (coeff n A - coeff n B) := by
  have hd : X ^ n ∣ A - B := by
    simpa [X_pow_dvd_iff, map_sub, sub_eq_zero] using h
  induction m with
  | zero => simp
  | succ m ih =>
    have hpow := hd.trans (sub_dvd_pow_sub_pow A B m)
    have he : A ^ (m + 1) - B ^ (m + 1) =
        (A ^ m - B ^ m) * A + (A - B) * B ^ m := by ring
    rw [← map_sub, he, map_add, leading_mul hpow, leading_mul hd]
    simp only [map_sub, map_pow, hA, hB, one_pow, mul_one, ih, Nat.cast_add,
      Nat.cast_one]
    ring

private theorem modular_unique (m : ℕ) [NeZero m] (B : PowerSeries (ZMod m))
    (h0 : coeff 0 B = 1) (h1 : coeff 1 B = 1)
    (he : ∀ n : ℕ, 1 < n → (n : ZMod m) * coeff n (B ^ n) =
      ((n : ZMod m) - 1) * coeff n (B ^ (n + 1))) :
    generatingSeries.map (Int.castRingHom (ZMod m)) = B := by
  let A := generatingSeries.map (Int.castRingHom (ZMod m))
  have hA0 : coeff 0 A = 1 := by simp [A, coeff_map, generating_equation.1]
  have hA1 : coeff 1 A = 1 := by simp [A, coeff_map, generating_equation.2.1]
  have hAe (n : ℕ) (hn : 1 < n) : (n : ZMod m) * coeff n (A ^ n) =
      ((n : ZMod m) - 1) * coeff n (A ^ (n + 1)) := by
    have h := congrArg (Int.castRingHom (ZMod m)) (generating_equation.2.2 n hn)
    simpa [A, ← map_pow, coeff_map] using h
  change A = B
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n; exact hA0.trans h0.symm
    by_cases hn1 : n = 1
    · subst n; exact hA1.trans h1.symm
    have hp := diagonal_multiplier
      (by simpa only [coeff_zero_eq_constantCoeff] using hA0)
      (by simpa only [coeff_zero_eq_constantCoeff] using h0) ih n
    have hq := diagonal_multiplier
      (by simpa only [coeff_zero_eq_constantCoeff] using hA0)
      (by simpa only [coeff_zero_eq_constantCoeff] using h0) ih (n+1)
    have ha := hAe n (by omega)
    have hb := he n (by omega)
    push_cast at hq
    linear_combination -(n : ZMod m) * hp + ((n : ZMod m) - 1) * hq + ha - hb

private theorem coeff_candidate {R : Type*} [CommRing R] (n : ℕ) :
    coeff n (candidate : PowerSeries R) = if n < 3 then 1 else -1 := by
  rw [candidate, sub_mul, one_mul]
  have ht : (2 : PowerSeries R) * X ^ 3 * geom = C (2 : R) * (X ^ 3 * geom) := by rw [map_ofNat]; ring
  rw [ht, map_sub, coeff_C_mul, coeff_X_pow_mul']
  simp only [geom, coeff_mk, Pi.one_apply]
  split_ifs <;> first | omega | ring

private theorem coeff_expand_shift {R : Type*} [CommRing R] (p : ℕ) (hp : p ≠ 0)
    (f : PowerSeries R) (n i r : ℕ) (hi : i < p) (hr : r < p) :
    coeff (p*n+r) (X^i * expand p hp f) = if i = r then coeff n f else 0 := by
  by_cases hir : i = r
  · subst i
    rw [coeff_X_pow_mul', if_pos (by omega), if_pos rfl,
      show p*n+r-r = p*n by omega, coeff_expand_mul]
  · rw [if_neg hir, coeff_X_pow_mul']
    split_ifs with h
    · apply coeff_expand_of_not_dvd
      intro hd
      obtain ⟨k, hk⟩ := hd
      have hh : p*n+r = i+p*k := by omega
      have hm := congrArg (fun t => t % p) hh
      simp only [Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_eq_of_lt hr,
        Nat.mod_eq_of_lt hi, add_zero] at hm
      exact hir hm.symm
    · rfl

private theorem three_zero : (3 : PowerSeries (ZMod 3)) = 0 := by
  have h := congrArg (C : ZMod 3 →+* PowerSeries (ZMod 3)) (show (3 : ZMod 3) = 0 by decide)
  simpa only [map_ofNat, map_zero] using h

private theorem four_zero : (4 : PowerSeries (ZMod 4)) = 0 := by
  have h := congrArg (C : ZMod 4 →+* PowerSeries (ZMod 4)) (show (4 : ZMod 4) = 0 by decide)
  simpa only [map_ofNat, map_zero] using h

private theorem char_three_poly :
    (1 - X : PowerSeries (ZMod 3)) ^ 3 = 1 - X ^ 3 := by
  linear_combination (X^2-X) * three_zero

private theorem char_four_poly :
    (1 - X : PowerSeries (ZMod 4)) ^ 4 = (1 - X ^ 2) ^ 2 := by
  linear_combination (2*X^2-X-X^3) * four_zero

private theorem geom_expand_three :
    (geom : PowerSeries (ZMod 3)) ^ 3 = expand 3 (by decide) geom := by
  have hd : (den : PowerSeries (ZMod 3)) ^ 3 = expand 3 (by decide) den := by
    simpa [den] using char_three_poly
  have h1 : (geom : PowerSeries (ZMod 3)) ^ 3 * den ^ 3 = 1 := by
    rw [← mul_pow, geom_den, one_pow]
  have h2 : expand 3 (by decide) (geom : PowerSeries (ZMod 3)) * den ^ 3 = 1 := by
    rw [hd, ← map_mul, geom_den, map_one]
  have hu : IsUnit ((den : PowerSeries (ZMod 3)) ^ 3) := by
    apply IsUnit.pow
    rw [isUnit_iff_constantCoeff]
    simp [den]
  exact hu.mul_right_cancel (h1.trans h2.symm)

private theorem candidate_cube :
    (candidate : PowerSeries (ZMod 3)) ^ 3 = expand 3 (by decide) candidate := by
  rw [candidate, mul_pow, geom_expand_three, map_mul]
  congr 1
  simp only [map_sub, map_one, map_mul, map_ofNat, map_pow, expand_X]
  linear_combination (-2*X^3+4*X^6-2*X^9) * three_zero

private theorem geom_raise {R : Type*} [CommRing R] (d e : ℕ) (h : d ≤ e) :
    (geom : PowerSeries R)^d = den^(e-d)*geom^e := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, pow_add]
  calc
    geom ^ d = geom ^ d * (geom * den) ^ k := by rw [geom_den, one_pow, mul_one]
    _ = den ^ k * (geom ^ d * geom ^ k) := by ring

private theorem coeff_split_three {R : Type*} [CommRing R]
    (f₀ f₁ f₂ g : PowerSeries R) (n r : ℕ) (hr : r < 3) :
    coeff (3*n+r) ((expand 3 (by decide) f₀ + X*expand 3 (by decide) f₁ +
      X^2*expand 3 (by decide) f₂) * expand 3 (by decide) g) =
      if r = 0 then coeff n (f₀*g) else if r = 1 then coeff n (f₁*g)
      else coeff n (f₂*g) := by
  have he : (expand 3 (by decide) f₀ + X*expand 3 (by decide) f₁ +
      X^2*expand 3 (by decide) f₂) * expand 3 (by decide) g =
      X^0*expand 3 (by decide) (f₀*g) + X^1*expand 3 (by decide) (f₁*g) +
      X^2*expand 3 (by decide) (f₂*g) := by simp only [map_mul]; ring
  rw [he, map_add, map_add]
  rw [coeff_expand_shift _ _ _ _ _ _ (by decide) hr,
    coeff_expand_shift _ _ _ _ _ _ (by decide) hr,
    coeff_expand_shift _ _ _ _ _ _ (by decide) hr]
  interval_cases r <;> simp

private theorem candidate_three : (candidate : PowerSeries (ZMod 3)) = (1+X^3)*geom := by
  unfold candidate
  linear_combination (-X^3*geom) * three_zero

private theorem ternary_reduction (P : PowerSeries (ZMod 3)) (n r : ℕ) (hr : r < 3) :
    P*geom*candidate^(3*n+r) =
      (P*(1+X^3)^r*den^(2-r))*expand 3 (by decide) (geom*candidate^n) := by
  rw [pow_add, pow_mul, candidate_cube, ← map_pow, map_mul, ← geom_expand_three]
  rw [show (candidate : PowerSeries (ZMod 3))^r = (1+X^3)^r*geom^r by
    rw [candidate_three, mul_pow]]
  have hg := geom_raise (R := ZMod 3) (r+1) 3 (by omega)
  rw [show 3-(r+1) = 2-r by omega] at hg
  calc
    P * geom * (expand 3 (by decide) (candidate ^ n) *
        ((1 + X ^ 3) ^ r * geom ^ r)) =
        (P*(1+X^3)^r)*geom^(r+1)*expand 3 (by decide) (candidate^n) := by ring
    _ = _ := by rw [hg]; ring

private noncomputable def ternaryDiagonal (n : ℕ) : ZMod 3 :=
  coeff n ((1+X)*geom*candidate^n)

private theorem ternary_step (n r : ℕ) (hr : r < 3) :
    ternaryDiagonal (3*n+r) = if r=0 then ternaryDiagonal n else 0 := by
  unfold ternaryDiagonal
  rw [ternary_reduction _ _ _ hr]
  interval_cases r
  · have he : ((1+X)*(1+X^3)^0*den^(2-0) : PowerSeries (ZMod 3)) =
        expand 3 (by decide) (1+X) + X*expand 3 (by decide) (-1) +
          X^2*expand 3 (by decide) (-1) := by
      simp only [den, map_add, map_one, expand_X, map_neg]
      ring
    rw [he, coeff_split_three _ _ _ _ _ _ (by decide)]
    simp [mul_assoc]
  · have he : ((1+X)*(1+X^3)^1*den^(2-1) : PowerSeries (ZMod 3)) =
        expand 3 (by decide) (1+X) + X*expand 3 (by decide) 0 +
          X^2*expand 3 (by decide) (-(1+X)) := by
      simp only [den, map_add, map_one, expand_X, map_neg, map_zero]
      ring
    rw [he, coeff_split_three _ _ _ _ _ _ (by decide)]
    simp
  · have he : ((1+X)*(1+X^3)^2*den^(2-2) : PowerSeries (ZMod 3)) =
        expand 3 (by decide) ((1+X)^2) + X*expand 3 (by decide) ((1+X)^2) +
          X^2*expand 3 (by decide) 0 := by
      simp only [den, map_add, map_one, expand_X, map_pow, map_zero]
      ring
    rw [he, coeff_split_three _ _ _ _ _ _ (by decide)]
    simp

private theorem ternary_vanish (n : ℕ) (hn : 0 < n) : ternaryDiagonal n = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have he : n = 3*(n/3)+n%3 := by omega
    rw [he, ternary_step _ _ (Nat.mod_lt _ (by decide))]
    split_ifs with h
    · exact ih (n/3) (by omega) (by omega)
    · rfl

private noncomputable def residual {R : Type*} [CommRing R] (B : PowerSeries R)
    (n : ℕ) : R := (n:R)*coeff n (B^n)-((n:R)-1)*coeff n (B^(n+1))

private theorem residual_coeff {R : Type*} [CommRing R] (B : PowerSeries R) (n : ℕ) :
    residual B n = coeff n ((B+C (n:R)*(1-B))*B^n) := by
  have he : (B+C (n:R)*(1-B))*B^n =
      C (n:R)*B^n-C ((n:R)-1)*B^(n+1) := by
    rw [map_sub, map_one]
    ring
  rw [he, map_sub, coeff_C_mul, coeff_C_mul]
  rfl

private theorem ternary_residual_step (n r : ℕ) (hr : r < 3) :
    residual (candidate : PowerSeries (ZMod 3)) (3*n+r) =
      if r=2 then 0 else ternaryDiagonal n := by
  rw [residual_coeff]
  have hc : ((3*n+r:ℕ):ZMod 3) = (r:ZMod 3) := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      show (3:ZMod 3)=0 by decide, zero_mul, zero_add]
  rw [hc]
  have he : (candidate+C (r:ZMod 3)*(1-candidate) : PowerSeries (ZMod 3)) =
      (1-C (r:ZMod 3)*X+(1-C (r:ZMod 3))*X^3)*geom := by
    rw [candidate_three]
    have hg := geom_den (R := ZMod 3)
    unfold den at hg
    linear_combination -C (r:ZMod 3) * hg
  rw [he, ternary_reduction _ _ _ hr]
  interval_cases r
  · have hp : ((1-C (0:ZMod 3)*X+(1-C (0:ZMod 3))*X^3)*(1+X^3)^0*
        den^(2-0) : PowerSeries (ZMod 3)) =
        expand 3 (by decide) (1+X) + X*expand 3 (by decide) (1+X) +
          X^2*expand 3 (by decide) (1+X) := by
      simp only [map_zero, den, map_add, map_one, expand_X]
      linear_combination (-X-X^4) * three_zero
    norm_num only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
    rw [hp, coeff_split_three _ _ _ _ _ _ (by decide)]
    simp [ternaryDiagonal, mul_assoc]
  · have hp : ((1-C (1:ZMod 3)*X+(1-C (1:ZMod 3))*X^3)*(1+X^3)^1*
        den^(2-1) : PowerSeries (ZMod 3)) =
        expand 3 (by decide) (1+X) + X*expand 3 (by decide) (1+X) +
          X^2*expand 3 (by decide) (1+X) := by
      simp only [map_one, den, map_add, expand_X]
      linear_combination (-X-X^4) * three_zero
    norm_num only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
    rw [hp, coeff_split_three _ _ _ _ _ _ (by decide)]
    simp [ternaryDiagonal, mul_assoc]
  · have hp : ((1-C (2:ZMod 3)*X+(1-C (2:ZMod 3))*X^3)*(1+X^3)^2*
        den^(2-2) : PowerSeries (ZMod 3)) =
        expand 3 (by decide) ((1-X)*(1+X)^2) +
          X*expand 3 (by decide) ((1+X)^2) + X^2*expand 3 (by decide) 0 := by
      simp only [map_ofNat, map_one, map_zero, den, map_add, map_sub, map_mul,
        map_pow, expand_X]
      linear_combination (-X-2*X^4-X^7) * three_zero
    norm_num only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
    rw [hp, coeff_split_three _ _ _ _ _ _ (by decide)]
    simp

private theorem ternary_residual_zero (n : ℕ) (hn : 1 < n) :
    residual (candidate : PowerSeries (ZMod 3)) n = 0 := by
  have he : n = 3*(n/3)+n%3 := by omega
  rw [he, ternary_residual_step _ _ (Nat.mod_lt _ (by decide))]
  split_ifs with h
  · rfl
  · exact ternary_vanish _ (by omega)

private theorem geom_expand_four :
    (geom : PowerSeries (ZMod 4)) ^ 4 = expand 2 (by decide) (geom^2) := by
  have hd : (den : PowerSeries (ZMod 4)) ^ 4 = expand 2 (by decide) (den^2) := by
    simpa [den] using char_four_poly
  have h1 : (geom : PowerSeries (ZMod 4)) ^ 4 * den ^ 4 = 1 := by
    rw [← mul_pow, geom_den, one_pow]
  have h2 : expand 2 (by decide) ((geom : PowerSeries (ZMod 4))^2) * den ^ 4 = 1 := by
    rw [hd, ← map_mul, ← mul_pow, geom_den, one_pow, map_one]
  have hu : IsUnit ((den : PowerSeries (ZMod 4)) ^ 4) := by
    apply IsUnit.pow
    rw [isUnit_iff_constantCoeff]
    simp [den]
  exact hu.mul_right_cancel (h1.trans h2.symm)

private noncomputable def correction : PowerSeries (ZMod 4) := 2*(X*geom+X^6)
private noncomputable def correctionNumerator : PowerSeries (ZMod 4) :=
  2*X+2*X^6-2*X^7
private noncomputable def numerator : PowerSeries (ZMod 4) := 1-2*X^3

private theorem correction_numerator : correction = correctionNumerator*geom := by
  have hg := geom_den (R := ZMod 4)
  unfold correction correctionNumerator den at *
  linear_combination (-2*X^6)*hg

private theorem correction_square : correction^2 = 0 := by
  unfold correction
  linear_combination (X*geom+X^6)^2 * four_zero

private theorem correction_two : 2*correction = 0 := by
  unfold correction
  linear_combination (X*geom+X^6) * four_zero

private theorem candidate_square :
    (candidate : PowerSeries (ZMod 4))^2 = expand 2 (by decide) candidate*(1+correction) := by
  have hg := geom_den (R := ZMod 4)
  have he := congrArg (expand 2 (by decide)) hg
  simp only [map_mul, map_one, den, map_sub, expand_X] at he
  have hs : (geom : PowerSeries (ZMod 4))^2*(1-X^2) = 1+2*X*geom := by
    unfold den at hg
    linear_combination (geom*(1+X)+1)*hg
  have ht : (geom : PowerSeries (ZMod 4))^2 = expand 2 (by decide) geom*(1+2*X*geom) := by
    linear_combination expand 2 (by decide) geom * hs - geom^2 * he
  unfold candidate correction
  simp only [map_mul, map_sub, map_one, map_ofNat, map_pow, expand_X]
  linear_combination ht +
    (-X^3*geom^2+X^6*geom^2+X^7*geom*expand 2 (by decide) geom+
      X^12*expand 2 (by decide) geom) * four_zero

private theorem correction_power (n : ℕ) :
    (1+correction)^n = 1+(n:PowerSeries (ZMod 4))*correction := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination (n:PowerSeries (ZMod 4)) * correction_square

private theorem binary_reduction (P Q : PowerSeries (ZMod 4)) (n r : ℕ) (hr : r < 2) :
    (P+((2*n+r:ℕ):PowerSeries (ZMod 4))*Q)*geom^2*candidate^(2*n+r) =
      ((P+(r:PowerSeries (ZMod 4))*Q)*numerator^r*den^(2-r) +
        (n:PowerSeries (ZMod 4))*(2*Q*numerator^r*den^(2-r)+
          (P+(r:PowerSeries (ZMod 4))*Q)*correctionNumerator*numerator^r*den^(1-r))) *
        expand 2 (by decide) (geom^2*candidate^n) := by
  have hpow : (candidate : PowerSeries (ZMod 4))^(2*n+r) =
      expand 2 (by decide) (candidate^n)*(1+(n:PowerSeries (ZMod 4))*correction)*
        (numerator^r*geom^r) := by
    rw [pow_add, pow_mul, candidate_square, mul_pow, correction_power, ← map_pow]
    congr 1
    exact mul_pow numerator geom r
  rw [hpow]
  have ha : (P+((2*n+r:ℕ):PowerSeries (ZMod 4))*Q)*(1+(n:PowerSeries (ZMod 4))*correction) =
      (P+(r:PowerSeries (ZMod 4))*Q)+(n:PowerSeries (ZMod 4))*
        (2*Q+(P+(r:PowerSeries (ZMod 4))*Q)*correction) := by
    push_cast
    linear_combination (n:PowerSeries (ZMod 4))^2*Q*correction_two
  have hg2 := geom_raise (R := ZMod 4) (r+2) 4 (by omega)
  have hg3 := geom_raise (R := ZMod 4) (r+3) 4 (by omega)
  rw [show 4-(r+2)=2-r by omega] at hg2
  rw [show 4-(r+3)=1-r by omega] at hg3
  calc
    _ = ((P+((2*n+r:ℕ):PowerSeries (ZMod 4))*Q)*
        (1+(n:PowerSeries (ZMod 4))*correction))*numerator^r*geom^(r+2)*
        expand 2 (by decide) (candidate^n) := by ring
    _ = ((P+(r:PowerSeries (ZMod 4))*Q)*numerator^r*geom^(r+2)+
        (n:PowerSeries (ZMod 4))*(2*Q*numerator^r*geom^(r+2)+
          (P+(r:PowerSeries (ZMod 4))*Q)*correctionNumerator*numerator^r*geom^(r+3)))*
        expand 2 (by decide) (candidate^n) := by
      rw [ha, correction_numerator]
      ring
    _ = _ := by
      rw [hg2, hg3, map_mul, ← geom_expand_four]
      ring

private theorem coeff_split_two {R : Type*} [CommRing R]
    (f₀ f₁ g : PowerSeries R) (n r : ℕ) (hr : r < 2) :
    coeff (2*n+r) ((expand 2 (by decide) f₀ + X*expand 2 (by decide) f₁)*
      expand 2 (by decide) g) = if r=0 then coeff n (f₀*g) else coeff n (f₁*g) := by
  have he : (expand 2 (by decide) f₀+X*expand 2 (by decide) f₁)*expand 2 (by decide) g =
      X^0*expand 2 (by decide) (f₀*g)+X^1*expand 2 (by decide) (f₁*g) := by
    simp only [map_mul]
    ring
  rw [he, map_add, coeff_expand_shift _ _ _ _ _ _ (by decide) hr,
    coeff_expand_shift _ _ _ _ _ _ (by decide) hr]
  interval_cases r <;> simp


-- Numerator pairs for the binary coefficient-extraction invariant.
private noncomputable def stateP : ℕ → PowerSeries (ZMod 4)
  | 0 => 1+3*X+2*X^3+2*X^4
  | 1 => 1+3*X+2*X^2+2*X^3
  | 2 => 1+X+2*X^2
  | 3 => 2*X
  | _ => 0

private noncomputable def stateQ : ℕ → PowerSeries (ZMod 4)
  | 0 => 3*X+X^2+2*X^3+2*X^4
  | 1 => 2*X+2*X^2+2*X^3+2*X^4
  | 2 => 2*X^3+2*X^4
  | 3 => 2
  | _ => 0

private def nextState : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ => 2
  | 1, 0 => 2
  | 1, _ => 3
  | 2, 0 => 2
  | 2, _ => 3
  | _, _ => 4

private noncomputable def binaryDiagonal (i n : ℕ) : ZMod 4 :=
  coeff n ((stateP i+(n:PowerSeries (ZMod 4))*stateQ i)*geom^2*candidate^n)

-- Each branch is a polynomial identity for arbitrary n, followed by coefficient extraction.
private theorem binary_step (i n r : ℕ) (hi : i < 5) (hr : r < 2) :
    binaryDiagonal i (2*n+r) = binaryDiagonal (nextState i r) n := by
  unfold binaryDiagonal
  rw [binary_reduction _ _ _ _ hr]
  interval_cases i <;> interval_cases r
  · have he :
        (stateP 0+(0:PowerSeries (ZMod 4))*stateQ 0)*numerator^0*den^(2-0)+
        (n:PowerSeries (ZMod 4))*(2*stateQ 0*numerator^0*den^(2-0)+
          (stateP 0+(0:PowerSeries (ZMod 4))*stateQ 0)*correctionNumerator*numerator^0*den^(1-0)) =
        expand 2 (by decide) ((1+3*X+2*X^2+2*X^3)+(n:PowerSeries (ZMod 4))*(2*X+2*X^2+2*X^3+2*X^4))+
          X*expand 2 (by decide) ((1+X+2*X^2)+(n:PowerSeries (ZMod 4))*(2*X^3+2*X^4)) := by
      simp only [stateP, stateQ, numerator, den, correctionNumerator,
        map_add, map_mul, map_pow, map_natCast, map_ofNat, map_one,
        expand_X, Nat.reduceSub]
      linear_combination (2*X*(n:PowerSeries (ZMod 4))-2*X^2-2*X^2*(n:PowerSeries (ZMod 4))+X^3-X^4-X^5-X^5*(n:PowerSeries (ZMod 4))-3*X^8*(n:PowerSeries (ZMod 4))+2*X^9*(n:PowerSeries (ZMod 4))-X^10*(n:PowerSeries (ZMod 4))-X^11*(n:PowerSeries (ZMod 4))+X^12*(n:PowerSeries (ZMod 4))) * four_zero
    norm_num only [Nat.cast_zero, Nat.cast_one]
    rw [he, coeff_split_two _ _ _ _ _ (by decide)]
    simp [nextState, stateP, stateQ, mul_assoc]
  · have he :
        (stateP 0+(1:PowerSeries (ZMod 4))*stateQ 0)*numerator^1*den^(2-1)+
        (n:PowerSeries (ZMod 4))*(2*stateQ 0*numerator^1*den^(2-1)+
          (stateP 0+(1:PowerSeries (ZMod 4))*stateQ 0)*correctionNumerator*numerator^1*den^(1-1)) =
        expand 2 (by decide) ((1+3*X+2*X^2+2*X^3)+(n:PowerSeries (ZMod 4))*(2*X^3+2*X^4))+
          X*expand 2 (by decide) ((1+X+2*X^2)+(n:PowerSeries (ZMod 4))*(2*X^3+2*X^4)) := by
      simp only [stateP, stateQ, numerator, den, correctionNumerator,
        map_add, map_mul, map_pow, map_natCast, map_ofNat, map_one,
        expand_X, Nat.reduceSub]
      linear_combination (X+2*X*(n:PowerSeries (ZMod 4))-2*X^2+2*X^2*(n:PowerSeries (ZMod 4))+X^3*(n:PowerSeries (ZMod 4))-3*X^4-2*X^4*(n:PowerSeries (ZMod 4))+X^5-3*X^5*(n:PowerSeries (ZMod 4))-2*X^6-2*X^6*(n:PowerSeries (ZMod 4))-2*X^7*(n:PowerSeries (ZMod 4))+2*X^8-5*X^8*(n:PowerSeries (ZMod 4))-5*X^10*(n:PowerSeries (ZMod 4))+3*X^11*(n:PowerSeries (ZMod 4))-3*X^12*(n:PowerSeries (ZMod 4))+4*X^14*(n:PowerSeries (ZMod 4))) * four_zero
    norm_num only [Nat.cast_zero, Nat.cast_one]
    rw [he, coeff_split_two _ _ _ _ _ (by decide)]
    simp [nextState, stateP, stateQ, mul_assoc]
  · have he :
        (stateP 1+(0:PowerSeries (ZMod 4))*stateQ 1)*numerator^0*den^(2-0)+
        (n:PowerSeries (ZMod 4))*(2*stateQ 1*numerator^0*den^(2-0)+
          (stateP 1+(0:PowerSeries (ZMod 4))*stateQ 1)*correctionNumerator*numerator^0*den^(1-0)) =
        expand 2 (by decide) ((1+X+2*X^2)+(n:PowerSeries (ZMod 4))*(2*X^3+2*X^4))+
          X*expand 2 (by decide) ((1+X+2*X^2)+(n:PowerSeries (ZMod 4))*(2+2*X+2*X^3+2*X^4)) := by
      simp only [stateP, stateQ, numerator, den, correctionNumerator,
        map_add, map_mul, map_pow, map_natCast, map_ofNat, map_one,
        expand_X, Nat.reduceSub]
      linear_combination (X*(n:PowerSeries (ZMod 4))-X^2-X^3*(n:PowerSeries (ZMod 4))-X^4-2*X^5*(n:PowerSeries (ZMod 4))+X^6*(n:PowerSeries (ZMod 4))-2*X^8*(n:PowerSeries (ZMod 4))-X^10*(n:PowerSeries (ZMod 4))+X^11*(n:PowerSeries (ZMod 4))) * four_zero
    norm_num only [Nat.cast_zero, Nat.cast_one]
    rw [he, coeff_split_two _ _ _ _ _ (by decide)]
    simp [nextState, stateP, stateQ, mul_assoc]
  · have he :
        (stateP 1+(1:PowerSeries (ZMod 4))*stateQ 1)*numerator^1*den^(2-1)+
        (n:PowerSeries (ZMod 4))*(2*stateQ 1*numerator^1*den^(2-1)+
          (stateP 1+(1:PowerSeries (ZMod 4))*stateQ 1)*correctionNumerator*numerator^1*den^(1-1)) =
        expand 2 (by decide) ((1+3*X+2*X^2)+(n:PowerSeries (ZMod 4))*(2*X+2*X^3+2*X^4))+
          X*expand 2 (by decide) ((2*X)+(n:PowerSeries (ZMod 4))*(2)) := by
      simp only [stateP, stateQ, numerator, den, correctionNumerator,
        map_add, map_mul, map_pow, map_natCast, map_ofNat, map_one,
        expand_X, Nat.reduceSub]
      linear_combination (X+X*(n:PowerSeries (ZMod 4))-X^2+2*X^2*(n:PowerSeries (ZMod 4))-X^3+2*X^3*(n:PowerSeries (ZMod 4))-3*X^4-X^4*(n:PowerSeries (ZMod 4))-5*X^5*(n:PowerSeries (ZMod 4))-4*X^6*(n:PowerSeries (ZMod 4))+X^7-2*X^7*(n:PowerSeries (ZMod 4))+X^8-X^8*(n:PowerSeries (ZMod 4))-X^9*(n:PowerSeries (ZMod 4))-5*X^10*(n:PowerSeries (ZMod 4))+2*X^13*(n:PowerSeries (ZMod 4))+2*X^14*(n:PowerSeries (ZMod 4))) * four_zero
    norm_num only [Nat.cast_zero, Nat.cast_one]
    rw [he, coeff_split_two _ _ _ _ _ (by decide)]
    simp [nextState, stateP, stateQ, mul_assoc]
  · have he :
        (stateP 2+(0:PowerSeries (ZMod 4))*stateQ 2)*numerator^0*den^(2-0)+
        (n:PowerSeries (ZMod 4))*(2*stateQ 2*numerator^0*den^(2-0)+
          (stateP 2+(0:PowerSeries (ZMod 4))*stateQ 2)*correctionNumerator*numerator^0*den^(1-0)) =
        expand 2 (by decide) ((1+X+2*X^2)+(n:PowerSeries (ZMod 4))*(2*X^3+2*X^4))+
          X*expand 2 (by decide) ((3+X)+(n:PowerSeries (ZMod 4))*(2+2*X+2*X^3+2*X^4)) := by
      simp only [stateP, stateQ, numerator, den, correctionNumerator,
        map_add, map_mul, map_pow, map_natCast, map_ofNat, map_one,
        expand_X, Nat.reduceSub]
      linear_combination (-X-X^3+X^3*(n:PowerSeries (ZMod 4))-2*X^4*(n:PowerSeries (ZMod 4))-X^5*(n:PowerSeries (ZMod 4))+X^6*(n:PowerSeries (ZMod 4))-X^7*(n:PowerSeries (ZMod 4))-2*X^9*(n:PowerSeries (ZMod 4))+X^10*(n:PowerSeries (ZMod 4))) * four_zero
    norm_num only [Nat.cast_zero, Nat.cast_one]
    rw [he, coeff_split_two _ _ _ _ _ (by decide)]
    simp [nextState, stateP, stateQ, mul_assoc]
  · have he :
        (stateP 2+(1:PowerSeries (ZMod 4))*stateQ 2)*numerator^1*den^(2-1)+
        (n:PowerSeries (ZMod 4))*(2*stateQ 2*numerator^1*den^(2-1)+
          (stateP 2+(1:PowerSeries (ZMod 4))*stateQ 2)*correctionNumerator*numerator^1*den^(1-1)) =
        expand 2 (by decide) ((1+X)+(n:PowerSeries (ZMod 4))*(2*X+2*X^3+2*X^4))+
          X*expand 2 (by decide) ((2*X)+(n:PowerSeries (ZMod 4))*(2)) := by
      simp only [stateP, stateQ, numerator, den, correctionNumerator,
        map_add, map_mul, map_pow, map_natCast, map_ofNat, map_one,
        expand_X, Nat.reduceSub]
      linear_combination (-X^3+2*X^3*(n:PowerSeries (ZMod 4))-X^5-X^5*(n:PowerSeries (ZMod 4))-4*X^6*(n:PowerSeries (ZMod 4))-2*X^7*(n:PowerSeries (ZMod 4))+X^8-X^9*(n:PowerSeries (ZMod 4))-2*X^11*(n:PowerSeries (ZMod 4))+2*X^14*(n:PowerSeries (ZMod 4))) * four_zero
    norm_num only [Nat.cast_zero, Nat.cast_one]
    rw [he, coeff_split_two _ _ _ _ _ (by decide)]
    simp [nextState, stateP, stateQ, mul_assoc]
  · have he :
        (stateP 3+(0:PowerSeries (ZMod 4))*stateQ 3)*numerator^0*den^(2-0)+
        (n:PowerSeries (ZMod 4))*(2*stateQ 3*numerator^0*den^(2-0)+
          (stateP 3+(0:PowerSeries (ZMod 4))*stateQ 3)*correctionNumerator*numerator^0*den^(1-0)) =
        expand 2 (by decide) ((0)+(n:PowerSeries (ZMod 4))*(0))+
          X*expand 2 (by decide) ((2+2*X)+(n:PowerSeries (ZMod 4))*(0)) := by
      simp only [stateP, stateQ, numerator, den, correctionNumerator,
        map_add, map_mul, map_natCast, map_ofNat, map_zero,
        expand_X, Nat.reduceSub]
      linear_combination ((n:PowerSeries (ZMod 4))-2*X*(n:PowerSeries (ZMod 4))-X^2+2*X^2*(n:PowerSeries (ZMod 4))-X^3*(n:PowerSeries (ZMod 4))+X^7*(n:PowerSeries (ZMod 4))-2*X^8*(n:PowerSeries (ZMod 4))+X^9*(n:PowerSeries (ZMod 4))) * four_zero
    norm_num only [Nat.cast_zero, Nat.cast_one]
    rw [he, coeff_split_two _ _ _ _ _ (by decide)]
    simp [nextState, stateP, stateQ]
  · have he :
        (stateP 3+(1:PowerSeries (ZMod 4))*stateQ 3)*numerator^1*den^(2-1)+
        (n:PowerSeries (ZMod 4))*(2*stateQ 3*numerator^1*den^(2-1)+
          (stateP 3+(1:PowerSeries (ZMod 4))*stateQ 3)*correctionNumerator*numerator^1*den^(1-1)) =
        expand 2 (by decide) ((2+2*X)+(n:PowerSeries (ZMod 4))*(0))+
          X*expand 2 (by decide) ((0)+(n:PowerSeries (ZMod 4))*(0)) := by
      simp only [stateP, stateQ, numerator, den, correctionNumerator,
        map_add, map_mul, map_natCast, map_ofNat, map_zero,
        expand_X, Nat.reduceSub]
      linear_combination ((n:PowerSeries (ZMod 4))-X^2+X^2*(n:PowerSeries (ZMod 4))-X^3-2*X^3*(n:PowerSeries (ZMod 4))+X^5-2*X^5*(n:PowerSeries (ZMod 4))+X^6*(n:PowerSeries (ZMod 4))-X^8*(n:PowerSeries (ZMod 4))-2*X^9*(n:PowerSeries (ZMod 4))+2*X^11*(n:PowerSeries (ZMod 4))) * four_zero
    norm_num only [Nat.cast_zero, Nat.cast_one]
    rw [he, coeff_split_two _ _ _ _ _ (by decide)]
    simp [nextState, stateP, stateQ]
  · have he :
        (stateP 4+(0:PowerSeries (ZMod 4))*stateQ 4)*numerator^0*den^(2-0)+
        (n:PowerSeries (ZMod 4))*(2*stateQ 4*numerator^0*den^(2-0)+
          (stateP 4+(0:PowerSeries (ZMod 4))*stateQ 4)*correctionNumerator*numerator^0*den^(1-0)) =
        expand 2 (by decide) ((0)+(n:PowerSeries (ZMod 4))*(0))+
          X*expand 2 (by decide) ((0)+(n:PowerSeries (ZMod 4))*(0)) := by
      simp only [stateP, stateQ, numerator, den, correctionNumerator,
        map_add, map_mul, map_natCast, map_zero,
        Nat.reduceSub]
      linear_combination (0) * four_zero
    norm_num only [Nat.cast_zero, Nat.cast_one]
    rw [he, coeff_split_two _ _ _ _ _ (by decide)]
    simp [nextState, stateP, stateQ]
  · have he :
        (stateP 4+(1:PowerSeries (ZMod 4))*stateQ 4)*numerator^1*den^(2-1)+
        (n:PowerSeries (ZMod 4))*(2*stateQ 4*numerator^1*den^(2-1)+
          (stateP 4+(1:PowerSeries (ZMod 4))*stateQ 4)*correctionNumerator*numerator^1*den^(1-1)) =
        expand 2 (by decide) ((0)+(n:PowerSeries (ZMod 4))*(0))+
          X*expand 2 (by decide) ((0)+(n:PowerSeries (ZMod 4))*(0)) := by
      simp only [stateP, stateQ, numerator, den, correctionNumerator,
        map_add, map_mul, map_natCast, map_zero,
        Nat.reduceSub]
      linear_combination (0) * four_zero
    norm_num only [Nat.cast_zero, Nat.cast_one]
    rw [he, coeff_split_two _ _ _ _ _ (by decide)]
    simp [nextState, stateP, stateQ]
private theorem binary_zero (n : ℕ) : binaryDiagonal 4 n = 0 := by
  simp [binaryDiagonal, stateP, stateQ]

private theorem binary_terminal (n : ℕ) : binaryDiagonal 3 n = 0 := by
  have he : n = 2*(n/2)+n%2 := by omega
  rw [he, binary_step _ _ _ (by decide) (Nat.mod_lt _ (by decide))]
  exact binary_zero _

private theorem binary_inner (n : ℕ) (hn : 0 < n) :
    binaryDiagonal 1 n = 0 ∧ binaryDiagonal 2 n = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have he : 2*(n/2)+n%2 = n := by omega
    have h1 := binary_step 1 (n/2) (n%2) (by decide) (Nat.mod_lt _ (by decide))
    have h2 := binary_step 2 (n/2) (n%2) (by decide) (Nat.mod_lt _ (by decide))
    rw [he] at h1 h2
    by_cases hr : n%2=0
    · rw [hr] at h1 h2
      have h := (ih (n/2) (by omega) (by omega)).2
      exact ⟨h1.trans h, h2.trans h⟩
    · have hr1 : n%2=1 := by omega
      rw [hr1] at h1 h2
      exact ⟨h1.trans (binary_terminal _), h2.trans (binary_terminal _)⟩

private theorem binary_residual (n : ℕ) :
    residual (candidate : PowerSeries (ZMod 4)) n = binaryDiagonal 0 n := by
  have hp : stateP 0 = numerator*den := by
    simp only [stateP, numerator, den]
    linear_combination (X+X^3)*four_zero
  have hq : stateQ 0 = (den-numerator)*den := by
    simp only [stateQ, numerator, den]
    linear_combination (X+X^4)*four_zero
  have hs : (stateP 0+(n:PowerSeries (ZMod 4))*stateQ 0)*geom^2 =
      candidate+(n:PowerSeries (ZMod 4))*(1-candidate) := by
    rw [hp, hq]
    calc
      _ = (numerator+(n:PowerSeries (ZMod 4))*(den-numerator))*geom := by
        have hg : (geom : PowerSeries (ZMod 4)) = den*geom^2 := by
          simpa only [pow_one, Nat.reduceSub] using geom_raise (R := ZMod 4) 1 2 (by decide)
        calc
          _ = (numerator+(n:PowerSeries (ZMod 4))*(den-numerator))*(den*geom^2) := by ring
          _ = _ := by rw [← hg]
      _ = _ := by
        have hg := geom_den (R := ZMod 4)
        unfold den numerator candidate at *
        linear_combination (n:PowerSeries (ZMod 4))*hg
  rw [residual_coeff]
  unfold binaryDiagonal
  rw [hs, map_natCast]

private theorem binary_residual_zero (n : ℕ) (hn : 1 < n) :
    residual (candidate : PowerSeries (ZMod 4)) n = 0 := by
  rw [binary_residual]
  have he : n = 2*(n/2)+n%2 := by omega
  rw [he, binary_step _ _ _ (by decide) (Nat.mod_lt _ (by decide))]
  have h := binary_inner (n/2) (by omega)
  by_cases hr : n%2=0
  · rw [hr]; exact h.1
  · have hr1 : n%2=1 := by omega
    rw [hr1]; exact h.2

/-- The reduction of the frozen generating series modulo three. -/
theorem mod_three_identity :
    generatingSeries.map (Int.castRingHom (ZMod 3)) = (1-2*X^3)*mk 1 := by
  change generatingSeries.map (Int.castRingHom (ZMod 3)) = candidate
  apply modular_unique
  · rw [coeff_candidate]; decide
  · rw [coeff_candidate]; decide
  · intro n hn
    exact sub_eq_zero.mp (ternary_residual_zero n hn)

/-- The reduction of the frozen generating series modulo four. -/
theorem mod_four_identity :
    generatingSeries.map (Int.castRingHom (ZMod 4)) = (1-2*X^3)*mk 1 := by
  change generatingSeries.map (Int.castRingHom (ZMod 4)) = candidate
  apply modular_unique
  · rw [coeff_candidate]; decide
  · rw [coeff_candidate]; decide
  · intro n hn
    exact sub_eq_zero.mp (binary_residual_zero n hn)

private theorem coefficient_mod_three (n : ℕ) (hn : 2 < n) : a n % 3 = 2 := by
  have hi : generatingSeries.map (Int.castRingHom (ZMod 3)) = candidate := mod_three_identity
  have hc := congrArg (coeff n) hi
  rw [coeff_candidate, if_neg (by omega)] at hc
  have h : (a n : ZMod 3) = (2:ℤ) := by
    simpa [coeff_map, generatingSeries, show (-1:ZMod 3)=(2:ℤ) by decide] using hc
  exact (ZMod.intCast_eq_intCast_iff' (a n) 2 3).mp h

private theorem coefficient_mod_four (n : ℕ) (hn : 2 < n) : a n % 4 = 3 := by
  have hi : generatingSeries.map (Int.castRingHom (ZMod 4)) = candidate := mod_four_identity
  have hc := congrArg (coeff n) hi
  rw [coeff_candidate, if_neg (by omega)] at hc
  have h : (a n : ZMod 4) = (3:ℤ) := by
    simpa [coeff_map, generatingSeries, show (-1:ZMod 4)=(3:ℤ) by decide] using hc
  exact (ZMod.intCast_eq_intCast_iff' (a n) 3 4).mp h

/-- The common modulus resolving both remaining conjectures in hanna2026a397241b. -/
theorem hanna_conjecture_mod_twelve (n : ℕ) (hn : 2 < n) : a n % 12 = 11 := by
  have h3 := coefficient_mod_three n hn
  have h4 := coefficient_mod_four n hn
  omega

/-- Hanna's conjecture modulo three for the existing integer coefficient sequence. -/
theorem hanna_conjecture_mod_three (n : ℕ) (hn : 2 < n) : a n % 3 = 2 := by
  have h := hanna_conjecture_mod_twelve n hn
  omega

/-- Hanna's conjecture modulo four for the existing integer coefficient sequence. -/
theorem hanna_conjecture_mod_four (n : ℕ) (hn : 2 < n) : a n % 4 = 3 := by
  have h := hanna_conjecture_mod_twelve n hn
  omega

#print axioms mod_three_identity
#print axioms mod_four_identity
#print axioms hanna_conjecture_mod_three
#print axioms hanna_conjecture_mod_four
#print axioms hanna_conjecture_mod_twelve
end D5.S1.Recurrence.Residue.DiagonalPowerRatioModTwelve
