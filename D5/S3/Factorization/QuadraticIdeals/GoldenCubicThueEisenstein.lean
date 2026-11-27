/- GID: D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueEisenstein
   generality: I
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/GoldenCubicThueEisenstein
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact polynomial Eisenstein certificates at the native Thue role prime and three. -/

import D5.S3.Factorization.QuadraticIdeals.GoldenCubicThueDescent
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# Two Eisenstein certificates for the native Thue companion

A primary Eisenstein coordinate pair of prime norm yields the same monic
integral cubic, Eisenstein at the role prime and, after translation by one,
at 3. These are polynomial certificates; no local index or field
discriminant assertion is made.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.QuadraticIdeals.GoldenCubicThueEisenstein

def generator {R : Type*} [CommRing R] (P E : R) : Cubic R :=
  ⟨1, -6*P, 9*P^2, -(E^2*P)⟩

def shifted {R : Type*} [CommRing R] (P E : R) : Cubic R :=
  ⟨1, 3-6*P, 3-12*P+9*P^2, 1-6*P+9*P^2-E^2*P⟩

theorem primary_norm_identity {R : Type*} [CommRing R] (a b : R) :
    (a^2-b^2)^2 - (a^2-b^2)*(2*a*b-b^2) + (2*a*b-b^2)^2 =
      (a^2-a*b+b^2)^2 := by ring

theorem key_norm {R : Type*} [CommRing R] {A D P : R}
    (h : A^2-A*D+D^2 = P^2) :
    4*P^2 - (A-2*D)^2 = 3*A^2 := by
  linear_combination -4*h

theorem generator_discriminant {R : Type*} [CommRing R] {A D P : R}
    (h : A^2-A*D+D^2 = P^2) :
    (generator P (A-2*D)).discr = 81*A^2*(A-2*D)^2*P^2 := by
  unfold generator Cubic.discr
  linear_combination (27*(A-2*D)^2*P^2)*key_norm h

/-- Coefficient form of Eisenstein, including the monic leading coefficient. -/
def EisensteinCoeffs (p : ℤ) (f : Cubic ℤ) : Prop :=
  f.a = 1 ∧ p ∣ f.b ∧ p ∣ f.c ∧ p ∣ f.d ∧ ¬ p^2 ∣ f.d

theorem eisenstein_at_role (P E : ℤ) (hP : P ≠ 0) (hE : ¬ P ∣ E^2) :
    EisensteinCoeffs P (generator P E) := by
  refine ⟨rfl, ⟨-6, by change -6*P = P*(-6); ring⟩,
    ⟨9*P, by change 9*P^2 = P*(9*P); ring⟩,
    ⟨-(E^2), by change -(E^2*P) = P*(-(E^2)); ring⟩, ?_⟩
  rintro ⟨k,hk⟩
  change -(E^2*P) = P^2*k at hk
  apply hE
  refine ⟨-k, mul_left_cancel₀ hP ?_⟩
  linear_combination -hk

theorem shifted_constant (A D P : ℤ) (h : A^2-A*D+D^2 = P^2)
    (hA : (3 : ℤ) ∣ A-1) (hP : (3 : ℤ) ∣ P-1) :
    (9 : ℤ) ∣ (shifted P (A-2*D)).d - 3 := by
  obtain ⟨m,hm⟩ := hA
  obtain ⟨n,hn⟩ := hP
  have hAs : A = 1+3*m := by linear_combination hm
  have hPs : P = 1+3*n := by linear_combination hn
  have huv : (A-2*D)^2*P = 4*P^3-3*A^2*P := by
    linear_combination -P * key_norm h
  change (9 : ℤ) ∣ 1-6*P+9*P^2-(A-2*D)^2*P-3
  rw [huv,hAs,hPs]
  refine ⟨-12*n^3 + 9*m^2*n + 3*m^2 + 6*m*n + 2*m - 3*n^2 + n, ?_⟩
  ring

theorem eisenstein_at_three (A D P : ℤ) (h : A^2-A*D+D^2 = P^2)
    (hA : (3 : ℤ) ∣ A-1) (hP : (3 : ℤ) ∣ P-1) :
    EisensteinCoeffs 3 (shifted P (A-2*D)) := by
  have hd := shifted_constant A D P h hA hP
  obtain ⟨k,hk⟩ := hd
  refine ⟨rfl, ⟨1-2*P, by change 3-6*P = 3*(1-2*P); ring⟩,
    ⟨1-4*P+3*P^2, by change 3-12*P+9*P^2 = 3*(1-4*P+3*P^2); ring⟩,
    ⟨1+3*k, by omega⟩, ?_⟩
  intro hh
  norm_num at hh
  omega

open Polynomial in
theorem shifted_eq_comp {R : Type*} [CommRing R] (P E : R) :
    (shifted P E).toPoly = (generator P E).toPoly.comp (X+C 1) := by
  simp only [shifted, generator, Cubic.toPoly, add_comp, mul_comp,
    pow_comp, X_comp, neg_comp, C_comp, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, ofNat_comp, one_comp]
  ring

open Polynomial in
theorem EisensteinCoeffs.isEisensteinAt {p : ℤ} {f : Cubic ℤ}
    (hf : EisensteinCoeffs p f) (hp : ¬ IsUnit p) :
    f.toPoly.IsEisensteinAt (Ideal.span ({p} : Set ℤ)) := by
  obtain ⟨ha,hb,hc,hd,hd2⟩ := hf
  have hm := Cubic.monic_of_a_eq_one ha
  refine hm.isEisensteinAt_of_mem_of_notMem (fun h => hp (Ideal.span_singleton_eq_top.mp h)) ?_ ?_
  · intro n hn
    rw [Cubic.natDegree_of_a_ne_zero (by simp [ha])] at hn
    rw [Ideal.mem_span_singleton]
    interval_cases n
    · simpa only [Cubic.coeff_eq_d] using hd
    · simpa only [Cubic.coeff_eq_c] using hc
    · simpa only [Cubic.coeff_eq_b] using hb
  · simpa only [Cubic.coeff_eq_d, Ideal.span_singleton_pow, Ideal.mem_span_singleton] using hd2

open Polynomial in
theorem isEisensteinAt_three (A D P : ℤ) (h : A^2-A*D+D^2 = P^2)
    (hA : (3 : ℤ) ∣ A-1) (hP : (3 : ℤ) ∣ P-1) :
    ((generator P (A-2*D)).toPoly.comp (X+C 1)).IsEisensteinAt
      (Ideal.span ({3} : Set ℤ)) := by
  rw [← shifted_eq_comp]
  exact (eisenstein_at_three A D P h hA hP).isEisensteinAt (by rw [Int.isUnit_iff]; decide)

theorem not_dvd_generator_discriminant_factors {P a b : ℤ} (hP : Prime P)
    (h3 : ¬ P ∣ (3 : ℤ)) (hn : a^2-a*b+b^2 = P) :
    (¬ P ∣ a^2-b^2) ∧ (¬ P ∣ (a^2-b^2)-2*(2*a*b-b^2)) := by
  let A := a^2-b^2
  let D := 2*a*b-b^2
  have hnorm : A^2-A*D+D^2=P^2 := by
    dsimp [A,D]; rw [primary_norm_identity, hn]
  change (¬ P ∣ A) ∧ (¬ P ∣ A-2*D)
  have ha : ¬ P ∣ A := by
    intro hA
    have hDsq : P ∣ D^2 := by
      obtain ⟨k,hk⟩ := hA
      refine ⟨P-k*A+k*D, ?_⟩
      linear_combination hnorm-(A-D)*hk
    have hD := hP.dvd_of_dvd_pow hDsq
    have hb : P ∣ b := by
      have hprod : P ∣ b*(2*a-b) := by convert hD using 1; dsimp [D]; ring
      rcases hP.dvd_or_dvd hprod with h | h
      · exact h
      · have h3sq : P ∣ 3*b^2 := by
          obtain ⟨k,hk⟩ := h
          refine ⟨4-k*(2*a-b), ?_⟩
          linear_combination 4*hn-(2*a-b)*hk
        exact hP.dvd_of_dvd_pow ((hP.dvd_or_dvd h3sq).resolve_left h3)
    have hasq : P ∣ a^2 := by
      obtain ⟨i,hi⟩ := hA
      obtain ⟨k,hk⟩ := hb
      refine ⟨i+k*b, ?_⟩
      change a^2-b^2 = P*i at hi
      linear_combination hi+b*hk
    obtain ⟨l,hl⟩ := hP.dvd_of_dvd_pow hasq
    obtain ⟨m,hm⟩ := hb
    have hup : 1 = P*(l^2-l*m+m^2) := by
      apply mul_left_cancel₀ hP.ne_zero
      rw [mul_one]
      linear_combination -hn + (a+P*l-b)*hl + (b+P*m-P*l)*hm
    exact hP.not_isUnit (isUnit_of_dvd_one ⟨_,hup⟩)
  refine ⟨ha, ?_⟩
  rintro ⟨k,hk⟩
  have hh : P ∣ 3*A^2 := by
    refine ⟨4*P-k*(A-2*D), ?_⟩
    linear_combination -key_norm hnorm-(A-2*D)*hk
  exact ha (hP.dvd_of_dvd_pow ((hP.dvd_or_dvd hh).resolve_left h3))

open Polynomial in
theorem isEisensteinAt_role {P a b : ℤ} (hP : Prime P)
    (h3 : ¬ P ∣ (3 : ℤ)) (hn : a^2-a*b+b^2 = P) :
    (generator P ((a^2-b^2)-2*(2*a*b-b^2))).toPoly.IsEisensteinAt
      (Ideal.span ({P} : Set ℤ)) := by
  exact (eisenstein_at_role P _ hP.ne_zero
    (fun h => (not_dvd_generator_discriminant_factors hP h3 hn).2 (hP.dvd_of_dvd_pow h))).isEisensteinAt hP.not_isUnit

open Polynomial in
theorem primary_pair_eisenstein {P a b : ℤ} (hP : Prime P)
    (hn : a^2-a*b+b^2 = P) (ha : (3:ℤ) ∣ a-1) (hb : (3:ℤ) ∣ b) :
    let g := (generator P ((a^2-b^2)-2*(2*a*b-b^2))).toPoly
    g.IsEisensteinAt (Ideal.span ({P} : Set ℤ)) ∧
      (g.comp (X+C 1)).IsEisensteinAt (Ideal.span ({3} : Set ℤ)) := by
  have hA : (3:ℤ) ∣ a^2-b^2-1 := by
    obtain ⟨k,hk⟩ := ha
    obtain ⟨l,hl⟩ := hb
    refine ⟨k*(a+1)-l*b, ?_⟩
    linear_combination (a+1)*hk-b*hl
  have hPone : (3:ℤ) ∣ P-1 := by
    obtain ⟨k,hk⟩ := ha
    obtain ⟨l,hl⟩ := hb
    refine ⟨k*(a+1)+l*(b-a), ?_⟩
    linear_combination -hn+(a+1)*hk+(b-a)*hl
  have hP3 : ¬ P ∣ (3:ℤ) := by
    obtain ⟨k,hk⟩ := hPone
    rintro ⟨l,hl⟩
    apply hP.not_isUnit
    apply isUnit_of_dvd_one
    refine ⟨1-l*k, ?_⟩
    linear_combination -hk-k*hl
  refine ⟨isEisensteinAt_role hP hP3 hn, isEisensteinAt_three _ _ _ ?_ hA hPone⟩
  rw [primary_norm_identity, hn]

end D5.S3.Factorization.QuadraticIdeals.GoldenCubicThueEisenstein


set_option autoImplicit false
namespace D5.S3.Factorization.QuadraticIdeals.GoldenCubicThueEisenstein

open Polynomial D5.S1.Scale
open D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
open D5.S3.Factorization.QuadraticIdeals.GoldenCubicThueDescent

theorem primary_coordinate_divisibilities (pi : EisensteinOrder)
    (hp : (3 : EisensteinOrder) ∣ pi - 1) :
    (3 : ℤ) ∣ pi.re - 1 ∧ (3 : ℤ) ∣ pi.im := by
  obtain ⟨k,hk⟩ := hp
  have hre := congrArg QuadraticAlgebra.re hk
  have him := congrArg QuadraticAlgebra.im hk
  have r3 : (3 : EisensteinOrder).re = 3 := rfl
  have i3 : (3 : EisensteinOrder).im = 0 := rfl
  simp only [QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_mul,
    QuadraticAlgebra.im_mul, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
    r3, i3, zero_mul, mul_zero, add_zero, sub_zero] at hre him
  exact ⟨⟨k.re,hre⟩, ⟨k.im,him⟩⟩

/-- Both Eisenstein certificates belong to one integral polynomial constructed
from the same square factor as the native exact Thue descent. -/
theorem native_role_pair_eisenstein (j P Q : ℕ) (hj : 1 ≤ j) (hP : P.Prime)
    (hQ : Q.Prime) (hPQ : P ≠ Q)
    (hfact : blockNorm ((goldenLucas (3 ^ j) - 1).toNat) = P ^ 2 * Q ^ 3) :
    ∃ pi : EisensteinOrder,
      Ideal.span {pi} = orientedIdeal ((goldenLucas (3 ^ j) - 1).toNat) ⊔
        Ideal.span {(P : EisensteinOrder)} ∧
      QuadraticAlgebra.norm pi = (P : ℤ) ∧
      let A := pi.re^2-pi.im^2
      let D := 2*pi.re*pi.im-pi.im^2
      let g := (generator (P:ℤ) (A-2*D)).toPoly
      g.Monic ∧ g.natDegree = 3 ∧
      g.IsEisensteinAt (Ideal.span ({(P:ℤ)} : Set ℤ)) ∧
      (g.comp (X+C 1)).IsEisensteinAt (Ideal.span ({3} : Set ℤ)) := by
  obtain ⟨pi, _, hn, _, _, _, hi, _, hp, _⟩ :=
    (golden_cubic_exact_thue_descent j P Q hj hP hQ hPQ).1 hfact
  obtain ⟨ha,hb⟩ := primary_coordinate_divisibilities pi hp
  have hprime : Prime (P:ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hP)
  have hn' : pi.re^2-pi.re*pi.im+pi.im^2=(P:ℤ) := by
    simp only [QuadraticAlgebra.norm_def] at hn
    linear_combination hn
  refine ⟨pi, hi, hn, ?_, ?_, primary_pair_eisenstein hprime hn' ha hb⟩
  · exact Cubic.monic_of_a_eq_one rfl
  · exact Cubic.natDegree_of_a_ne_zero (by change (1:ℤ) ≠ 0; decide)

end D5.S3.Factorization.QuadraticIdeals.GoldenCubicThueEisenstein
