/- GID: D5/S3/Factorization/Mordell/EllipticTraceNormDivisibility
   generality: I
   mirror-B: D5/B/S3/Factorization/Mordell/EllipticTraceNormDivisibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Smooth Weierstrass trace and norm control polynomial denominators. -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Trace and norm divisibility on a smooth Weierstrass curve

The denominator divides both polynomial coordinates when it divides the trace and its square
divides the norm. The proof uses smoothness over prime residue fields and factorization induction.

Source: TauCetiProject/TauCeti, commit 33c2099c678ea391f7ea3e0ddaf945a76a625e5d,
TauCeti/AlgebraicGeometry/EllipticCurve/Affine/CoordinateRing.lean.
The same source bytes occur at 65482a19dabd31843aab0cf8469c5e7613988eba.
This source distribution is modified from the cited source.
-/


open Polynomial Polynomial.Bivariate
open WeierstrassCurve.Affine

namespace D5.S3.Factorization.Mordell.EllipticTraceNormDivisibility

variable {F : Type*} [Field F]

theorem elliptic_trace_norm_denominator_divides_coordinates
    (W : WeierstrassCurve.Affine F) [W.IsElliptic] (d : F[X]) : ∀ p q : F[X], d ≠ 0 →
    d ∣ 2 * p - q * (C W.a₁ * X + C W.a₃) →
    d ^ 2 ∣ p ^ 2 - p * q * (C W.a₁ * X + C W.a₃) -
      q ^ 2 * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆) →
    d ∣ p ∧ d ∣ q := by
  have dvd_a₁_mul_add_of_dvd_two_mul_sub_of_sq_dvd
      {π g : F[X]}
      (hs : π ∣ 2 * g - (C W.a₁ * X + C W.a₃))
      (hsq : π ^ 2 ∣ g ^ 2 - g * (C W.a₁ * X + C W.a₃) -
        (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)) :
      π ∣ C W.a₁ * g + (3 * X ^ 2 + 2 * C W.a₂ * X + C W.a₄) := by
    have hd : derivative (g ^ 2 - g * (C W.a₁ * X + C W.a₃) -
        (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)) =
        derivative g * (2 * g - (C W.a₁ * X + C W.a₃)) -
          (C W.a₁ * g + (3 * X ^ 2 + 2 * C W.a₂ * X + C W.a₄)) := by
      simp only [derivative_sub, derivative_mul, derivative_pow, derivative_add, derivative_C,
        derivative_X, map_ofNat, Nat.cast_ofNat]
      ring1
    have hd' : π ∣ derivative g * (2 * g - (C W.a₁ * X + C W.a₃)) -
        (C W.a₁ * g + (3 * X ^ 2 + 2 * C W.a₂ * X + C W.a₄)) := by
      rw [← hd]
      simpa using Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd hsq
    simpa using dvd_sub (hs.mul_left (derivative g)) hd'
  have not_sq_dvd_of_dvd_two_mul_sub
      {π g : F[X]} (hπ : Prime π)
      (hs : π ∣ 2 * g - (C W.a₁ * X + C W.a₃)) :
      ¬π ^ 2 ∣ g ^ 2 - g * (C W.a₁ * X + C W.a₃) -
        (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆) := by
    intro hsq
    have : Fact (Irreducible π) := ⟨hπ.irreducible⟩
    have hev : ∀ r : F[X], π ∣ r → aeval (AdjoinRoot.root π) r = 0 := fun r hr => by
      rw [AdjoinRoot.aeval_eq]; exact AdjoinRoot.mk_eq_zero.mpr hr
    have h₁ := hev _ ((dvd_pow_self π two_ne_zero).trans hsq)
    have h₂ := hev _ hs
    have h₃ := hev _ (dvd_a₁_mul_add_of_dvd_two_mul_sub_of_sq_dvd hs hsq)
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, aeval_C, aeval_X] at h₁ h₂ h₃
    have key : (W.map (algebraMap F (AdjoinRoot π))).Nonsingular (AdjoinRoot.root π)
        (-aeval (AdjoinRoot.root π) g) := equation_iff_nonsingular.mp <| by
      rw [equation_iff']
      simp only [_root_.WeierstrassCurve.map_a₁, _root_.WeierstrassCurve.map_a₂,
        _root_.WeierstrassCurve.map_a₃, _root_.WeierstrassCurve.map_a₄,
        _root_.WeierstrassCurve.map_a₆]
      linear_combination h₁
    rw [nonsingular_iff'] at key
    refine key.2.elim (fun h => h ?_) fun h => h ?_
    · simp only [_root_.WeierstrassCurve.map_a₁, _root_.WeierstrassCurve.map_a₂,
        _root_.WeierstrassCurve.map_a₄]
      linear_combination -h₃
    · simp only [_root_.WeierstrassCurve.map_a₁, _root_.WeierstrassCurve.map_a₃]
      linear_combination -h₂
  have exists_dvd_two_mul_sub_and_sq_dvd_of_not_dvd
      {π p q : F[X]} (hπ : Prime π)
      (hq : ¬π ∣ q) (ht : π ∣ 2 * p - q * (C W.a₁ * X + C W.a₃))
      (hn : π ^ 2 ∣ p ^ 2 - p * q * (C W.a₁ * X + C W.a₃) -
        q ^ 2 * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)) :
      ∃ g : F[X], π ∣ 2 * g - (C W.a₁ * X + C W.a₃) ∧
        π ^ 2 ∣ g ^ 2 - g * (C W.a₁ * X + C W.a₃) -
          (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆) := by
    have : Fact (Irreducible π) := ⟨hπ.irreducible⟩
    have hqk : AdjoinRoot.mk π q ≠ 0 := fun h => hq (AdjoinRoot.mk_eq_zero.mp h)
    obtain ⟨g, hg⟩ := AdjoinRoot.mk_surjective (AdjoinRoot.mk π p / AdjoinRoot.mk π q)
    obtain ⟨p₁, hp₁⟩ : π ∣ p - g * q := AdjoinRoot.mk_eq_zero.mp <| by
      rw [map_sub, map_mul, hg, div_mul_cancel₀ _ hqk, sub_self]
    obtain ⟨f, hf⟩ : π ∣ 2 * g - (C W.a₁ * X + C W.a₃) := by
      have hprod : π ∣ q * (2 * g - (C W.a₁ * X + C W.a₃)) := by
        obtain ⟨t₁, ht₁⟩ := ht
        exact ⟨t₁ - 2 * p₁, by linear_combination ht₁ - 2 * hp₁⟩
      exact (hπ.dvd_or_dvd hprod).resolve_left hq
    refine ⟨g, ⟨f, hf⟩, ?_⟩
    refine hπ.pow_dvd_of_dvd_mul_left (a := q ^ 2) 2 (fun h => hq (hπ.dvd_of_dvd_pow h)) ?_
    obtain ⟨n₁, hn₁⟩ := hn
    exact ⟨n₁ - p₁ * q * f - p₁ ^ 2, by
      linear_combination hn₁ -
        (p + g * q + π * p₁ - q * (C W.a₁ * X + C W.a₃)) * hp₁ - π * p₁ * q * hf⟩
  have dvd_and_dvd_of_prime
      {π p q : F[X]} (hπ : Prime π)
      (ht : π ∣ 2 * p - q * (C W.a₁ * X + C W.a₃))
      (hn : π ^ 2 ∣ p ^ 2 - p * q * (C W.a₁ * X + C W.a₃) -
        q ^ 2 * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)) :
      π ∣ p ∧ π ∣ q := by
    have hq : π ∣ q := by
      by_contra hq
      obtain ⟨g, hs, hsq⟩ := exists_dvd_two_mul_sub_and_sq_dvd_of_not_dvd
          hπ hq ht hn
      exact not_sq_dvd_of_dvd_two_mul_sub hπ hs hsq
    refine ⟨?_, hq⟩
    obtain ⟨q₁, rfl⟩ := hq
    refine hπ.dvd_of_dvd_pow (n := 2) ?_
    obtain ⟨n₁, hn₁⟩ := dvd_trans (dvd_pow_self π two_ne_zero) hn
    exact ⟨n₁ + p * q₁ * (C W.a₁ * X + C W.a₃) +
      π * q₁ ^ 2 * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆), by linear_combination hn₁⟩
  refine UniqueFactorizationMonoid.induction_on_prime d (fun p q hd => absurd rfl hd)
    (fun u hu p q _ _ _ => ⟨hu.dvd, hu.dvd⟩) fun a π ha hπ ih p q _ ht hn => ?_
  obtain ⟨hp, hq⟩ := dvd_and_dvd_of_prime hπ ((dvd_mul_right π a).trans
      ht)
    (dvd_trans (pow_dvd_pow_of_dvd (dvd_mul_right π a) 2) hn)
  obtain ⟨p', rfl⟩ := hp
  obtain ⟨q', rfl⟩ := hq
  have ht' : a ∣ 2 * p' - q' * (C W.a₁ * X + C W.a₃) := by
    refine (mul_dvd_mul_iff_left hπ.ne_zero).mp ?_
    have htrace : π * (2 * p' - q' * (C W.a₁ * X + C W.a₃)) =
        2 * (π * p') - π * q' * (C W.a₁ * X + C W.a₃) := by ring
    rw [htrace]
    exact ht
  have hn' : a ^ 2 ∣ p' ^ 2 - p' * q' * (C W.a₁ * X + C W.a₃) -
      q' ^ 2 * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆) := by
    refine (mul_dvd_mul_iff_left (pow_ne_zero 2 hπ.ne_zero)).mp ?_
    have hnorm : π ^ 2 * (p' ^ 2 - p' * q' * (C W.a₁ * X + C W.a₃) -
        q' ^ 2 * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)) =
        (π * p') ^ 2 - π * p' * (π * q') * (C W.a₁ * X + C W.a₃) -
          (π * q') ^ 2 * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆) := by ring
    rw [hnorm, ← mul_pow]
    exact hn
  obtain ⟨hp', hq'⟩ := ih p' q' ha ht' hn'
  exact ⟨mul_dvd_mul_left π hp', mul_dvd_mul_left π hq'⟩

end D5.S3.Factorization.Mordell.EllipticTraceNormDivisibility
