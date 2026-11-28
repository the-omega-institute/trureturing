/- GID: D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeCMThickening
   generality: I
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/GoldenCubicNativeCMThickening
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Exact integral CM model contact sees the earlier block valuation without doubling. -/

import D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeElliptic
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

set_option autoImplicit false

namespace D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeCMThickening
open WeierstrassCurve
open D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeElliptic

theorem short_change_forces_a6_zero {R : Type*} [CommRing R] (l : R)
    (h₂ : IsUnit (2:R)) (h₃ : IsUnit (3:R)) (C : VariableChange R)
    (h : C • (model l 1) = model 0 1) : 2*(l^2+3)*l = 0 := by
  have nzCancel (u : Rˣ) (n : ℕ) (a : R) (H : ↑u ^ n * a = 0) : a = 0 := by
    have hu : IsUnit ((u:R)^n) := u.isUnit.pow _
    apply (IsUnit.mul_left_inj hu).mp
    simpa [mul_comm] using H
  have h₁ := congrArg a₁ h
  rw [variableChange_a₁] at h₁
  simp [model] at h₁
  have hs0 := nzCancel C.u⁻¹ 1 (2*C.s) (by simpa using h₁)
  have hs : C.s = 0 :=
    (IsUnit.mul_left_inj h₂).mp (by simpa [mul_comm] using hs0)
  have h₂' := congrArg a₂ h
  rw [variableChange_a₂] at h₂'
  simp [model, hs] at h₂'
  have hr0 := nzCancel C.u⁻¹ 2 (3*C.r) h₂'
  have hr : C.r = 0 :=
    (IsUnit.mul_left_inj h₃).mp (by simpa [mul_comm] using hr0)
  have h₃' := congrArg a₃ h
  rw [variableChange_a₃] at h₃'
  simp [model, hr] at h₃'
  have ht0 := nzCancel C.u⁻¹ 3 (2*C.t) h₃'
  have ht : C.t = 0 :=
    (IsUnit.mul_left_inj h₂).mp (by simpa [mul_comm] using ht0)
  have h₆ := congrArg a₆ h
  rw [variableChange_a₆] at h₆
  simp [model, hr, ht] at h₆
  exact nzCancel C.u⁻¹ 6 _ h₆

open D5.S1.Scale D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeCyclic
open D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeForwardSplitting

theorem native_cm_model_thickening {p i j : ℕ} [Fact p.Prime] (n : ℕ)
    (hp : 3 < p) (hi : 1 ≤ i) (hij : i < j)
    (hB : (p:ℤ) ∣ goldenLucas (3^i)^2+3) :
    (∃ C : VariableChange (ZMod (p^n)),
      C • model (goldenLucas (3^j):ZMod (p^n)) 1 = model 0 1) ↔
      n ≤ padicValInt p (goldenLucas (3^i)^2+3) := by
  have hp' : p.Prime := Fact.out
  let l := goldenLucas (3^j)
  have hn : l ≠ 0 := by
    have hm := (native_lucas_mod j (by omega)).1
    dsimp [l]
    omega
  have hdiv : (p:ℤ) ∣ l := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    apply later_lucas_vanishes i j hi hij
    simpa only [Int.cast_add, Int.cast_pow, Int.cast_ofNat] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hB
  have hc₂ : IsUnit (2 : ZMod (p^n)) := by
    apply ZMod.isUnit_prime_of_not_dvd Nat.prime_two
    intro H
    have hh := Nat.prime_two.dvd_of_dvd_pow H
    have h' : 2 = p := (Nat.dvd_prime hp').mp hh |>.resolve_left (by decide)
    omega
  have hc₃ : IsUnit (3 : ZMod (p^n)) := by
    apply ZMod.isUnit_prime_of_not_dvd Nat.prime_three
    intro H
    have hh := Nat.prime_three.dvd_of_dvd_pow H
    have h' : 3 = p := (Nat.dvd_prime hp').mp hh |>.resolve_left (by decide)
    omega
  have hB' : ¬ (p:ℤ) ∣ l^2+3 := by
    intro H
    have h₁ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdiv
    have h₂ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr H
    have h₃ : (3 : ZMod p) = 0 := by simpa [h₁] using h₂
    exact (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 3) hp)
      ((ZMod.natCast_eq_zero_iff 3 p).mp h₃)
  have h₂nd : ¬ (p:ℤ) ∣ (2:ℤ) := by
    exact_mod_cast (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) (by omega : 2 < p))
  have hdepth : padicValInt p l = padicValInt p (goldenLucas (3^i)^2+3) :=
    native_later_lucas_depth hp hi hij hB
  constructor
  · rintro ⟨C,hC⟩
    have h0 := short_change_forces_a6_zero (l:ZMod (p^n)) hc₂ hc₃ C hC
    have h0' : ((p^n:ℕ):ℤ) ∣ 2*(l^2+3)*l := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p^n)).mp
      simpa only [Int.cast_mul, Int.cast_add, Int.cast_pow, Int.cast_ofNat] using h0
    rw [Nat.cast_pow, padicValInt_dvd_iff, or_iff_right
      (mul_ne_zero (mul_ne_zero (by norm_num) (by positivity)) hn),
      padicValInt.mul (mul_ne_zero (by norm_num) (by positivity)) hn,
      padicValInt.mul (by norm_num) (by positivity),
      padicValInt.eq_zero_of_not_dvd h₂nd, padicValInt.eq_zero_of_not_dvd hB',
      zero_add, zero_add, hdepth] at h0'
    exact h0'
  · intro H
    have hh : (p:ℤ)^n ∣ l := (padicValInt_dvd_iff _ _).mpr (Or.inr (hdepth ▸ H))
    have hl : (l:ZMod (p^n)) = 0 := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p^n)).mpr
      exact_mod_cast hh
    exact ⟨1, by rw [show (goldenLucas (3^j):ZMod (p^n)) = 0 from hl, one_smul]⟩

end D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeCMThickening
