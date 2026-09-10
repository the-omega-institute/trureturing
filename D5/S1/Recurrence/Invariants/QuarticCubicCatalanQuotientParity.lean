/- GID: D5/S1/Recurrence/Invariants/QuarticCubicCatalanQuotientParity
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/QuarticCubicCatalanQuotientParity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Integral contraction and binary Catalan reversion prove Hanna's parity conjecture. -/

import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.FieldTheory.Finite.Basic

open PowerSeries

namespace D5.S1.Recurrence.Invariants.QuarticCubicCatalanQuotientParity

variable {R : Type*} [CommRing R]

private def Agree (d : ℕ) (f g : PowerSeries R) : Prop :=
  ∀ n < d, coeff n f = coeff n g

private theorem agree_iff (d : ℕ) (f g : PowerSeries R) :
    Agree d f g ↔ (X : PowerSeries R) ^ d ∣ f - g := by
  simp [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]

private theorem agree_pow {d : ℕ} {f g : PowerSeries R}
    (h : Agree d f g) (k : ℕ) : Agree d (f ^ k) (g ^ k) :=
  (agree_iff _ _ _).mpr (((agree_iff _ _ _).mp h).trans (sub_dvd_pow_sub_pow f g k))

private theorem agree_X_mul {d : ℕ} {f g : PowerSeries R}
    (h : Agree d f g) : Agree (d + 1) (X * f) (X * g) := by
  apply (agree_iff _ _ _).mpr
  have hd := mul_dvd_mul_left X ((agree_iff _ _ _).mp h)
  simpa only [← pow_succ', mul_sub] using hd

private theorem subst_constant {u : PowerSeries R} (hu : constantCoeff u = 0)
    (f : PowerSeries R) : constantCoeff (f.subst u) = constantCoeff f := by
  rw [← coeff_zero_eq_constantCoeff, coeff_subst' (.of_constantCoeff_zero hu)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro k hk
    have hz := X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hu) k)
      0 (Nat.pos_of_ne_zero hk)
    rw [hz, smul_zero]

private theorem subst_contract {d : ℕ} (hd : 1 ≤ d) {f g u v : PowerSeries R}
    (hu : X ^ 2 ∣ u) (hv : X ^ 2 ∣ v)
    (hfg : Agree d f g) (huv : Agree (d + 1) u v) :
    Agree (d + 1) (f.subst u) (g.subst v) := by
  have hu0 : constantCoeff u = 0 := X_dvd_iff.mp ((dvd_pow_self X (by omega : 2 ≠ 0)).trans hu)
  have hv0 : constantCoeff v = 0 := X_dvd_iff.mp ((dvd_pow_self X (by omega : 2 ≠ 0)).trans hv)
  intro n hn
  rw [coeff_subst' (.of_constantCoeff_zero hu0), coeff_subst' (.of_constantCoeff_zero hv0)]
  apply finsum_congr
  intro k
  by_cases hk : k < d
  · rw [hfg k hk, agree_pow huv k n hn]
  · have hnu : coeff n (u ^ k) = 0 := by
      apply X_pow_dvd_iff.mp _ n (by omega : n < 2 * k)
      simpa only [← pow_mul] using pow_dvd_pow_of_dvd hu k
    have hnv : coeff n (v ^ k) = 0 := by
      apply X_pow_dvd_iff.mp _ n (by omega : n < 2 * k)
      simpa only [← pow_mul] using pow_dvd_pow_of_dvd hv k
    rw [hnu, hnv, smul_zero, smul_zero]

private noncomputable def inner (p : ℕ) (b : PowerSeries R) : PowerSeries R :=
  X ^ p * (1 + (p : PowerSeries R) * X * b ^ p)

private theorem inner_zero (p : ℕ) (hp : 1 ≤ p) (b : PowerSeries R) :
    constantCoeff (inner p b) = 0 := by simp [inner, zero_pow (by omega : p ≠ 0)]

private theorem inner_two (p : ℕ) (hp : 2 ≤ p) (b : PowerSeries R) :
    (X : PowerSeries R) ^ 2 ∣ inner p b :=
  dvd_mul_of_dvd_left (pow_dvd_pow X hp) _

private theorem inner_agree (p : ℕ) {d : ℕ} {b c : PowerSeries R}
    (h : Agree d b c) : Agree (d + 1) (inner p b) (inner p c) := by
  apply (agree_iff _ _ _).mpr
  have hd := (agree_iff _ _ _).mp (agree_X_mul (agree_pow h p))
  convert dvd_mul_of_dvd_right hd ((X : PowerSeries R) ^ p * p) using 1
  simp only [inner]
  ring

private noncomputable def step (b : PowerSeries R) : PowerSeries R :=
  b + (1 + 4 * X * b ^ 4) * b.subst (inner 4 b) -
    b * (1 + 3 * X * b ^ 3) * b.subst (inner 3 b)

-- Writing A = X * b cancels X^4 from the equation; this update uses no division.

private theorem step_one {b : PowerSeries R} (hb : constantCoeff b = 1) :
    constantCoeff (step b) = 1 := by
  simp [step, subst_constant (inner_zero 3 (by omega) b),
    subst_constant (inner_zero 4 (by omega) b), hb]

private theorem step_agree {d : ℕ} {b c : PowerSeries R}
    (hb : constantCoeff b = 1) (hc : constantCoeff c = 1)
    (h : Agree d b c) : Agree (d + 1) (step b) (step c) := by
  by_cases hd : d = 0
  · subst d
    intro n hn
    have hn0 : n = 0 := by omega
    simp only [hn0, coeff_zero_eq_constantCoeff, step_one hb, step_one hc]
  have h3 := subst_contract (by omega : 1 ≤ d) (inner_two 3 (by omega) b)
    (inner_two 3 (by omega) c) h (inner_agree 3 h)
  have h4 := subst_contract (by omega : 1 ≤ d) (inner_two 4 (by omega) b)
    (inner_two 4 (by omega) c) h (inner_agree 4 h)
  have hpow := (agree_iff _ _ _).mp (agree_X_mul (agree_pow h 4))
  have hsub3 := (agree_iff _ _ _).mp h3
  have hsub4 := (agree_iff _ _ _).mp h4
  have hz : (X : PowerSeries R) ∣ 1 - c.subst (inner 3 c) := by
    apply X_dvd_iff.mpr
    simp [subst_constant (inner_zero 3 (by omega) c), hc]
  have hbc := mul_dvd_mul ((agree_iff _ _ _).mp h) hz
  rw [← pow_succ] at hbc
  apply (agree_iff _ _ _).mpr
  have hfirst := dvd_mul_of_dvd_left hsub4 (1 + 4 * X * b ^ 4)
  have hsecond := dvd_mul_of_dvd_right hpow (4 * c.subst (inner 4 c))
  have hthird := dvd_mul_of_dvd_left hsub3 (b + 3 * X * b ^ 4)
  have hfourth := dvd_mul_of_dvd_right hpow (3 * c.subst (inner 3 c))
  convert dvd_sub (dvd_sub (dvd_add (dvd_add hbc hfirst) hsecond) hthird) hfourth using 1
  simp only [step]
  ring

private theorem fixed_unique {b c : PowerSeries R}
    (hb : constantCoeff b = 1) (hc : constantCoeff c = 1)
    (fb : b = step b) (fc : c = step c) : b = c := by
  have hall : ∀ d, Agree d b c := by
    intro d
    induction d with
    | zero => intro n hn; omega
    | succ d ih => simpa only [← fb, ← fc] using step_agree hb hc ih
  ext n
  exact hall (n + 1) n (by omega)

private noncomputable def approximation : ℕ → PowerSeries R
  | 0 => 1
  | d + 1 => step (approximation d)

private theorem approximation_one (d : ℕ) :
    constantCoeff (approximation (R := R) d) = 1 := by
  induction d with
  | zero => simp [approximation]
  | succ d ih => exact step_one ih

private theorem approximation_stable {d e : ℕ} (h : d ≤ e) :
    Agree d (approximation (R := R) d) (approximation e) := by
  induction d generalizing e with
  | zero => intro n hn; omega
  | succ d ih =>
    cases e with
    | zero => omega
    | succ e => exact step_agree (approximation_one d) (approximation_one e) (ih (by omega))

private noncomputable def solution : PowerSeries R :=
  mk (fun n => coeff n (approximation (n + 1)))

private theorem solution_agree (d : ℕ) :
    Agree d (solution (R := R)) (approximation d) := by
  intro n hn
  simpa only [solution, coeff_mk] using
    approximation_stable (R := R) (by omega : n + 1 ≤ d) n (by omega)

private theorem solution_one : constantCoeff (solution (R := R)) = 1 := by
  rw [← coeff_zero_eq_constantCoeff, solution_agree 1 0 (by omega), coeff_zero_eq_constantCoeff]
  exact approximation_one 1

private theorem solution_fixed : solution (R := R) = step solution := by
  ext n
  have hg := solution_agree (R := R) (n + 2) n (by omega)
  have hs := step_agree solution_one (approximation_one (n + 1))
    (solution_agree (R := R) (n + 1)) n (by omega)
  exact hg.trans hs.symm

private theorem normalized_iff (b : PowerSeries R) :
    b = step b ↔ (X * b) * (X * b).subst (X ^ 3 + 3 * X * (X * b) ^ 3) =
      (X * b).subst (X ^ 4 + 4 * X * (X * b) ^ 4) := by
  have hi3 : X ^ 3 + 3 * X * (X * b) ^ 3 = inner 3 b := by simp [inner]; ring
  have hi4 : X ^ 4 + 4 * X * (X * b) ^ 4 = inner 4 b := by simp [inner]; ring
  rw [hi3, hi4, subst_mul (.of_constantCoeff_zero (inner_zero 3 (by omega) b)),
    subst_mul (.of_constantCoeff_zero (inner_zero 4 (by omega) b)),
    subst_X (.of_constantCoeff_zero (inner_zero 3 (by omega) b)),
    subst_X (.of_constantCoeff_zero (inner_zero 4 (by omega) b))]
  have he : (X * b) * (inner 3 b * b.subst (inner 3 b)) =
      X ^ 4 * (b * (1 + 3 * X * b ^ 3) * b.subst (inner 3 b)) := by
    simp [inner]; ring
  have he4 : inner 4 b * b.subst (inner 4 b) =
      X ^ 4 * ((1 + 4 * X * b ^ 4) * b.subst (inner 4 b)) := by
    simp only [inner, Nat.cast_ofNat]
    ring
  rw [he, he4, X_pow_mul_inj]
  simp only [step]
  constructor <;> intro h <;> linear_combination h

noncomputable def a (n : ℕ) : ℤ := coeff n (X * (solution : PowerSeries ℤ))

noncomputable def generatingSeries : PowerSeries ℤ := mk a

private theorem generating_eq : generatingSeries = X * solution := by
  ext n
  simp [generatingSeries, a]

theorem generating_equation : constantCoeff generatingSeries = 0 ∧
    coeff 1 generatingSeries = 1 ∧
    generatingSeries * generatingSeries.subst (X ^ 3 + 3 * X * generatingSeries ^ 3) =
      generatingSeries.subst (X ^ 4 + 4 * X * generatingSeries ^ 4) := by
  rw [generating_eq]
  exact ⟨by simp, by simpa using (solution_one (R := ℤ)),
    (normalized_iff solution).mp solution_fixed⟩

private theorem equation_unique {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (hf1 : coeff 1 f = 1) (hg1 : coeff 1 g = 1)
    (fe : f * f.subst (X ^ 3 + 3 * X * f ^ 3) = f.subst (X ^ 4 + 4 * X * f ^ 4))
    (ge : g * g.subst (X ^ 3 + 3 * X * g ^ 3) = g.subst (X ^ 4 + 4 * X * g ^ 4)) :
    f = g := by
  obtain ⟨b, rfl⟩ := X_dvd_iff.mpr hf
  obtain ⟨c, rfl⟩ := X_dvd_iff.mpr hg
  have hb : constantCoeff b = 1 := by simpa using hf1
  have hc : constantCoeff c = 1 := by simpa using hg1
  rw [fixed_unique hb hc ((normalized_iff b).mpr fe) ((normalized_iff c).mpr ge)]

theorem generating_unique (f : PowerSeries ℤ)
    (hf : constantCoeff f = 0) (hf1 : coeff 1 f = 1)
    (he : f * f.subst (X ^ 3 + 3 * X * f ^ 3) = f.subst (X ^ 4 + 4 * X * f ^ 4)) :
    f = generatingSeries :=
  equation_unique hf generating_equation.1 hf1 generating_equation.2.1 he generating_equation.2.2

private noncomputable def binary : PowerSeries (ZMod 2) :=
  (X + X ^ 2 : PowerSeries (ZMod 2)).substInvOfIsUnit (by simp)

private theorem binary_zero : constantCoeff binary = 0 := by simp [binary]

private theorem binary_quadratic : binary + binary ^ 2 = X := by
  have h := subst_substInvOfIsUnit_right (X + X ^ 2 : PowerSeries (ZMod 2))
    (by simp) (by simp)
  change (X + X ^ 2 : PowerSeries (ZMod 2)).subst binary = X at h
  simpa only [subst_add (.of_constantCoeff_zero binary_zero),
    subst_pow (.of_constantCoeff_zero binary_zero),
    subst_X (.of_constantCoeff_zero binary_zero)] using h

private theorem binary_left : binary.subst (X + X ^ 2 : PowerSeries (ZMod 2)) = X :=
  subst_substInvOfIsUnit_left (X + X ^ 2 : PowerSeries (ZMod 2)) (by simp) (by simp)

private theorem square_subst (f : PowerSeries (ZMod 2)) : f.subst (X ^ 2) = f ^ 2 := by
  have h := MvPowerSeries.map_frobenius_expand 2 (by decide : 2 ≠ 0) (f := f)
  change (f.expand 2 (by decide)).map (frobenius (ZMod 2) 2) = f ^ 2 at h
  rw [ZMod.frobenius_zmod, PowerSeries.map_id, expand_apply] at h
  exact h

private theorem fourth_subst (f : PowerSeries (ZMod 2)) : f.subst (X ^ 4) = f ^ 4 := by
  have hx : HasSubst (X ^ 2 : PowerSeries (ZMod 2)) := .X_pow (by decide)
  calc
    f.subst (X ^ 4) = PowerSeries.subst (X ^ 2) (f.subst (X ^ 2)) := by
      rw [subst_comp_subst_apply hx hx, subst_pow hx, subst_X hx, ← pow_mul]
    _ = f ^ 4 := by rw [square_subst, square_subst, ← pow_mul]

private theorem binary_cubic_inner : X ^ 3 + X * binary ^ 3 = binary ^ 3 + binary ^ 6 := by
  have h4 : (4 : PowerSeries (ZMod 2)) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (C (R := ZMod 2)) (show (4 : ZMod 2) = 0 from rfl)
  rw [← binary_quadratic]
  ring_nf
  rw [h4]
  simp

private theorem binary_cubic_reversion : binary.subst (binary ^ 3 + binary ^ 6) = binary ^ 3 := by
  have hz : HasSubst (binary ^ 3) := .of_constantCoeff_zero
    (show constantCoeff (binary ^ 3) = 0 by simp [binary_zero])
  have hp : HasSubst (X + X ^ 2 : PowerSeries (ZMod 2)) := .of_constantCoeff_zero
    (show constantCoeff (X + X ^ 2 : PowerSeries (ZMod 2)) = 0 by simp)
  have h := congrArg (subst (binary ^ 3)) binary_left
  rw [subst_comp_subst_apply hp hz, subst_add hz, subst_pow hz, subst_X hz,
    ← pow_mul] at h
  exact h

private theorem binary_equation :
    binary * binary.subst (X ^ 3 + 3 * X * binary ^ 3) =
      binary.subst (X ^ 4 + 4 * X * binary ^ 4) := by
  have h3 : (3 : PowerSeries (ZMod 2)) = 1 := by
    simpa only [map_ofNat, map_one] using
      congrArg (C (R := ZMod 2)) (show (3 : ZMod 2) = 1 from rfl)
  have h4 : (4 : PowerSeries (ZMod 2)) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (C (R := ZMod 2)) (show (4 : ZMod 2) = 0 from rfl)
  rw [h3, h4, one_mul, zero_mul, zero_mul, add_zero, binary_cubic_inner,
    binary_cubic_reversion, fourth_subst]
  ring

private theorem binary_one : coeff 1 binary = 1 := by
  have h := congrArg (coeff 1) binary_quadratic
  have hz : coeff 1 (binary ^ 2) = 0 :=
    X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (X_dvd_iff.mpr binary_zero) 2) 1 (by omega)
  simpa [hz] using h

private theorem generating_mod_two :
    generatingSeries.map (Int.castRingHom (ZMod 2)) = binary := by
  let hom := Int.castRingHom (ZMod 2)
  let f := generatingSeries.map hom
  have hf : constantCoeff f = 0 := by
    simpa [f, ← coeff_zero_eq_constantCoeff, coeff_map] using
      congrArg hom generating_equation.1
  have hf1 : coeff 1 f = 1 := by
    simpa [f, coeff_map] using congrArg hom generating_equation.2.1
  have he := congrArg (PowerSeries.map hom) generating_equation.2.2
  have h3 : constantCoeff (X ^ 3 + 3 * X * generatingSeries ^ 3) = 0 := by simp
  have h4 : constantCoeff (X ^ 4 + 4 * X * generatingSeries ^ 4) = 0 := by simp
  have hs3 : PowerSeries.map hom (generatingSeries.subst (X ^ 3 + 3 * X * generatingSeries ^ 3)) =
      f.subst ((X ^ 3 + 3 * X * generatingSeries ^ 3).map hom) :=
    map_subst (.of_constantCoeff_zero h3) _
  have hs4 : PowerSeries.map hom (generatingSeries.subst (X ^ 4 + 4 * X * generatingSeries ^ 4)) =
      f.subst ((X ^ 4 + 4 * X * generatingSeries ^ 4).map hom) :=
    map_subst (.of_constantCoeff_zero h4) _
  rw [map_mul, hs3, hs4] at he
  simp only [map_add, map_mul, map_pow, map_ofNat, map_X] at he
  exact equation_unique hf binary_zero hf1 binary_one he binary_equation

private theorem binary_coefficient (n : ℕ) (hn : 1 ≤ n) :
    coeff n binary = 1 ↔ ∃ k, n = 2 ^ k := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h1 : n = 1
    · subst n
      exact ⟨fun _ => ⟨0, rfl⟩, fun _ => binary_one⟩
    have he := congrArg (coeff n) binary_quadratic
    rw [← square_subst, map_add, coeff_subst_X_pow (by decide : 2 ≠ 0)] at he
    simp only [Algebra.algebraMap_self, RingHom.id_apply, coeff_X, if_neg h1] at he
    by_cases hd : 2 ∣ n
    · rw [if_pos hd] at he
      have heq : coeff n binary = coeff (n / 2) binary := by
        exact (CharTwo.add_eq_zero).mp he
      rw [heq, ih (n / 2) (by omega) (by omega)]
      have hmul := Nat.mul_div_cancel' hd
      constructor
      · rintro ⟨k, hk⟩
        exact ⟨k + 1, by rw [pow_succ]; omega⟩
      · rintro ⟨k, hk⟩
        cases k with
        | zero => simp at hk; omega
        | succ k => exact ⟨k, by rw [pow_succ] at hk; omega⟩
    · rw [if_neg hd, add_zero] at he
      rw [he]
      constructor
      · intro h; exact (zero_ne_one h).elim
      · rintro ⟨k, hk⟩
        exfalso
        cases k with
        | zero => simp at hk; omega
        | succ k => exact hd ⟨2 ^ k, by rw [pow_succ] at hk; omega⟩

theorem hanna_conjecture (n : ℕ) (hn : 1 ≤ n) : Odd (a n) ↔ ∃ k, n = 2 ^ k := by
  have hc := congrArg (coeff n) generating_mod_two
  have hc' : (a n : ZMod 2) = coeff n binary := by
    simpa [coeff_map, generatingSeries] using hc
  rw [← ZMod.intCast_eq_one_iff_odd, hc']
  exact binary_coefficient n hn

#print axioms generating_equation
#print axioms generating_unique
#print axioms hanna_conjecture

end D5.S1.Recurrence.Invariants.QuarticCubicCatalanQuotientParity
