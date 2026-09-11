/- GID: D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/CatalanCompositionSquareParity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Catalan composition, degree contraction, and binary support prove Hanna parity. -/

import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.FieldTheory.Finite.Basic

open PowerSeries
open scoped BigOperators

namespace D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity

private noncomputable def catalanUnit : PowerSeries ℤ :=
  PowerSeries.catalanSeries.map (Nat.castRingHom ℤ)

noncomputable def catalanSeries : PowerSeries ℤ := X * catalanUnit

private theorem catalan_unit_zero : constantCoeff catalanUnit = 1 := by
  rw [← coeff_zero_eq_constantCoeff]
  simp [catalanUnit]

theorem catalan_equation : constantCoeff catalanSeries = 0 ∧
    coeff 1 catalanSeries = 1 ∧ catalanSeries = X + catalanSeries ^ 2 := by
  have hd := congrArg (PowerSeries.map (Nat.castRingHom ℤ))
    PowerSeries.catalanSeries_sq_mul_X_add_one
  have hd' : catalanUnit ^ 2 * X + 1 = catalanUnit := by
    simpa [catalanUnit] using hd
  refine ⟨by simp [catalanSeries], ?_, ?_⟩
  · simpa [catalanSeries, coeff_zero_eq_constantCoeff] using catalan_unit_zero
  · dsimp [catalanSeries]
    linear_combination -X * hd'

private def Agree {R : Type*} [CommRing R] (n : ℕ) (f g : PowerSeries R) : Prop :=
  ∀ i < n, coeff i f = coeff i g

private theorem agree_iff {R : Type*} [CommRing R] (n : ℕ) (f g : PowerSeries R) :
    Agree n f g ↔ (X : PowerSeries R) ^ n ∣ f - g := by
  simp [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]

private theorem agree_pow {R : Type*} [CommRing R] {n : ℕ} {f g : PowerSeries R}
    (h : Agree n f g) (k : ℕ) : Agree n (f ^ k) (g ^ k) :=
  (agree_iff _ _ _).mpr (((agree_iff _ _ _).mp h).trans (sub_dvd_pow_sub_pow f g k))

private theorem agree_mul_left {R : Type*} [CommRing R] {n : ℕ}
    {f g : PowerSeries R} (h : Agree n f g) (d : PowerSeries R) :
    Agree n (d * f) (d * g) := by
  apply (agree_iff _ _ _).mpr
  rw [← mul_sub]
  exact dvd_mul_of_dvd_right ((agree_iff _ _ _).mp h) d

private theorem coeff_pow_vanish {R : Type*} [CommRing R] {u : PowerSeries R}
    {r i k : ℕ} (hu : X ^ r ∣ u) (hi : i < r * k) : coeff i (u ^ k) = 0 := by
  apply X_pow_dvd_iff.mp _ i hi
  simpa only [← pow_mul] using pow_dvd_pow_of_dvd hu k

private theorem subst_constant {R : Type*} [CommRing R] (f u : PowerSeries R)
    (hu : constantCoeff u = 0) : constantCoeff (f.subst u) = constantCoeff f := by
  rw [← coeff_zero_eq_constantCoeff, coeff_subst' (.of_constantCoeff_zero hu)]
  rw [finsum_eq_single _ 0]
  · simp [coeff_zero_eq_constantCoeff]
  · intro k hk
    rw [coeff_pow_vanish (r := 1) (by simpa using X_dvd_iff.mpr hu) (by omega)]
    simp

-- The substitution argument has order at least two, so agreement gains a degree.
private noncomputable def argument (f : PowerSeries ℤ) : PowerSeries ℤ :=
  X ^ 2 * f * catalanUnit

private theorem argument_zero (f : PowerSeries ℤ) : constantCoeff (argument f) = 0 := by
  simp [argument]

private theorem argument_order (f : PowerSeries ℤ) : X ^ 2 ∣ argument f := by
  exact ⟨f * catalanUnit, by simp [argument, mul_assoc]⟩

private theorem argument_agree {n : ℕ} {f g : PowerSeries ℤ} (h : Agree n f g) :
    Agree (n + 2) (argument f) (argument g) := by
  apply (agree_iff _ _ _).mpr
  have hd := mul_dvd_mul_left (X ^ 2 : PowerSeries ℤ) ((agree_iff _ _ _).mp h)
  have hd' := dvd_mul_of_dvd_left hd catalanUnit
  convert hd' using 1
  · simp [pow_add, mul_comm]
  · dsimp [argument]; ring

private noncomputable def step (f : PowerSeries ℤ) : PowerSeries ℤ :=
  catalanUnit * f.subst (argument f)

private theorem step_constant (f : PowerSeries ℤ) : constantCoeff (step f) = constantCoeff f := by
  simp only [step, map_mul, catalan_unit_zero, subst_constant _ _ (argument_zero f), one_mul]

private theorem step_agree {n : ℕ} (hn : 1 ≤ n) {f g : PowerSeries ℤ}
    (h : Agree n f g) : Agree (n + 1) (step f) (step g) := by
  apply agree_mul_left (d := catalanUnit)
  intro i hi
  rw [coeff_subst' (.of_constantCoeff_zero (argument_zero f)),
    coeff_subst' (.of_constantCoeff_zero (argument_zero g))]
  apply finsum_congr
  intro k
  by_cases hk : k < n
  · rw [h k hk, agree_pow (argument_agree h) k i (by omega)]
  · rw [coeff_pow_vanish (argument_order f) (by omega : i < 2 * k),
      coeff_pow_vanish (argument_order g) (by omega : i < 2 * k), smul_zero, smul_zero]

private noncomputable def approximation : ℕ → PowerSeries ℤ
  | 0 => 1
  | n + 1 => step (approximation n)

private theorem approximation_constant (n : ℕ) : constantCoeff (approximation n) = 1 := by
  induction n with
  | zero => simp [approximation]
  | succ n ih => simpa only [approximation, step_constant] using ih

private theorem approximation_stable {n m : ℕ} (h : n ≤ m) :
    Agree (n + 1) (approximation n) (approximation m) := by
  induction n generalizing m with
  | zero =>
    intro i hi
    have : i = 0 := by omega
    subst i
    simp [coeff_zero_eq_constantCoeff, approximation_constant]
  | succ n ih =>
    cases m with
    | zero => omega
    | succ m => exact step_agree (by omega) (ih (by omega))

private noncomputable def limitUnit : PowerSeries ℤ :=
  mk (fun n => coeff n (approximation n))

private theorem limit_agree (n : ℕ) : Agree (n + 1) limitUnit (approximation n) := by
  intro i hi
  simpa only [limitUnit, coeff_mk] using
    approximation_stable (by omega : i ≤ n) i (by omega)

private theorem limit_constant : constantCoeff limitUnit = 1 := by
  rw [← coeff_zero_eq_constantCoeff, limit_agree 0 0 (by omega),
    coeff_zero_eq_constantCoeff, approximation_constant]

private theorem limit_fixed : limitUnit = step limitUnit := by
  ext i
  exact (limit_agree (i + 1) i (by omega)).trans
    (step_agree (by omega : 1 ≤ i + 1) (limit_agree i) i (by omega)).symm

noncomputable def generatingSeries : PowerSeries ℤ := X * limitUnit

noncomputable def a (n : ℕ) : ℤ := coeff n generatingSeries

theorem generating_equation : constantCoeff generatingSeries = 0 ∧
    coeff 1 generatingSeries = 1 ∧
    generatingSeries ^ 2 = generatingSeries.subst (generatingSeries * catalanSeries) := by
  refine ⟨by simp [generatingSeries], ?_, ?_⟩
  · simpa [generatingSeries, coeff_zero_eq_constantCoeff] using limit_constant
  · have ha : generatingSeries * catalanSeries = argument limitUnit := by
      simp [generatingSeries, catalanSeries, argument]; ring
    rw [ha, generatingSeries, subst_mul (.of_constantCoeff_zero (argument_zero _)),
      subst_X (.of_constantCoeff_zero (argument_zero _))]
    have hf := limit_fixed
    dsimp [step, argument] at *
    linear_combination X ^ 2 * limitUnit * hf

private theorem quadratic_unique {R : Type*} [CommRing R] {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (ef : f = X + f ^ 2) (eg : g = X + g ^ 2) : f = g := by
  have hu : IsUnit (1 - f - g) := by
    rw [isUnit_iff_constantCoeff]
    simp [hf, hg]
  have he : (1 - f - g) * (f - g) = (1 - f - g) * 0 := by
    linear_combination ef - eg
  exact sub_eq_zero.mp (hu.mul_left_cancel he)

theorem catalan_unique (f : PowerSeries ℤ) (h0 : constantCoeff f = 0)
    (hf : f = X + f ^ 2) : f = catalanSeries :=
  quadratic_unique h0 catalan_equation.1 hf catalan_equation.2.2

private theorem fixed_unique {f g : PowerSeries ℤ}
    (hf : constantCoeff f = 1) (hg : constantCoeff g = 1)
    (ef : f = step f) (eg : g = step g) : f = g := by
  have h : ∀ n, Agree (n + 1) f g := by
    intro n
    induction n with
    | zero =>
      intro i hi
      have : i = 0 := by omega
      subst i
      simp [coeff_zero_eq_constantCoeff, hf, hg]
    | succ n ih => simpa only [← ef, ← eg] using step_agree (by omega) ih
  ext i
  exact h i i (by omega)

theorem generating_unique (f : PowerSeries ℤ) (h0 : constantCoeff f = 0)
    (h1 : coeff 1 f = 1)
    (hf : f ^ 2 = f.subst (f * catalanSeries)) : f = generatingSeries := by
  obtain ⟨b, rfl⟩ := X_dvd_iff.mpr h0
  have hb : constantCoeff b = 1 := by simpa using h1
  have hu : IsUnit b := isUnit_iff_constantCoeff.mpr (hb ▸ isUnit_one)
  have ha : X * b * catalanSeries = argument b := by
    simp [catalanSeries, argument]; ring
  rw [ha, subst_mul (.of_constantCoeff_zero (argument_zero b)),
    subst_X (.of_constantCoeff_zero (argument_zero b))] at hf
  have he : X ^ 2 * (b * b) = X ^ 2 * (b * step b) := by
    dsimp [step, argument] at *
    linear_combination hf
  have hbfix : b = step b := hu.mul_left_cancel (X_pow_mul_cancel he)
  rw [fixed_unique hb limit_constant hbfix limit_fixed]
  rfl

private theorem square_subst (f : PowerSeries (ZMod 2)) : f ^ 2 = f.subst (X ^ 2) := by
  have he := MvPowerSeries.map_frobenius_expand (f := f) 2 (by decide)
  rw [ZMod.frobenius_zmod, MvPowerSeries.map_id] at he
  exact he.symm.trans (PowerSeries.expand_apply 2 (by decide) f)

private theorem outer_cancel {f u v : PowerSeries (ZMod 2)}
    (hf : constantCoeff f = 0) (hf1 : coeff 1 f = 1)
    (hu : constantCoeff u = 0) (hv : constantCoeff v = 0)
    (he : f.subst u = f.subst v) : u = v := by
  have hunit : IsUnit (coeff 1 f) := hf1 ▸ isUnit_one
  let inverse := f.substInvOfIsUnit hunit
  have hi : inverse.subst f = X := subst_substInvOfIsUnit_left f hf hunit
  have h := congrArg (fun s => inverse.subst s) he
  rw [← subst_comp_subst_apply (.of_constantCoeff_zero hf) (.of_constantCoeff_zero hu),
    ← subst_comp_subst_apply (.of_constantCoeff_zero hf) (.of_constantCoeff_zero hv),
    hi, subst_X (.of_constantCoeff_zero hu), subst_X (.of_constantCoeff_zero hv)] at h
  exact h

private noncomputable def reducedCatalan : PowerSeries (ZMod 2) :=
  catalanSeries.map (Int.castRingHom (ZMod 2))

private theorem reduced_catalan_spec : constantCoeff reducedCatalan = 0 ∧
    coeff 1 reducedCatalan = 1 ∧ reducedCatalan = X + reducedCatalan ^ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff]
    simp only [reducedCatalan, coeff_map, coeff_zero_eq_constantCoeff, catalan_equation.1,
      map_zero]
  · simp only [reducedCatalan, coeff_map, catalan_equation.2.1, map_one]
  · simpa [reducedCatalan] using congrArg
      (PowerSeries.map (Int.castRingHom (ZMod 2))) catalan_equation.2.2

private theorem mod_two_identity : generatingSeries.map (Int.castRingHom (ZMod 2)) =
    X * (1 + reducedCatalan) := by
  let hom := Int.castRingHom (ZMod 2)
  let f := generatingSeries.map hom
  have hf0 : constantCoeff f = 0 := by
    rw [← coeff_zero_eq_constantCoeff]
    simp [f, coeff_map, coeff_zero_eq_constantCoeff, generating_equation.1]
  have hf1 : coeff 1 f = 1 := by
    simp [f, coeff_map, generating_equation.2.1]
  have he : f ^ 2 = f.subst (f * reducedCatalan) := by
    have hs : constantCoeff (generatingSeries * catalanSeries) = 0 := by
      simp [generating_equation.1]
    calc
      f ^ 2 = (generatingSeries ^ 2).map hom := (map_pow _ _ _).symm
      _ = (generatingSeries.subst (generatingSeries * catalanSeries)).map hom :=
        congrArg (PowerSeries.map hom) generating_equation.2.2
      _ = (generatingSeries.map hom).subst
          ((generatingSeries * catalanSeries).map hom) :=
        map_subst (.of_constantCoeff_zero hs) generatingSeries
      _ = f.subst (f * reducedCatalan) := by simp [f, reducedCatalan, hom]
  rw [square_subst] at he
  have hprod : f * reducedCatalan = X ^ 2 := (outer_cancel hf0 hf1
    (by simp) (by simp [hf0]) he).symm
  have hc : reducedCatalan * (1 + reducedCatalan) = X := by
    have h := reduced_catalan_spec.2.2
    have hz : (2 : PowerSeries (ZMod 2)) = 0 := by
      simpa only [map_ofNat, map_zero] using
        congrArg (C (R := ZMod 2)) (show (2 : ZMod 2) = 0 by decide)
    linear_combination h + reducedCatalan ^ 2 * hz
  have heq : f * reducedCatalan = X * (1 + reducedCatalan) * reducedCatalan := by
    rw [hprod]
    calc
      X ^ 2 = X * (reducedCatalan * (1 + reducedCatalan)) := by rw [hc]; ring
      _ = X * (1 + reducedCatalan) * reducedCatalan := by ring
  obtain ⟨d, hd⟩ := X_dvd_iff.mpr reduced_catalan_spec.1
  have hd0 : constantCoeff d = 1 := by
    have h := reduced_catalan_spec.2.1
    simpa [hd] using h
  have hdu : IsUnit d := isUnit_iff_constantCoeff.mpr (hd0 ▸ isUnit_one)
  apply hdu.mul_right_cancel
  apply mul_X_cancel
  simpa only [hd, mul_assoc, mul_comm X d] using heq

private theorem binary_support (n : ℕ) :
    coeff n reducedCatalan = 1 ↔ ∃ k : ℕ, n = 2 ^ k := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n
      rw [coeff_zero_eq_constantCoeff, reduced_catalan_spec.1]
      exact iff_of_false zero_ne_one (by
        rintro ⟨k, hk⟩
        exact (pow_ne_zero k (by decide : (2 : ℕ) ≠ 0)) hk.symm)
    by_cases hn1 : n = 1
    · subst n
      exact iff_of_true reduced_catalan_spec.2.1 ⟨0, rfl⟩
    have hn : 1 < n := by omega
    have hc := congrArg (coeff n) reduced_catalan_spec.2.2
    rw [square_subst, map_add, coeff_subst_X_pow (by decide : 2 ≠ 0)] at hc
    simp only [coeff_X, if_neg hn1, zero_add, Algebra.algebraMap_self, RingHom.id_apply] at hc
    by_cases heven : 2 ∣ n
    · rw [if_pos heven] at hc
      rw [hc, ih (n / 2) (by omega)]
      constructor
      · rintro ⟨k, hk⟩
        refine ⟨k + 1, ?_⟩
        have hd := Nat.mod_eq_zero_of_dvd heven
        rw [pow_succ]
        omega
      · rintro ⟨k, hk⟩
        cases k with
        | zero => simp at hk; omega
        | succ k =>
          refine ⟨k, ?_⟩
          rw [pow_succ] at hk
          omega
    · rw [if_neg heven] at hc
      rw [hc]
      exact iff_of_false zero_ne_one (by
        rintro ⟨k, hk⟩
        cases k with
        | zero => simp at hk; omega
        | succ k =>
          apply heven
          rw [hk, pow_succ]
          exact dvd_mul_left 2 (2 ^ k))

theorem binary_catalan (n : ℕ) :
    coeff n (catalanSeries.map (Int.castRingHom (ZMod 2))) = 1 ↔
      ∃ k : ℕ, n = 2 ^ k := binary_support n

theorem hanna_conjecture (n : ℕ) (hn : 1 < n) :
    Odd (a n) ↔ ∃ k : ℕ, n = 2 ^ k + 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [← ZMod.intCast_eq_one_iff_odd]
  have he := congrArg (coeff (m + 1)) mod_two_identity
  simp only [coeff_map, coeff_succ_X_mul, map_add, coeff_one,
    if_neg (by omega : m ≠ 0), zero_add] at he
  change (a (m + 1) : ZMod 2) = coeff m reducedCatalan at he
  rw [he]
  change coeff m (catalanSeries.map (Int.castRingHom (ZMod 2))) = 1 ↔ _
  rw [binary_catalan]
  simp only [Nat.succ_eq_add_one, Nat.add_right_cancel_iff]

#print axioms catalan_equation
#print axioms catalan_unique
#print axioms generating_equation
#print axioms generating_unique
#print axioms binary_catalan
#print axioms hanna_conjecture

end D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity
