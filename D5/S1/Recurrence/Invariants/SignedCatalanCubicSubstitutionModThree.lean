/- GID: D5/S1/Recurrence/Invariants/SignedCatalanCubicSubstitutionModThree
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/SignedCatalanCubicSubstitutionModThree
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Integral reversion and ternary digit support prove Hanna's A386666 congruence. -/

import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.FieldTheory.Finite.Basic

open PowerSeries

namespace D5.S1.Recurrence.Invariants.SignedCatalanCubicSubstitutionModThree

private theorem prime_power_subst (p : ℕ) [Fact p.Prime]
    (f : PowerSeries (ZMod p)) : f ^ p = f.subst (X ^ p) := by
  have h := MvPowerSeries.map_frobenius_expand (σ := Unit) (R := ZMod p)
    p (NeZero.ne p) (f := f)
  rw [ZMod.frobenius_zmod, MvPowerSeries.map_id] at h
  exact h.symm.trans (PowerSeries.expand_apply p (NeZero.ne p) f)

private def Agree {R : Type*} [CommRing R] (d : ℕ) (f g : PowerSeries R) : Prop :=
  ∀ n < d, coeff n f = coeff n g

private theorem agree_iff {R : Type*} [CommRing R] (d : ℕ) (f g : PowerSeries R) :
    Agree d f g ↔ (X : PowerSeries R) ^ d ∣ f - g := by
  simp [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]

private theorem square_linear {R : Type*} [CommRing R] {d : ℕ}
    {f g : PowerSeries R} (hf : constantCoeff f = 1) (hg : constantCoeff g = 1)
    (h : Agree d f g) (n : ℕ) (hn : n < d + 1) :
    coeff n (f ^ 2) - coeff n (g ^ 2) = 2 * (coeff n f - coeff n g) := by
  have hz : (X : PowerSeries R) ∣ f + g - C 2 := by
    apply X_dvd_iff.mpr
    simp [hf, hg]
    ring
  have hd := mul_dvd_mul ((agree_iff _ _ _).mp h) hz
  rw [← pow_succ] at hd
  have he : (f - g) * (f + g - C 2) = f ^ 2 - g ^ 2 - C 2 * (f - g) := by ring
  rw [he] at hd
  have hc := X_pow_dvd_iff.mp hd n hn
  simpa only [map_sub, coeff_C_mul, sub_eq_zero] using hc

private theorem subst_two_agree {R : Type*} [CommRing R] {d : ℕ}
    (hd : 1 ≤ d) {f g : PowerSeries R} (h : Agree d f g) :
    Agree (d + 1) (f.subst ((X : PowerSeries R) ^ 2)) (g.subst ((X : PowerSeries R) ^ 2)) := by
  intro n hn
  simp only [coeff_subst_X_pow (by decide : 2 ≠ 0), Algebra.algebraMap_self,
    RingHom.id_apply]
  split_ifs
  · exact h (n / 2) (by omega)
  · rfl

private theorem normalized_unique {R : Type*} [CommRing R] [NoZeroDivisors R]
    (h2 : (2 : R) ≠ 0) {f g : PowerSeries R}
    (hf : constantCoeff f = 1) (hg : constantCoeff g = 1)
    (he : f.subst (X ^ 2) - f ^ 2 = g.subst (X ^ 2) - g ^ 2) : f = g := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n; simpa only [coeff_zero_eq_constantCoeff] using hf.trans hg.symm
    have hs := subst_two_agree (by omega : 1 ≤ n) ih n (by omega)
    have hl := square_linear hf hg ih n (by omega)
    have hc := congrArg (coeff n) he
    simp only [map_sub] at hc
    rw [hs] at hc
    have hz : 2 * (coeff n f - coeff n g) = 0 := by linear_combination -hc - hl
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left h2)

private noncomputable def residual (f : PowerSeries ℤ) : PowerSeries ℤ :=
  f.subst (X ^ 2) - f ^ 2 - 4 * X

-- Frobenius makes division by two exact before any coefficients are chosen.
private theorem residual_even (f : PowerSeries ℤ) (n : ℕ) :
    (2 : ℤ) ∣ coeff n (residual f) := by
  let hom := Int.castRingHom (ZMod 2)
  have hm : (residual f).map hom = 0 := by
    have h4 : (4 : PowerSeries (ZMod 2)) = 0 := by
      rw [← map_ofNat C 4, show (4 : ZMod 2) = 0 from rfl, map_zero]
    simp only [residual, map_sub, map_pow, map_mul, map_ofNat, map_X]
    rw [show PowerSeries.map hom (f.subst ((X : PowerSeries ℤ) ^ 2)) =
      (f.map hom).subst ((X : PowerSeries (ZMod 2)) ^ 2) by
        have he : PowerSeries.map hom (f.subst ((X : PowerSeries ℤ) ^ 2)) =
            (PowerSeries.map hom f).subst (PowerSeries.map hom ((X : PowerSeries ℤ) ^ 2)) :=
          map_subst (.of_constantCoeff_zero
            (by simp : constantCoeff ((X : PowerSeries ℤ) ^ 2) = 0)) f
        simpa only [map_pow, map_X] using he]
    simp only [← prime_power_subst, h4, zero_mul, sub_self]
  have hc := congrArg (coeff n) hm
  change ((coeff n (residual f) : ℤ) : ZMod 2) = 0 at hc
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc

private noncomputable def step (f : PowerSeries ℤ) : PowerSeries ℤ :=
  f + mk (fun n => coeff n (residual f) / 2)

private theorem step_coeff (f : PowerSeries ℤ) (n : ℕ) :
    2 * coeff n (step f) = 2 * coeff n f + coeff n (residual f) := by
  simp only [step, map_add, coeff_mk, mul_add]
  rw [Int.mul_ediv_cancel' (residual_even f n)]

private theorem step_one {f : PowerSeries ℤ} (hf : constantCoeff f = 1) :
    constantCoeff (step f) = 1 := by
  simp [step, residual, coeff_zero_eq_constantCoeff, hf]

private theorem step_agree {d : ℕ} (hd : 1 ≤ d) {f g : PowerSeries ℤ}
    (hf : constantCoeff f = 1) (hg : constantCoeff g = 1) (h : Agree d f g) :
    Agree (d + 1) (step f) (step g) := by
  intro n hn
  have hs := subst_two_agree hd h n hn
  have hl := square_linear hf hg h n hn
  have hc := step_coeff f n
  have hc' := step_coeff g n
  simp only [residual, map_sub] at hc hc'
  omega

private noncomputable def approximation : ℕ → PowerSeries ℤ
  | 0 => 1
  | n + 1 => step (approximation n)

private theorem approximation_one (n : ℕ) : constantCoeff (approximation n) = 1 := by
  induction n with
  | zero => simp [approximation]
  | succ n ih => exact step_one ih

private theorem approximation_stable {d e : ℕ} (h : d ≤ e) :
    Agree (d + 1) (approximation d) (approximation e) := by
  induction d generalizing e with
  | zero =>
    intro n hn
    have hn0 : n = 0 := by omega
    subst n
    simpa only [coeff_zero_eq_constantCoeff] using
      (approximation_one 0).trans (approximation_one e).symm
  | succ d ih =>
    cases e with
    | zero => omega
    | succ e =>
      exact step_agree (by omega) (approximation_one d)
        (approximation_one e) (ih (by omega))

private noncomputable def normalizedSeries : PowerSeries ℤ :=
  mk fun n => coeff n (approximation n)

private theorem normalized_agree (d : ℕ) :
    Agree (d + 1) normalizedSeries (approximation d) := by
  intro n hn
  simp only [normalizedSeries, coeff_mk]
  exact approximation_stable (by omega : n ≤ d) n (by omega)

private theorem normalized_one : constantCoeff normalizedSeries = 1 := by
  have h := normalized_agree 0 0 (by omega)
  simpa only [coeff_zero_eq_constantCoeff, approximation_one] using h

private theorem normalized_equation :
    normalizedSeries.subst (X ^ 2) = normalizedSeries ^ 2 + 4 * X := by
  have hf : normalizedSeries = step normalizedSeries := by
    ext n
    have hg := normalized_agree (n + 1) n (by omega)
    have hs := step_agree (by omega : 1 ≤ n + 1) normalized_one (approximation_one n)
      (normalized_agree n) n (by omega)
    exact hg.trans hs.symm
  ext n
  have hc := step_coeff normalizedSeries n
  rw [← hf] at hc
  simp only [residual, map_sub, map_add] at hc ⊢
  omega

private theorem inverse_exists {R : Type*} [CommRing R] (f : PowerSeries R)
    (hf : constantCoeff f = 0) (hf1 : coeff 1 f = 1) :
    ∃ b : PowerSeries R, constantCoeff b = 0 ∧ coeff 1 b = 1 ∧
      f.subst b = X ∧ b.subst f = X := by
  have hu : IsUnit (coeff 1 f) := hf1.symm ▸ isUnit_one
  refine ⟨f.substInvOfIsUnit hu, by simp, ?_,
    subst_substInvOfIsUnit_right f hf hu, subst_substInvOfIsUnit_left f hf hu⟩
  rw [coeff_one_substInvOfIsUnit]
  have he : hu.unit = 1 := Units.ext (hu.unit_spec.trans hf1)
  simp [he]

private theorem subst_four {R : Type*} [CommRing R] (f : PowerSeries R) :
    (4 : PowerSeries R).subst f = (4 : PowerSeries R) := by
  simpa only [map_ofNat] using (subst_C (a := f) (4 : R))

-- Reversion turns the nonlinear inner argument into substitution by X squared.
private theorem inverse_equation {R : Type*} [CommRing R] {f b : PowerSeries R}
    (hf : constantCoeff f = 0) (hb : constantCoeff b = 0)
    (hfb : f.subst b = X) (hbf : b.subst f = X) :
    (b.subst ((X : PowerSeries R) ^ 2) = b ^ 2 + 4 * X ^ 3) ↔
      f ^ 2 = f.subst (X ^ 2 + 4 * f ^ 3) := by
  have sf : HasSubst f := .of_constantCoeff_zero hf
  have sb : HasSubst b := .of_constantCoeff_zero hb
  have sx : HasSubst ((X : PowerSeries R) ^ 2) := .of_constantCoeff_zero
    (by simp : constantCoeff ((X : PowerSeries R) ^ 2) = 0)
  have sf2 : HasSubst (f ^ 2) := .of_constantCoeff_zero
    (by simp [hf] : constantCoeff (f ^ 2) = 0)
  have si : HasSubst (X ^ 2 + 4 * f ^ 3) := .of_constantCoeff_zero
    (by simp [hf] : constantCoeff (X ^ 2 + 4 * f ^ 3) = 0)
  constructor
  · intro he
    have hs := congrArg (fun g : PowerSeries R => g.subst f) he
    rw [subst_comp_subst_apply sx sf, subst_pow sf, subst_X sf,
      subst_add sf, subst_pow sf, hbf, subst_mul sf, subst_four,
      subst_pow sf, subst_X sf] at hs
    have ht := congrArg (fun g : PowerSeries R => f.subst g) hs
    rw [← subst_comp_subst_apply sb sf2, hfb, subst_X sf2] at ht
    exact ht
  · intro he
    have hs := congrArg (fun g : PowerSeries R => b.subst g) he
    rw [← subst_comp_subst_apply sf si, hbf, subst_X si] at hs
    have ht := congrArg (fun g : PowerSeries R => g.subst b) hs
    rw [subst_comp_subst_apply sf2 sb, subst_pow sb, hfb,
      subst_add sb, subst_pow sb, subst_X sb, subst_mul sb, subst_four,
      subst_pow sb, hfb] at ht
    exact ht

private theorem inverse_normalized {R : Type*} [CommRing R] {b : PowerSeries R}
    (hb : constantCoeff b = 0) (hb1 : coeff 1 b = 1)
    (he : b.subst ((X : PowerSeries R) ^ 2) = b ^ 2 + 4 * X ^ 3) :
    ∃ h : PowerSeries R, b = X * h ∧ constantCoeff h = 1 ∧
      h.subst ((X : PowerSeries R) ^ 2) = h ^ 2 + 4 * X := by
  obtain ⟨h, rfl⟩ := X_dvd_iff.mpr hb
  refine ⟨h, rfl, by simpa using hb1, ?_⟩
  have sx : HasSubst ((X : PowerSeries R) ^ 2) := .of_constantCoeff_zero
    (by simp : constantCoeff ((X : PowerSeries R) ^ 2) = 0)
  rw [subst_mul sx, subst_X sx] at he
  apply X_pow_mul_injective (k := 2)
  calc
    X ^ 2 * h.subst (X ^ 2) = (X * h) ^ 2 + 4 * X ^ 3 := he
    _ = X ^ 2 * (h ^ 2 + 4 * X) := by ring

private theorem exists_series : ∃ f : PowerSeries ℤ,
    constantCoeff f = 0 ∧ coeff 1 f = 1 ∧
    f ^ 2 = f.subst (X ^ 2 + 4 * f ^ 3) := by
  let b : PowerSeries ℤ := X * normalizedSeries
  have hb : constantCoeff b = 0 := by simp [b]
  have hb1 : coeff 1 b = 1 := by simpa [b] using normalized_one
  have he : b.subst ((X : PowerSeries ℤ) ^ 2) = b ^ 2 + 4 * X ^ 3 := by
    have sx : HasSubst ((X : PowerSeries ℤ) ^ 2) := .of_constantCoeff_zero
      (by simp : constantCoeff ((X : PowerSeries ℤ) ^ 2) = 0)
    simp only [b, subst_mul sx, subst_X sx, normalized_equation]
    ring
  obtain ⟨f, hf, hf1, hbf, hfb⟩ := inverse_exists b hb hb1
  exact ⟨f, hf, hf1, (inverse_equation hf hb hfb hbf).mp he⟩

noncomputable def generatingSeries : PowerSeries ℤ := Classical.choose exists_series

noncomputable def a (n : ℕ) : ℤ := coeff n generatingSeries

theorem generating_equation : constantCoeff generatingSeries = 0 ∧
    coeff 1 generatingSeries = 1 ∧
    generatingSeries ^ 2 = generatingSeries.subst (X ^ 2 + 4 * generatingSeries ^ 3) :=
  Classical.choose_spec exists_series

private theorem solution_unique {R : Type*} [CommRing R] [NoZeroDivisors R]
    (h2 : (2 : R) ≠ 0) {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (hf1 : coeff 1 f = 1) (hg1 : coeff 1 g = 1)
    (he : f ^ 2 = f.subst (X ^ 2 + 4 * f ^ 3))
    (he' : g ^ 2 = g.subst (X ^ 2 + 4 * g ^ 3)) : f = g := by
  obtain ⟨b, hb, hb1, hfb, hbf⟩ := inverse_exists f hf hf1
  obtain ⟨c, hc, hc1, hgc, hcg⟩ := inverse_exists g hg hg1
  obtain ⟨h, hbh, hh, hhe⟩ := inverse_normalized hb hb1
    ((inverse_equation hf hb hfb hbf).mpr he)
  obtain ⟨k, hck, hk, hke⟩ := inverse_normalized hc hc1
    ((inverse_equation hg hc hgc hcg).mpr he')
  have hhk : h = k := normalized_unique h2 hh hk (by rw [hhe, hke]; ring)
  have hbc : b = c := by rw [hbh, hck, hhk]
  rw [← hbc] at hgc
  have hs := congrArg (fun t : PowerSeries R => t.subst f) (hfb.trans hgc.symm)
  rw [subst_comp_subst_apply (.of_constantCoeff_zero hb) (.of_constantCoeff_zero hf),
    subst_comp_subst_apply (.of_constantCoeff_zero hb) (.of_constantCoeff_zero hf),
    hbf, X_subst, X_subst] at hs
  exact hs

theorem generating_unique (f : PowerSeries ℤ)
    (hf : constantCoeff f = 0) (hf1 : coeff 1 f = 1)
    (he : f ^ 2 = f.subst (X ^ 2 + 4 * f ^ 3)) : f = generatingSeries :=
  solution_unique (by decide) hf generating_equation.1 hf1 generating_equation.2.1
    he generating_equation.2.2

def distinctPowersOfThree (n : ℕ) : ℕ :=
  if (Nat.digits 3 n).all (· != 2) then 1 else 0

private theorem partitions_zero : distinctPowersOfThree 0 = 1 := by
  simp [distinctPowersOfThree]

private theorem partitions_three (n : ℕ) :
    distinctPowersOfThree (3 * n) = distinctPowersOfThree n := by
  by_cases hn : n = 0
  · simp [hn]
  · simp [distinctPowersOfThree, Nat.digits_base_mul (by decide : 1 < 3) (by omega : 0 < n)]

private theorem partitions_three_one (n : ℕ) :
    distinctPowersOfThree (3 * n + 1) = distinctPowersOfThree n := by
  rw [distinctPowersOfThree, Nat.digits_def' (by decide : 1 < 3) (by omega)]
  simp [Nat.add_div, distinctPowersOfThree]

private theorem partitions_three_two (n : ℕ) :
    distinctPowersOfThree (3 * n + 2) = 0 := by
  rw [distinctPowersOfThree, Nat.digits_def' (by decide : 1 < 3) (by omega)]
  simp

private noncomputable def digitSeries : PowerSeries (ZMod 3) :=
  mk fun n => (distinctPowersOfThree n : ZMod 3)

private theorem digit_zero : constantCoeff digitSeries = 1 := by
  simp [digitSeries, partitions_zero]

private theorem digit_self_similarity :
    digitSeries = (1 + X) * digitSeries.subst ((X : PowerSeries (ZMod 3)) ^ 3) := by
  ext n
  rw [add_mul, one_mul, map_add]
  cases n with
  | zero => simp [coeff_zero_eq_constantCoeff, digit_zero]
  | succ n =>
    rw [coeff_succ_X_mul]
    simp only [coeff_subst_X_pow (by decide : 3 ≠ 0), Algebra.algebraMap_self,
      RingHom.id_apply, digitSeries, coeff_mk]
    have hr : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases hr with hr | hr | hr
    · have he : n = 3 * (n / 3) := by omega
      rw [he]
      simp [partitions_three_one, show ¬ 3 ∣ 3 * (n / 3) + 1 by omega]
    · have he : n = 3 * (n / 3) + 1 := by omega
      rw [he]
      simp [show 3 * (n / 3) + 1 + 1 = 3 * (n / 3) + 2 by omega,
        partitions_three_two, show ¬ 3 ∣ 3 * (n / 3) + 1 by omega,
        show ¬ 3 ∣ 3 * (n / 3) + 2 by omega]
    · have he : n + 1 = 3 * (n / 3 + 1) := by omega
      rw [he, partitions_three]
      simp [show ¬ 3 ∣ n by omega]

private theorem digit_square : (1 + X) * digitSeries ^ 2 = 1 := by
  have hu : IsUnit digitSeries := isUnit_iff_constantCoeff.mpr (digit_zero ▸ isUnit_one)
  apply hu.mul_left_cancel
  calc
    digitSeries * ((1 + X) * digitSeries ^ 2) = (1 + X) * digitSeries ^ 3 := by ring
    _ = digitSeries := by rw [prime_power_subst]; exact digit_self_similarity.symm
    _ = digitSeries * 1 := (mul_one _).symm

noncomputable def signedCatalanSeries : PowerSeries (ZMod 3) :=
  1 - (1 + X) * digitSeries

private theorem signed_zero : constantCoeff signedCatalanSeries = 0 := by
  simp [signedCatalanSeries, digit_zero]

private theorem signed_quadratic : signedCatalanSeries + signedCatalanSeries ^ 2 = X := by
  have h3 : (3 : PowerSeries (ZMod 3)) = 0 := by
    rw [← map_ofNat C 3, show (3 : ZMod 3) = 0 from rfl, map_zero]
  dsimp [signedCatalanSeries]
  linear_combination (1 + X) * digit_square + (1 - (1 + X) * digitSeries) * h3

private theorem signed_one : coeff 1 signedCatalanSeries = 1 := by
  have h := congrArg (coeff 1) signed_quadratic
  simpa [pow_two, coeff_one_mul, signed_zero] using h

private theorem quadratic_unique {R : Type*} [CommRing R] {u v : PowerSeries R}
    (hu : constantCoeff u = 0) (hv : constantCoeff v = 0)
    (he : u + u ^ 2 = v + v ^ 2) : u = v := by
  have hunit : IsUnit (1 + u + v) := isUnit_iff_constantCoeff.mpr (by simp [hu, hv])
  apply sub_eq_zero.mp
  apply hunit.mul_right_cancel
  linear_combination he

private theorem signed_substitution : signedCatalanSeries ^ 2 =
    signedCatalanSeries.subst (X ^ 2 + signedCatalanSeries ^ 3) := by
  let t : PowerSeries (ZMod 3) := X ^ 2 + signedCatalanSeries ^ 3
  have ht : constantCoeff t = 0 := by simp [t, signed_zero]
  have st : HasSubst t := .of_constantCoeff_zero ht
  have h3 : (3 : PowerSeries (ZMod 3)) = 0 := by
    rw [← map_ofNat C 3, show (3 : ZMod 3) = 0 from rfl, map_zero]
  have hp : signedCatalanSeries ^ 2 + (signedCatalanSeries ^ 2) ^ 2 = t := by
    dsimp [t]
    linear_combination (X + signedCatalanSeries + signedCatalanSeries ^ 2) *
      signed_quadratic - signedCatalanSeries ^ 3 * h3
  have hs := congrArg (fun f : PowerSeries (ZMod 3) => f.subst t) signed_quadratic
  rw [subst_add st, subst_pow st, subst_X st] at hs
  exact quadratic_unique (by simp [signed_zero])
    (constantCoeff_subst_eq_zero ht _ signed_zero) (hp.trans hs.symm)

private theorem signed_coeff_succ (n : ℕ) :
    coeff (n + 1) signedCatalanSeries =
      -(distinctPowersOfThree (n + 1) : ZMod 3) - distinctPowersOfThree n := by
  simp [signedCatalanSeries, add_mul, digitSeries]
  ring

private theorem negative_two (z : ZMod 3) : -z = 2 * z := by
  calc
    -z = (-1) * z := by ring
    _ = 2 * z := by rw [show (-1 : ZMod 3) = 2 from rfl]

private theorem signed_residues (n : ℕ) (hn : 0 < n) :
    coeff (3 * n) signedCatalanSeries = 2 * (distinctPowersOfThree n : ZMod 3) ∧
    coeff (3 * n + 1) signedCatalanSeries = (distinctPowersOfThree n : ZMod 3) ∧
    coeff (3 * n + 2) signedCatalanSeries = 2 * (distinctPowersOfThree n : ZMod 3) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [show 3 * (k + 1) = (3 * k + 2) + 1 by omega, signed_coeff_succ,
      show 3 * k + 2 + 1 = 3 * (k + 1) by omega,
      partitions_three, partitions_three_two, Nat.cast_zero, sub_zero, negative_two]
  · rw [signed_coeff_succ, partitions_three_one, partitions_three]
    have h3 : (3 : ZMod 3) = 0 := rfl
    linear_combination -(distinctPowersOfThree n : ZMod 3) * h3
  · rw [show 3 * n + 2 = (3 * n + 1) + 1 by omega, signed_coeff_succ,
      show 3 * n + 1 + 1 = 3 * n + 2 by omega,
      partitions_three_two, partitions_three_one, Nat.cast_zero, neg_zero, zero_sub, negative_two]

theorem signed_catalan_mod_three (n : ℕ) (hn : 0 < n) :
    constantCoeff signedCatalanSeries = 0 ∧ coeff 1 signedCatalanSeries = 1 ∧
    signedCatalanSeries + signedCatalanSeries ^ 2 = X ∧
    signedCatalanSeries ^ 2 = signedCatalanSeries.subst (X ^ 2 + signedCatalanSeries ^ 3) ∧
    coeff (3 * n) signedCatalanSeries = 2 * (distinctPowersOfThree n : ZMod 3) ∧
    coeff (3 * n + 1) signedCatalanSeries = (distinctPowersOfThree n : ZMod 3) ∧
    coeff (3 * n + 2) signedCatalanSeries = 2 * (distinctPowersOfThree n : ZMod 3) :=
  ⟨signed_zero, signed_one, signed_quadratic, signed_substitution, signed_residues n hn⟩

private theorem generating_mod_three :
    generatingSeries.map (Int.castRingHom (ZMod 3)) = signedCatalanSeries := by
  let hom := Int.castRingHom (ZMod 3)
  have hz : constantCoeff (generatingSeries.map hom) = 0 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
      generating_equation.1, map_zero]
  have h1 : coeff 1 (generatingSeries.map hom) = 1 := by
    rw [coeff_map, generating_equation.2.1, map_one]
  have hi : constantCoeff (X ^ 2 + 4 * generatingSeries ^ 3) = 0 := by
    simp [generating_equation.1]
  have hm : PowerSeries.map hom
      (generatingSeries.subst (X ^ 2 + 4 * generatingSeries ^ 3)) =
      (generatingSeries.map hom).subst ((X : PowerSeries (ZMod 3)) ^ 2 +
        4 * (generatingSeries.map hom) ^ 3) := by
    have h : PowerSeries.map hom
        (generatingSeries.subst (X ^ 2 + 4 * generatingSeries ^ 3)) =
        (generatingSeries.map hom).subst
          (PowerSeries.map hom (X ^ 2 + 4 * generatingSeries ^ 3)) :=
      map_subst (.of_constantCoeff_zero hi) generatingSeries
    simpa only [map_add, map_mul, map_pow, map_X, map_ofNat] using h
  have he := congrArg (PowerSeries.map hom) generating_equation.2.2
  rw [map_pow, hm] at he
  have h4 : (4 : PowerSeries (ZMod 3)) = 1 := by
    rw [← map_ofNat C 4, show (4 : ZMod 3) = 1 from rfl, map_one]
  exact solution_unique (by decide : (2 : ZMod 3) ≠ 0) hz signed_zero h1 signed_one he
    (by simpa only [h4, one_mul] using signed_substitution)

theorem hanna_conjecture (n : ℕ) (hn : 0 < n) :
    a (3 * n) % 3 = (2 * (distinctPowersOfThree n : ℤ)) % 3 ∧
    (2 * a (3 * n + 1)) % 3 = (2 * (distinctPowersOfThree n : ℤ)) % 3 ∧
    a (3 * n + 2) % 3 = (2 * (distinctPowersOfThree n : ℤ)) % 3 := by
  have hc (k : ℕ) : (a k : ZMod 3) = coeff k signedCatalanSeries := by
    have h := congrArg (coeff k) generating_mod_three
    simpa only [a, coeff_map, Int.coe_castRingHom] using h
  have hs := signed_residues n hn
  refine ⟨?_, ?_, ?_⟩
  · apply (ZMod.intCast_eq_intCast_iff' _ _ 3).mp
    simpa only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, hc] using hs.1
  · apply (ZMod.intCast_eq_intCast_iff' _ _ 3).mp
    simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, hc, hs.2.1]
  · apply (ZMod.intCast_eq_intCast_iff' _ _ 3).mp
    simpa only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, hc] using hs.2.2

#print axioms generating_equation
#print axioms generating_unique
#print axioms signed_catalan_mod_three
#print axioms hanna_conjecture

end D5.S1.Recurrence.Invariants.SignedCatalanCubicSubstitutionModThree
