/- GID: D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Cubic lifting and a mod-two series identity prove Hanna's A392525 parity conjecture. -/

import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.FieldTheory.Finite.Basic

open PowerSeries

namespace D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity

private theorem prime_power_subst (p : ℕ) [Fact p.Prime]
    (f : PowerSeries (ZMod p)) : f ^ p = f.subst (X ^ p) := by
  have h := MvPowerSeries.map_frobenius_expand (σ := Unit) (R := ZMod p)
    p (NeZero.ne p) (f := f)
  rw [ZMod.frobenius_zmod, MvPowerSeries.map_id] at h
  exact h.symm.trans (PowerSeries.expand_apply p (NeZero.ne p) f)

noncomputable def powerTwoSeries : PowerSeries (ZMod 2) := by
  classical
  exact mk fun n => if ∃ k : ℕ, n = 2 ^ k then 1 else 0

private theorem dyadic_halve (n : ℕ) (hn : n ≠ 1) :
    (∃ k : ℕ, n = 2 ^ k) ↔ 2 ∣ n ∧ ∃ k : ℕ, n / 2 = 2 ^ k := by
  constructor
  · rintro ⟨k, rfl⟩
    cases k with
    | zero => simp at hn
    | succ k =>
      rw [pow_succ]
      exact ⟨dvd_mul_left _ _, k, Nat.mul_div_cancel _ (by decide)⟩
  · rintro ⟨hd, k, hk⟩
    refine ⟨k + 1, ?_⟩
    rw [pow_succ, ← hk, Nat.div_mul_cancel hd]

private theorem power_two_zero : constantCoeff powerTwoSeries = 0 := by
  have hz : ¬ ∃ k : ℕ, 0 = 2 ^ k := by
    rintro ⟨k, hk⟩
    exact pow_ne_zero k (by decide : (2 : ℕ) ≠ 0) hk.symm
  simp only [powerTwoSeries, constantCoeff_mk, if_neg hz]

private theorem power_two_one : coeff 1 powerTwoSeries = 1 := by
  simp only [powerTwoSeries, coeff_mk, if_pos (show ∃ k : ℕ, 1 = 2 ^ k from ⟨0, rfl⟩)]

private theorem power_two_quadratic : powerTwoSeries = X + powerTwoSeries ^ 2 := by
  classical
  rw [prime_power_subst]
  ext n
  rw [map_add, coeff_subst_X_pow (by decide)]
  by_cases hn : n = 1
  · subst n
    simp [power_two_one]
  · simp only [powerTwoSeries, coeff_mk, coeff_X, if_neg hn, zero_add]
    rw [dyadic_halve n hn]
    by_cases hd : 2 ∣ n <;> simp [hd]

private theorem quadratic_unique {u v : PowerSeries (ZMod 2)}
    (hu : constantCoeff u = 0) (hv : constantCoeff v = 0)
    (h : u + u ^ 2 = v + v ^ 2) : u = v := by
  have hz : (u - v) * (1 + u + v) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hz with he | he
  · exact sub_eq_zero.mp he
  · have hc := congrArg constantCoeff he
    simp [hu, hv] at hc

theorem thue_series_equation :
    powerTwoSeries = X + powerTwoSeries ^ 2 ∧
    powerTwoSeries ^ 3 = powerTwoSeries.subst (X ^ 3 + X * powerTwoSeries ^ 3) := by
  refine ⟨power_two_quadratic, ?_⟩
  let t : PowerSeries (ZMod 2) := X ^ 3 + X * powerTwoSeries ^ 3
  have ht : constantCoeff t = 0 := by simp [t]
  have hs : HasSubst t := .of_constantCoeff_zero ht
  have hc : powerTwoSeries + powerTwoSeries ^ 2 = X := by
    have hz : (2 : PowerSeries (ZMod 2)) = 0 := by
      rw [← map_ofNat C 2, show (2 : ZMod 2) = 0 by decide, map_zero]
    linear_combination power_two_quadratic + powerTwoSeries ^ 2 * hz
  have hd : powerTwoSeries ^ 3 + (powerTwoSeries ^ 3) ^ 2 = t := by
    dsimp [t]
    have hz : (2 : PowerSeries (ZMod 2)) = 0 := by
      rw [← map_ofNat C 2, show (2 : ZMod 2) = 0 by decide, map_zero]
    linear_combination
      (powerTwoSeries ^ 4 + powerTwoSeries ^ 3 +
        (X + 1) * powerTwoSeries ^ 2 + X * powerTwoSeries + X ^ 2) * hc -
        (powerTwoSeries ^ 5 + powerTwoSeries ^ 4 + X * powerTwoSeries ^ 3) * hz
  have he := congrArg (subst t) hc
  rw [subst_add hs, subst_pow hs, subst_X hs] at he
  exact quadratic_unique (by simp [power_two_zero])
    (constantCoeff_subst_eq_zero ht _ power_two_zero) (hd.trans he.symm)

section Coefficients

variable {R : Type*} [CommRing R]

private def Agree (n : ℕ) (f g : PowerSeries R) : Prop :=
  ∀ k < n, coeff k f = coeff k g

private theorem agree_iff (n : ℕ) (f g : PowerSeries R) :
    Agree n f g ↔ (X : PowerSeries R) ^ n ∣ f - g := by
  simp [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]

private theorem agree_pow {n : ℕ} {f g : PowerSeries R}
    (h : Agree n f g) (k : ℕ) : Agree n (f ^ k) (g ^ k) :=
  (agree_iff _ _ _).mpr ((agree_iff _ _ _).mp h |>.trans
    (sub_dvd_pow_sub_pow f g k))

private theorem pow_low {u : PowerSeries R} {d e k : ℕ}
    (hu : (X : PowerSeries R) ^ d ∣ u) (hk : k < d * e) : coeff k (u ^ e) = 0 := by
  apply X_pow_dvd_iff.mp _ k hk
  simpa only [← pow_mul] using pow_dvd_pow_of_dvd hu e

private theorem agree_cube {n : ℕ} {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (h : Agree n f g) : Agree (n + 2) (f ^ 3) (g ^ 3) := by
  obtain ⟨u, hu⟩ := X_dvd_iff.mpr hf
  obtain ⟨v, hv⟩ := X_dvd_iff.mpr hg
  obtain ⟨w, hw⟩ := (agree_iff _ _ _).mp h
  apply (agree_iff _ _ _).mpr
  refine ⟨w * (u ^ 2 + u * v + v ^ 2), ?_⟩
  calc
    f ^ 3 - g ^ 3 = (f - g) * (f ^ 2 + f * g + g ^ 2) := by ring
    _ = X ^ (n + 2) * (w * (u ^ 2 + u * v + v ^ 2)) := by
      rw [hw, hu, hv, pow_add]
      ring

private theorem cube_top {n : ℕ} {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (hf1 : coeff 1 f = 1) (hg1 : coeff 1 g = 1) (h : Agree n f g) :
    coeff (n + 2) (f ^ 3) - coeff (n + 2) (g ^ 3) =
      3 * (coeff n f - coeff n g) := by
  obtain ⟨u, hu⟩ := X_dvd_iff.mpr hf
  obtain ⟨v, hv⟩ := X_dvd_iff.mpr hg
  have hu0 : constantCoeff u = 1 := by simpa [hu] using hf1
  have hv0 : constantCoeff v = 1 := by simpa [hv] using hg1
  obtain ⟨w, hw⟩ := (agree_iff _ _ _).mp h
  have he : f ^ 3 - g ^ 3 = X ^ (n + 2) * (w * (u ^ 2 + u * v + v ^ 2)) := by
    calc
      f ^ 3 - g ^ 3 = (f - g) * (f ^ 2 + f * g + g ^ 2) := by ring
      _ = _ := by rw [hw, hu, hv, pow_add]; ring
  have hc := congrArg (coeff (n + 2)) he
  have hd := congrArg (coeff n) hw
  simp only [map_sub, coeff_X_pow_mul', le_refl, ↓reduceIte, Nat.sub_self,
    coeff_zero_eq_constantCoeff, map_mul, map_add, map_pow, hu0, hv0,
    one_pow, one_mul] at hc hd
  rw [hd]
  linear_combination hc

private theorem agree_subst_order {n m d : ℕ} {f g u v : PowerSeries R}
    (hu : constantCoeff u = 0) (hv : constantCoeff v = 0)
    (hud : (X : PowerSeries R) ^ d ∣ u) (hvd : (X : PowerSeries R) ^ d ∣ v)
    (hm : m ≤ d * n) (hfg : Agree n f g) (huv : Agree m u v) :
    Agree m (f.subst u) (g.subst v) := by
  intro k hk
  rw [coeff_subst' (.of_constantCoeff_zero hu), coeff_subst' (.of_constantCoeff_zero hv)]
  apply finsum_congr
  intro e
  by_cases he : e < n
  · rw [hfg e he, agree_pow huv e k hk]
  · have he' : n ≤ e := by omega
    have hke : k < d * e := lt_of_lt_of_le (lt_of_lt_of_le hk hm) (Nat.mul_le_mul_left d he')
    rw [pow_low hud hke, pow_low hvd hke, smul_zero, smul_zero]

private noncomputable def inner (f : PowerSeries R) : PowerSeries R :=
  X ^ 3 + 15 * X * f ^ 3

private theorem inner_zero (f : PowerSeries R) : constantCoeff (inner f) = 0 := by
  simp [inner]

private theorem inner_order {f : PowerSeries R} (hf : constantCoeff f = 0) :
    (X : PowerSeries R) ^ 3 ∣ inner f := by
  apply dvd_add (dvd_refl _)
  exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hf) 3) _

private theorem inner_agree {n : ℕ} {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) (h : Agree n f g) :
    Agree (n + 3) (inner f) (inner g) := by
  apply (agree_iff _ _ _).mpr
  obtain ⟨w, hw⟩ := (agree_iff _ _ _).mp (agree_cube hf hg h)
  refine ⟨15 * w, ?_⟩
  have he : inner f - inner g = 15 * X * (f ^ 3 - g ^ 3) := by dsimp [inner]; ring
  rw [he, hw, show n + 3 = (n + 2) + 1 by omega, pow_succ]
  ring

private theorem rhs_agree {n : ℕ} {f g : PowerSeries R} (hn : 1 < n)
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) (h : Agree n f g) :
    Agree (n + 3) (f.subst (inner f)) (g.subst (inner g)) :=
  agree_subst_order (inner_zero f) (inner_zero g) (inner_order hf) (inner_order hg)
    (by omega) h (inner_agree hf hg h)

private noncomputable def residual (f : PowerSeries R) : PowerSeries R :=
  f ^ 3 - f.subst (inner f)

private theorem residual_agree {n : ℕ} {f g : PowerSeries R} (hn : 1 < n)
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) (h : Agree n f g) :
    Agree (n + 2) (residual f) (residual g) := by
  intro k hk
  simp only [residual, map_sub]
  rw [agree_cube hf hg h k hk, rhs_agree hn hf hg h k (by omega)]

private theorem residual_top {n : ℕ} {f g : PowerSeries R} (hn : 1 < n)
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (hf1 : coeff 1 f = 1) (hg1 : coeff 1 g = 1) (h : Agree n f g) :
    coeff (n + 2) (residual f) - coeff (n + 2) (residual g) =
      3 * (coeff n f - coeff n g) := by
  have hc := cube_top hf hg hf1 hg1 h
  have hr := rhs_agree hn hf hg h (n + 2) (by omega)
  simp only [residual, map_sub]
  linear_combination hc - hr

end Coefficients

private theorem residual_divisible (f : PowerSeries ℤ) (n : ℕ) :
    3 ∣ coeff n (residual f) := by
  let hom := Int.castRingHom (ZMod 3)
  have h15 : (15 : PowerSeries (ZMod 3)) = 0 := by
    rw [← map_ofNat C 15, show (15 : ZMod 3) = 0 by decide, map_zero]
  have hi : (inner f).map hom = X ^ 3 := by
    simp only [inner, map_add, map_mul, map_pow, map_X, map_ofNat, h15, zero_mul, add_zero]
  have he : (residual f).map hom = 0 := by
    simp only [residual, map_sub, map_pow]
    rw [show PowerSeries.map hom (f.subst (inner f)) =
        (f.map hom).subst ((inner f).map hom) from
      map_subst (.of_constantCoeff_zero (inner_zero f)) _, hi,
      prime_power_subst, sub_self]
  have hc := congrArg (coeff n) he
  simp only [coeff_map, map_zero, hom, Int.coe_castRingHom] at hc
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc

private noncomputable def correction (n : ℕ) (f : PowerSeries ℤ) : ℤ :=
  -(coeff (n + 2) (residual f) / 3)

private noncomputable def extend (n : ℕ) (f : PowerSeries ℤ) : PowerSeries ℤ :=
  f + C (correction n f) * X ^ n

private theorem extend_agree (n : ℕ) (f : PowerSeries ℤ) : Agree n (extend n f) f := by
  intro k hk
  simp only [extend, map_add, coeff_C_mul_X_pow, if_neg (show k ≠ n by omega), add_zero]

private theorem extend_normal {n : ℕ} {f : PowerSeries ℤ}
    (hn : 1 < n) (hf : constantCoeff f = 0) (hf1 : coeff 1 f = 1) :
    constantCoeff (extend n f) = 0 ∧ coeff 1 (extend n f) = 1 := by
  constructor
  · simpa only [coeff_zero_eq_constantCoeff, hf] using extend_agree n f 0 (by omega)
  · simpa only [hf1] using extend_agree n f 1 hn

private theorem extend_correct {n : ℕ} {f : PowerSeries ℤ}
    (hn : 1 < n) (hf : constantCoeff f = 0) (hf1 : coeff 1 f = 1)
    (he : Agree (n + 2) (residual f) 0) :
    Agree (n + 3) (residual (extend n f)) 0 := by
  have hz := extend_normal hn hf hf1
  have ht := residual_top hn hz.1 hf hz.2 hf1 (extend_agree n f)
  have hc : 3 * correction n f = -coeff (n + 2) (residual f) := by
    dsimp [correction]
    rw [mul_neg, Int.mul_ediv_cancel' (residual_divisible f (n + 2))]
  have hcoeff : coeff n (extend n f) - coeff n f = correction n f := by
    simp only [extend, map_add, coeff_C_mul_X_pow, ↓reduceIte]
    ring
  rw [hcoeff, hc] at ht
  intro k hk
  by_cases hkn : k < n + 2
  · exact (residual_agree hn hz.1 hf (extend_agree n f) k hkn).trans (he k hkn)
  · have hk' : k = n + 2 := by omega
    subst k
    simp only [map_zero]
    linear_combination ht

private noncomputable def approximation : ℕ → PowerSeries ℤ
  | 0 => X
  | j + 1 => extend (j + 2) (approximation j)

private theorem approximation_spec (j : ℕ) :
    constantCoeff (approximation j) = 0 ∧ coeff 1 (approximation j) = 1 ∧
    Agree (j + 4) (residual (approximation j)) 0 := by
  induction j with
  | zero =>
    refine ⟨by simp [approximation], by simp [approximation], ?_⟩
    intro k hk
    simp only [map_zero]
    have hd : (X : PowerSeries ℤ) ^ 4 ∣ residual (approximation 0) := by
      refine ⟨-15, ?_⟩
      simp only [approximation, residual]
      rw [subst_X (.of_constantCoeff_zero (inner_zero _))]
      dsimp [inner]
      ring
    exact X_pow_dvd_iff.mp hd k hk
  | succ j ih =>
    have hz := extend_normal (by omega : 1 < j + 2) ih.1 ih.2.1
    exact ⟨hz.1, hz.2, extend_correct (by omega) ih.1 ih.2.1 ih.2.2⟩

private theorem approximation_stable {j k : ℕ} (hjk : j ≤ k) :
    Agree (j + 2) (approximation k) (approximation j) := by
  induction k, hjk using Nat.le_induction with
  | base => intro i hi; rfl
  | succ k hk ih =>
    intro i hi
    exact (extend_agree (k + 2) (approximation k) i (by omega)).trans (ih i hi)

private noncomputable def limitSeries : PowerSeries ℤ :=
  mk fun n => coeff n (approximation n)

private theorem limit_agree (j : ℕ) : Agree (j + 2) limitSeries (approximation j) := by
  intro n hn
  simp only [limitSeries, coeff_mk]
  by_cases hnj : n ≤ j
  · exact (approximation_stable hnj n (by omega)).symm
  · exact approximation_stable (by omega : j ≤ n) n hn

private theorem exists_series : ∃ f : PowerSeries ℤ,
    constantCoeff f = 0 ∧ coeff 1 f = 1 ∧
    f ^ 3 = f.subst (X ^ 3 + 15 * X * f ^ 3) := by
  have hz : constantCoeff limitSeries = 0 := by
    simpa only [coeff_zero_eq_constantCoeff, approximation, constantCoeff_X] using
      limit_agree 0 0 (by omega)
  have h1 : coeff 1 limitSeries = 1 := by
    simpa only [approximation, coeff_one_X] using limit_agree 0 1 (by omega)
  refine ⟨limitSeries, hz, h1, ?_⟩
  change limitSeries ^ 3 = limitSeries.subst (inner limitSeries)
  apply sub_eq_zero.mp
  change residual limitSeries = 0
  ext n
  exact (residual_agree (by omega) hz (approximation_spec n).1 (limit_agree n)
    n (by omega)).trans ((approximation_spec n).2.2 n (by omega))

noncomputable def generatingSeries : PowerSeries ℤ := Classical.choose exists_series

noncomputable def a (n : ℕ) : ℤ := coeff n generatingSeries

theorem generating_equation : constantCoeff generatingSeries = 0 ∧
    coeff 1 generatingSeries = 1 ∧
    generatingSeries ^ 3 =
      generatingSeries.subst (X ^ 3 + 15 * X * generatingSeries ^ 3) :=
  Classical.choose_spec exists_series

private theorem solution_unique {R : Type*} [CommRing R] [NoZeroDivisors R]
    (h3 : (3 : R) ≠ 0) {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (hf1 : coeff 1 f = 1) (hg1 : coeff 1 g = 1)
    (he : residual f = 0) (he' : residual g = 0) : f = g := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n
      simpa only [coeff_zero_eq_constantCoeff, hf] using hg.symm
    by_cases hn1 : n = 1
    · subst n
      exact hf1.trans hg1.symm
    have ht := residual_top (by omega : 1 < n) hf hg hf1 hg1 ih
    rw [he, he', map_zero, sub_self] at ht
    exact sub_eq_zero.mp ((mul_eq_zero.mp ht.symm).resolve_left h3)

theorem generating_unique (f : PowerSeries ℤ)
    (hf : constantCoeff f = 0) (hf1 : coeff 1 f = 1)
    (he : f ^ 3 = f.subst (X ^ 3 + 15 * X * f ^ 3)) : f = generatingSeries :=
  solution_unique (by decide) hf generating_equation.1 hf1 generating_equation.2.1
    (sub_eq_zero.mpr he) (sub_eq_zero.mpr generating_equation.2.2)

private theorem generating_mod_two :
    generatingSeries.map (Int.castRingHom (ZMod 2)) = powerTwoSeries := by
  let hom := Int.castRingHom (ZMod 2)
  have hz : constantCoeff (generatingSeries.map hom) = 0 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
      generating_equation.1, map_zero]
  have h1 : coeff 1 (generatingSeries.map hom) = 1 := by
    rw [coeff_map, generating_equation.2.1, map_one]
  have hi : PowerSeries.map hom (inner generatingSeries) = inner (generatingSeries.map hom) := by
    simp only [inner, map_add, map_mul, map_pow, map_X, map_ofNat]
  have he : residual (generatingSeries.map hom) = 0 := by
    have h := congrArg (PowerSeries.map hom) (sub_eq_zero.mpr generating_equation.2.2)
    change PowerSeries.map hom (residual generatingSeries) = PowerSeries.map hom 0 at h
    simp only [residual, map_sub, map_pow, map_zero] at h ⊢
    rw [show PowerSeries.map hom (generatingSeries.subst (inner generatingSeries)) =
      (generatingSeries.map hom).subst ((inner generatingSeries).map hom) from
      map_subst (.of_constantCoeff_zero (inner_zero generatingSeries)) _, hi] at h
    exact h
  have h15 : (15 : PowerSeries (ZMod 2)) = 1 := by
    rw [← map_ofNat C 15, show (15 : ZMod 2) = 1 by decide, map_one]
  have hc : residual powerTwoSeries = 0 := by
    simp only [residual, inner, h15, one_mul]
    exact sub_eq_zero.mpr thue_series_equation.2
  exact solution_unique (by decide : (3 : ZMod 2) ≠ 0) hz power_two_zero h1 power_two_one he hc

theorem hanna_conjecture (n : ℕ) (_hn : 1 ≤ n) : Odd (a n) ↔ ∃ k : ℕ, n = 2 ^ k := by
  classical
  have hc := congrArg (coeff n) generating_mod_two
  change (a n : ZMod 2) = coeff n powerTwoSeries at hc
  rw [← ZMod.intCast_eq_one_iff_odd, hc]
  simp only [powerTwoSeries, coeff_mk]
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun he => (zero_ne_one he).elim, fun he => (h he).elim⟩

#print axioms generating_equation
#print axioms generating_unique
#print axioms thue_series_equation
#print axioms hanna_conjecture

end D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity
