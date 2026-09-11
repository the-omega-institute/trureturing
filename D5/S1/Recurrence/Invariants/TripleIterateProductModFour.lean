/- GID: D5/S1/Recurrence/Invariants/TripleIterateProductModFour
   generality: I
   mirror-B: D5/B/S1/Recurrence/Invariants/TripleIterateProductModFour
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A coefficient perturbation and mod-sixteen lifting prove Hanna A396794. -/

import D5.S1.Recurrence.Invariants.CompositionalIterateCongruence

open PowerSeries
open D5.S1.Recurrence.Invariants.CompositionalIterateCongruence (iterate)

namespace D5.S1.Recurrence.Invariants.TripleIterateProductModFour
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

private theorem pow_low {f : PowerSeries R} (hf : constantCoeff f = 0)
    {n k : ℕ} (h : n < k) : coeff n (f ^ k) = 0 :=
  X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hf) k) n h

private theorem agree_mul {n : ℕ} {f g u v : PowerSeries R}
    (hf : constantCoeff f = 0) (hv : constantCoeff v = 0)
    (hfg : Agree n f g) (huv : Agree n u v) :
    Agree (n + 1) (f * u) (g * v) := by
  apply (agree_iff _ _ _).mpr
  have h1 := mul_dvd_mul (X_dvd_iff.mpr hf) ((agree_iff _ _ _).mp huv)
  have h2 := mul_dvd_mul ((agree_iff _ _ _).mp hfg) (X_dvd_iff.mpr hv)
  rw [mul_comm X, ← pow_succ] at h1
  rw [← pow_succ] at h2
  convert dvd_add h1 h2 using 1
  ring

private theorem agree_subst {n : ℕ} {f g u v : PowerSeries R}
    (hu : constantCoeff u = 0) (hv : constantCoeff v = 0)
    (hfg : Agree n f g) (huv : Agree n u v) :
    Agree n (f.subst u) (g.subst v) := by
  intro k hk
  rw [coeff_subst' (.of_constantCoeff_zero hu), coeff_subst' (.of_constantCoeff_zero hv)]
  apply finsum_congr
  intro e
  by_cases he : e < n
  · rw [hfg e he, agree_pow huv e k hk]
  · rw [pow_low hu (by omega : k < e), pow_low hv (by omega : k < e),
      smul_zero, smul_zero]

private theorem subst_coeff (f u : PowerSeries R) (hu : constantCoeff u = 0) (n : ℕ) :
    coeff n (f.subst u) = ∑ k ∈ Finset.range (n + 1), coeff k f * coeff n (u ^ k) := by
  rw [coeff_subst' (.of_constantCoeff_zero hu)]
  simp only [smul_eq_mul]
  apply finsum_eq_sum_of_support_subset
  intro k hk
  apply Finset.mem_range.mpr
  by_contra h
  exact hk (by dsimp; rw [pow_low hu (by omega), mul_zero])

private theorem leading_pow {u : PowerSeries R} (hu : constantCoeff u = 0)
    (hu1 : coeff 1 u = 1) (n : ℕ) : coeff n (u ^ n) = 1 := by
  obtain ⟨v, rfl⟩ := X_dvd_iff.mpr hu
  have hv : constantCoeff v = 1 := by simpa using hu1
  simp [mul_pow, coeff_X_pow_mul', hv]

private theorem pow_top {n : ℕ} {u v : PowerSeries R}
    (hu : constantCoeff u = 0) (hv : constantCoeff v = 0)
    (h : Agree n u v) (k : ℕ) : coeff n (u ^ (k + 2)) = coeff n (v ^ (k + 2)) := by
  have hh := agree_mul hu (show constantCoeff (v ^ (k + 1)) = 0 by simp [hv])
    h (agree_pow h (k + 1)) n (by omega)
  simpa only [← pow_succ'] using hh

private theorem subst_outer_top {n : ℕ} {f g u : PowerSeries R}
    (hu : constantCoeff u = 0) (hu1 : coeff 1 u = 1) (h : Agree n f g) :
    coeff n (f.subst u) - coeff n (g.subst u) = coeff n f - coeff n g := by
  rw [subst_coeff f u hu, subst_coeff g u hu, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single n]
  · rw [leading_pow hu hu1, mul_one, mul_one]
  · intro k hk hkn
    have hk' : k < n := by have := Finset.mem_range.mp hk; omega
    rw [h k hk', sub_self]
  · simp

private theorem subst_inner_top {n : ℕ} {u v : PowerSeries R} (f : PowerSeries R)
    (hn : 1 < n) (hu : constantCoeff u = 0) (hv : constantCoeff v = 0)
    (h : Agree n u v) :
    coeff n (f.subst u) - coeff n (f.subst v) =
      coeff 1 f * (coeff n u - coeff n v) := by
  rw [subst_coeff f u hu, subst_coeff f v hv, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single 1]
  · simp only [pow_one, mul_sub]
  · intro k hk hk1
    rcases k with _ | _ | k
    · simp
    · exact (hk1 rfl).elim
    · rw [pow_top hu hv h k, sub_self]
  · simp [show 1 < n + 1 by omega]

private theorem subst_top {n : ℕ} {f g u v : PowerSeries R}
    (hn : 1 < n) (hu : constantCoeff u = 0) (hv : constantCoeff v = 0)
    (hu1 : coeff 1 u = 1) (hg1 : coeff 1 g = 1)
    (hfg : Agree n f g) (huv : Agree n u v) :
    coeff n (f.subst u) - coeff n (g.subst v) =
      (coeff n f - coeff n g) + (coeff n u - coeff n v) := by
  have h1 := subst_outer_top hu hu1 hfg
  have h2 := subst_inner_top g hn hu hv huv
  rw [hg1, one_mul] at h2
  linear_combination h1 + h2

private theorem iterate_normal {f : PowerSeries R} (hf : constantCoeff f = 0)
    (hf1 : coeff 1 f = 1) (j : ℕ) :
    constantCoeff (iterate f j) = 0 ∧ coeff 1 (iterate f j) = 1 := by
  induction j with
  | zero => simp [iterate]
  | succ j ih =>
    refine ⟨constantCoeff_subst_eq_zero hf _ ih.1, ?_⟩
    rw [iterate, subst_coeff _ _ hf]
    simp [Finset.sum_range_succ, hf1, ih.2]

private theorem iterate_agree {n : ℕ} {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (h : Agree n f g) (j : ℕ) : Agree n (iterate f j) (iterate g j) := by
  induction j with
  | zero => intro k hk; rfl
  | succ j ih => exact agree_subst hf hg ih h

private theorem iterate_top {n : ℕ} {f g : PowerSeries R}
    (hn : 1 < n) (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (hf1 : coeff 1 f = 1) (hg1 : coeff 1 g = 1)
    (h : Agree n f g) (j : ℕ) :
    coeff n (iterate f j) - coeff n (iterate g j) =
      (j : R) * (coeff n f - coeff n g) := by
  induction j with
  | zero => simp [iterate]
  | succ j ih =>
    rw [iterate, iterate, subst_top hn hf hg hf1 (iterate_normal hg hg1 j).2
      (iterate_agree hf hg h j) h, ih]
    push_cast
    ring

private theorem mul_top {n : ℕ} {f g u v : PowerSeries R}
    (hf : constantCoeff f = 0) (hv : constantCoeff v = 0)
    (hf1 : coeff 1 f = 1) (hv1 : coeff 1 v = 1)
    (hfg : Agree n f g) (huv : Agree n u v) :
    coeff (n + 1) (f * u) - coeff (n + 1) (g * v) =
      (coeff n f - coeff n g) + (coeff n u - coeff n v) := by
  obtain ⟨p, hp⟩ := (agree_iff _ _ _).mp hfg
  obtain ⟨q, hq⟩ := (agree_iff _ _ _).mp huv
  have he : f * u - g * v = X ^ n * (p * v + f * q) := by
    linear_combination v * hp + f * hq
  have hc := congrArg (coeff (n + 1)) he
  have hp' := congrArg (coeff n) hp
  have hq' := congrArg (coeff n) hq
  simp only [map_sub] at hp' hq' hc
  rw [show n + 1 = 1 + n by omega, coeff_X_pow_mul, map_add, coeff_one_mul,
    coeff_one_mul, hv, hf, hf1, hv1] at hc
  simp only [mul_zero, one_mul, zero_add, add_zero] at hc
  simp only [coeff_X_pow_mul', le_refl, ↓reduceIte, Nat.sub_self,
    coeff_zero_eq_constantCoeff] at hp' hq'
  rw [Nat.add_comm 1 n] at hc
  linear_combination hc - hp' - hq'

private theorem product_top {n : ℕ} {f g : PowerSeries R}
    (hn : 1 < n) (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (hf1 : coeff 1 f = 1) (hg1 : coeff 1 g = 1) (h : Agree n f g) :
    coeff (n + 1) (f * iterate f 3) - coeff (n + 1) (g * iterate g 3) =
      4 * (coeff n f - coeff n g) := by
  rw [mul_top hf (iterate_normal hg hg1 3).1 hf1 (iterate_normal hg hg1 3).2
    h (iterate_agree hf hg h 3), iterate_top hn hf hg hf1 hg1 h]
  norm_num
  ring

private theorem subst_annihilate (r : R) (f u v : PowerSeries R)
    (hu : constantCoeff u = 0) (hv : constantCoeff v = 0)
    (h : C r * (u - v) = 0) : C r * (f.subst u - f.subst v) = 0 := by
  ext n
  simp only [coeff_C_mul, map_sub, map_zero]
  rw [subst_coeff f u hu, subst_coeff f v hv, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro k hk
  obtain ⟨q, hq⟩ := sub_dvd_pow_sub_pow u v k
  have hp : C r * (u ^ k - v ^ k) = 0 := by rw [hq, ← mul_assoc, h, zero_mul]
  have hc := congrArg (coeff n) hp
  simp only [coeff_C_mul, map_sub, map_zero] at hc
  linear_combination coeff k f * hc

private theorem nilpotent_iterate (r : R) (hr : r * r = 0) (b : PowerSeries R)
    (hz : constantCoeff (X + C r * b) = 0) (j : ℕ) :
    iterate (X + C r * b) j = X + C ((j : R) * r) * b := by
  have hs : HasSubst (X + C r * b) := .of_constantCoeff_zero hz
  have ha : C r * (b.subst (X + C r * b) - b) = 0 := by
    simpa only [X_subst] using subst_annihilate r b (X + C r * b) X hz
      constantCoeff_X (by simp only [add_sub_cancel_left]; rw [← mul_assoc, ← map_mul, hr,
        map_zero, zero_mul])
  induction j with
  | zero => simp [iterate]
  | succ j ih =>
    rw [iterate, ih, subst_add hs, subst_X hs, subst_mul hs, subst_C]
    change X + C r * b + C ((j : R) * r) * b.subst (X + C r * b) =
      X + C (((j + 1 : ℕ) : R) * r) * b
    push_cast
    simp only [map_add, map_mul, map_one]
    linear_combination C (j : R) * ha

private theorem mod_sixteen_product (f : PowerSeries ℤ)
    (hf : constantCoeff f = 0) (h4 : ∀ n, 4 ∣ coeff n (f - X)) :
    ∀ n, 16 ∣ coeff n (f * iterate f 3 - X ^ 2) := by
  let b : PowerSeries ℤ := mk fun n => coeff n (f - X) / 4
  have hb : f = X + C 4 * b := by
    ext n
    have hh := Int.mul_ediv_cancel' (h4 n)
    simp only [map_sub] at hh
    simp only [map_add, coeff_C_mul, b, coeff_mk, map_sub]
    linear_combination -hh
  let hom := Int.castRingHom (ZMod 16)
  have hz : constantCoeff (f.map hom) = 0 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff, hf, map_zero]
  have hm : f.map hom = X + C 4 * b.map hom := by
    rw [hb]
    simp only [map_add, map_mul, map_X, map_C]
    norm_num [hom]
  have hi : (iterate f 3).map hom = iterate (f.map hom) 3 := by
    have aux : ∀ j, (iterate f j).map hom = iterate (f.map hom) j := by
      intro j
      induction j with
      | zero => simp [iterate]
      | succ j ih =>
        change (iterate f j |>.subst f).map hom =
          (iterate (f.map hom) j).subst (f.map hom)
        rw [show (iterate f j |>.subst f).map hom =
          ((iterate f j).map hom).subst (f.map hom) from
          map_subst (.of_constantCoeff_zero hf) _, ih]
    exact aux 3
  have hn := nilpotent_iterate (4 : ZMod 16) (by decide) (b.map hom) (hm ▸ hz) 3
  have he : (f * iterate f 3 - X ^ 2).map hom = 0 := by
    rw [map_sub, map_mul, map_pow, map_X, hi, hm, hn]
    norm_num only [Nat.cast_ofNat, show (3 : ZMod 16) * 4 = 12 by decide]
    have hsum : C (4 : ZMod 16) + C 12 = 0 := by
      rw [← map_add, show (4 : ZMod 16) + 12 = 0 by decide, map_zero]
    have hprod : C (4 : ZMod 16) * C 12 = 0 := by
      rw [← map_mul, show (4 : ZMod 16) * 12 = 0 by decide, map_zero]
    linear_combination X * b.map hom * hsum + (b.map hom) ^ 2 * hprod
  intro n
  have hc := congrArg (coeff n) he
  simp only [coeff_map, map_zero, hom, Int.coe_castRingHom] at hc
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc

private noncomputable def rhs : PowerSeries ℤ := X ^ 2 + C 16 * X ^ 3

private theorem error_divisible (f : PowerSeries ℤ)
    (hf : constantCoeff f = 0) (h4 : ∀ n, 4 ∣ coeff n (f - X)) (n : ℕ) :
    16 ∣ coeff n (rhs - f * iterate f 3) := by
  have h := mod_sixteen_product f hf h4 n
  have he : coeff n (rhs - f * iterate f 3) =
      16 * coeff n (X ^ 3 : PowerSeries ℤ) - coeff n (f * iterate f 3 - X ^ 2) := by
    simp only [rhs, map_sub, map_add, coeff_C_mul]
    ring
  rw [he]
  exact dvd_sub (dvd_mul_right _ _) h

private noncomputable def correction (n : ℕ) (f : PowerSeries ℤ) : ℤ :=
  coeff (n + 1) (rhs - f * iterate f 3) / 4

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

private theorem extend_four {n : ℕ} {f : PowerSeries ℤ}
    (hf : constantCoeff f = 0) (h4 : ∀ k, 4 ∣ coeff k (f - X)) :
    ∀ k, 4 ∣ coeff k (extend n f - X) := by
  have hc : 4 ∣ correction n f := by
    obtain ⟨q, hq⟩ := error_divisible f hf h4 (n + 1)
    refine ⟨q, ?_⟩
    simp only [correction, hq]
    omega
  intro k
  have he : coeff k (extend n f - X) =
      coeff k (f - X) + if k = n then correction n f else 0 := by
    simp only [extend, map_sub, map_add, coeff_C_mul_X_pow]
    ring
  rw [he]
  exact dvd_add (h4 k) (by split_ifs <;> simp_all)

private theorem extend_correct {n : ℕ} {f : PowerSeries ℤ}
    (hn : 1 < n) (hf : constantCoeff f = 0) (hf1 : coeff 1 f = 1)
    (h4 : ∀ k, 4 ∣ coeff k (f - X))
    (he : Agree (n + 1) (f * iterate f 3) rhs) :
    Agree (n + 2) (extend n f * iterate (extend n f) 3) rhs := by
  have hz := extend_normal hn hf hf1
  have ht := product_top hn hz.1 hf hz.2 hf1 (extend_agree n f)
  have hc : 4 * correction n f = coeff (n + 1) (rhs - f * iterate f 3) :=
    Int.mul_ediv_cancel' (dvd_trans (by norm_num : (4 : ℤ) ∣ 16)
      (error_divisible f hf h4 (n + 1)))
  have hcoeff : coeff n (extend n f) - coeff n f = correction n f := by
    simp only [extend, map_add, coeff_C_mul_X_pow, ↓reduceIte]
    ring
  rw [hcoeff, hc, map_sub] at ht
  intro k hk
  by_cases hkn : k < n + 1
  · exact (agree_mul hz.1 (iterate_normal hf hf1 3).1 (extend_agree n f)
      (iterate_agree hz.1 hf (extend_agree n f) 3) k hkn).trans (he k hkn)
  · have hk' : k = n + 1 := by omega
    subst k
    linear_combination ht

private noncomputable def approximation : ℕ → PowerSeries ℤ
  | 0 => X
  | j + 1 => extend (j + 2) (approximation j)

private theorem approximation_spec (j : ℕ) :
    constantCoeff (approximation j) = 0 ∧ coeff 1 (approximation j) = 1 ∧
    (∀ k, 4 ∣ coeff k (approximation j - X)) ∧
    Agree (j + 3) (approximation j * iterate (approximation j) 3) rhs := by
  induction j with
  | zero =>
    have hi : ∀ k, iterate (X : PowerSeries ℤ) k = X := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => simpa only [iterate, X_subst] using ih
    refine ⟨by simp [approximation], by simp [approximation], ?_, ?_⟩
    · intro k; simp [approximation]
    · intro k hk
      simp only [approximation, hi, rhs, map_add, coeff_C_mul_X_pow]
      rw [if_neg (by omega : k ≠ 3), add_zero]
      congr 1
      ring
  | succ j ih =>
    have hz := extend_normal (by omega : 1 < j + 2) ih.1 ih.2.1
    exact ⟨hz.1, hz.2, extend_four ih.1 ih.2.2.1,
      extend_correct (by omega) ih.1 ih.2.1 ih.2.2.1 ih.2.2.2⟩

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
    f * iterate f 3 = X ^ 2 + 16 * X ^ 3 ∧ constantCoeff f = 0 ∧ coeff 1 f = 1 := by
  have hz : constantCoeff limitSeries = 0 := by
    simpa only [coeff_zero_eq_constantCoeff, approximation, constantCoeff_X] using
      limit_agree 0 0 (by omega)
  have h1 : coeff 1 limitSeries = 1 := by
    simpa only [approximation, coeff_one_X] using limit_agree 0 1 (by omega)
  refine ⟨limitSeries, ?_, hz, h1⟩
  change limitSeries * iterate limitSeries 3 = rhs
  ext n
  exact (agree_mul hz (iterate_normal (approximation_spec n).1
    (approximation_spec n).2.1 3).1 (limit_agree n)
    (iterate_agree hz (approximation_spec n).1 (limit_agree n) 3) n (by omega)).trans
      ((approximation_spec n).2.2.2 n (by omega))

noncomputable def generatingSeries : PowerSeries ℤ := Classical.choose exists_series

noncomputable def a (n : ℕ) : ℤ := coeff n generatingSeries

theorem generating_equation :
    generatingSeries * iterate generatingSeries 3 = X ^ 2 + 16 * X ^ 3 ∧
    constantCoeff generatingSeries = 0 ∧ coeff 1 generatingSeries = 1 :=
  Classical.choose_spec exists_series

theorem generating_unique (f : PowerSeries ℤ)
    (he : f * iterate f 3 = X ^ 2 + 16 * X ^ 3)
    (hf : constantCoeff f = 0) (hf1 : coeff 1 f = 1) : f = generatingSeries := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n
      simpa only [coeff_zero_eq_constantCoeff, hf] using generating_equation.2.1.symm
    by_cases hn1 : n = 1
    · subst n
      exact hf1.trans generating_equation.2.2.symm
    have ht := product_top (by omega : 1 < n) hf generating_equation.2.1
      hf1 generating_equation.2.2 ih
    rw [he, generating_equation.1, sub_self] at ht
    omega

private theorem solution_four (f : PowerSeries ℤ)
    (he : f * iterate f 3 = rhs) (hf : constantCoeff f = 0) (hf1 : coeff 1 f = 1) :
    ∀ n, 1 < n → 4 ∣ coeff n f := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    let p : PowerSeries ℤ := mk fun k => if k < n then coeff k f else 0
    have hp : Agree n f p := by
      intro k hk
      simp only [p, coeff_mk, if_pos hk]
    have hp0 : constantCoeff p = 0 := by
      simpa only [coeff_zero_eq_constantCoeff, hf] using (hp 0 (by omega)).symm
    have hp1 : coeff 1 p = 1 := by rw [← hp 1 hn, hf1]
    have hpn : coeff n p = 0 := by simp [p]
    have h4 : ∀ k, 4 ∣ coeff k (p - X) := by
      intro k
      rw [map_sub]
      by_cases hk0 : k = 0
      · subst k
        simp [coeff_zero_eq_constantCoeff, hp0]
      by_cases hk1 : k = 1
      · subst k
        simp [hp1]
      have hx : coeff k (X : PowerSeries ℤ) = 0 := by simp [coeff_X, hk1]
      rw [hx, sub_zero]
      by_cases hkn : k < n
      · rw [← hp k hkn]
        exact ih k hkn (by omega)
      · simp [p, hkn]
    have ht := product_top hn hf hp0 hf1 hp1 hp
    rw [hpn, sub_zero, he] at ht
    have hd := error_divisible p hp0 h4 (n + 1)
    rw [map_sub, ht] at hd
    obtain ⟨q, hq⟩ := hd
    exact ⟨q, by omega⟩

theorem hanna_conjecture (n : ℕ) (hn : 1 < n) : 4 ∣ a n :=
  solution_four generatingSeries generating_equation.1 generating_equation.2.1
    generating_equation.2.2 n hn

#print axioms generating_equation
#print axioms generating_unique
#print axioms hanna_conjecture

end D5.S1.Recurrence.Invariants.TripleIterateProductModFour
