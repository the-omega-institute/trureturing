/- GID: D5/S1/Recurrence/Invariants/TripleIterateShiftModThree
   generality: I
   mirror-B: D5/B/S1/Recurrence/Invariants/TripleIterateShiftModThree
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: First differences and a geometric solution modulo three prove Hanna A396102. -/

import D5.S1.Recurrence.Invariants.CompositionalIterateCongruence

open PowerSeries
open D5.S1.Recurrence.Invariants.CompositionalIterateCongruence
  (iterate mobius mobius_iterate)

namespace D5.S1.Recurrence.Invariants.TripleIterateShiftModThree

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

private noncomputable def step (f : PowerSeries R) : PowerSeries R :=
  f + (1 + X) * iterate f 2 - iterate f 3

private theorem step_normal {f : PowerSeries R} (hf : constantCoeff f = 0)
    (hf1 : coeff 1 f = 1) : constantCoeff (step f) = 0 ∧ coeff 1 (step f) = 1 := by
  have h2 := iterate_normal hf hf1 2
  have h3 := iterate_normal hf hf1 3
  simp [step, hf, hf1, coeff_one_mul, h2.1, h2.2, h3.1, h3.2]

-- The first differing coefficient occurs twice on the right and three times on the left.
private theorem step_contract {n : ℕ} {f g : PowerSeries R}
    (hn : 1 < n) (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (hf1 : coeff 1 f = 1) (hg1 : coeff 1 g = 1) (h : Agree n f g) :
    Agree (n + 1) (step f) (step g) := by
  have h2 := iterate_agree hf hg h 2
  have h3 := iterate_agree hf hg h 3
  have hx : Agree (n + 1) (X * iterate f 2) (X * iterate g 2) :=
    agree_mul constantCoeff_X (iterate_normal hg hg1 2).1 (fun _ _ => rfl) h2
  intro k hk
  by_cases hkn : k < n
  · simp only [step, add_mul, one_mul, map_sub, map_add]
    rw [h k hkn, h2 k hkn, h3 k hkn, hx k hk]
  · have hkn : k = n := by omega
    subst k
    have ht2 := iterate_top hn hf hg hf1 hg1 h 2
    have ht3 := iterate_top hn hf hg hf1 hg1 h 3
    have hxt := hx n (by omega)
    norm_num only [Nat.cast_ofNat] at ht2 ht3
    simp only [step, add_mul, one_mul, map_sub, map_add]
    linear_combination ht2 - ht3 + hxt

private theorem normal_agree {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (hf1 : coeff 1 f = 1) (hg1 : coeff 1 g = 1) : Agree 2 f g := by
  intro k hk
  have h : k = 0 ∨ k = 1 := by omega
  rcases h with rfl | rfl <;> simp_all [coeff_zero_eq_constantCoeff]

private theorem unique {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (hf1 : coeff 1 f = 1) (hg1 : coeff 1 g = 1)
    (he : iterate f 3 = (1 + X) * iterate f 2)
    (hgE : iterate g 3 = (1 + X) * iterate g 2) : f = g := by
  have ff : step f = f := by simp [step, he]
  have gg : step g = g := by simp [step, hgE]
  have ha : ∀ d, Agree (d + 2) f g := by
    intro d
    induction d with
    | zero => exact normal_agree hf hg hf1 hg1
    | succ d ih =>
      simpa only [ff, gg, Nat.add_right_comm d 1 2] using
        step_contract (by omega : 1 < d + 2) hf hg hf1 hg1 ih
  ext n
  exact ha n n (by omega)

private noncomputable def approximation : ℕ → PowerSeries R
  | 0 => X
  | d + 1 => step (approximation d)

private theorem approximation_normal (d : ℕ) :
    constantCoeff (approximation (R := R) d) = 0 ∧
    coeff 1 (approximation (R := R) d) = 1 := by
  induction d with
  | zero => simp [approximation]
  | succ d ih => exact step_normal ih.1 ih.2

private theorem approximation_stable {d e : ℕ} (h : d ≤ e) :
    Agree (d + 2) (approximation (R := R) d) (approximation e) := by
  induction d generalizing e with
  | zero =>
    exact normal_agree (approximation_normal 0).1 (approximation_normal e).1
      (approximation_normal 0).2 (approximation_normal e).2
  | succ d ih =>
    cases e with
    | zero => omega
    | succ e =>
      simpa only [approximation, Nat.add_right_comm d 1 2] using
        step_contract (by omega : 1 < d + 2)
          (approximation_normal d).1 (approximation_normal e).1
          (approximation_normal d).2 (approximation_normal e).2 (ih (by omega))

noncomputable def a (n : ℕ) : ℤ := coeff n (approximation n)

noncomputable def generatingSeries : PowerSeries ℤ := mk a

private theorem generating_agree (d : ℕ) : Agree (d + 2) generatingSeries (approximation d) := by
  intro n hn
  simp only [generatingSeries, coeff_mk, a]
  by_cases hnd : n ≤ d
  · exact approximation_stable hnd n (by omega)
  · exact (approximation_stable (by omega : d ≤ n) n hn).symm

theorem generating_equation : constantCoeff generatingSeries = 0 ∧
    coeff 1 generatingSeries = 1 ∧
    iterate generatingSeries 3 = (1 + X) * iterate generatingSeries 2 := by
  have hz : constantCoeff generatingSeries = 0 := by
    simpa only [coeff_zero_eq_constantCoeff, approximation, constantCoeff_X] using
      generating_agree 0 0 (by omega)
  have h1 : coeff 1 generatingSeries = 1 := by
    simpa only [approximation, coeff_one_X] using generating_agree 0 1 (by omega)
  refine ⟨hz, h1, ?_⟩
  have hs : generatingSeries = step generatingSeries := by
    ext n
    have ha := generating_agree (n + 1) n (by omega)
    have hb := step_contract (by omega : 1 < n + 2) hz (approximation_normal n).1
      h1 (approximation_normal n).2 (generating_agree n) n (by omega)
    exact ha.trans hb.symm
  dsimp [step] at hs
  linear_combination hs

theorem generating_unique {f : PowerSeries ℤ}
    (h0 : constantCoeff f = 0) (h1 : coeff 1 f = 1)
    (he : iterate f 3 = (1 + X) * iterate f 2) : f = generatingSeries :=
  unique h0 generating_equation.1 h1 generating_equation.2.1 he generating_equation.2.2

private theorem map_iterates {S : Type*} [CommRing S] (hom : R →+* S)
    {f : PowerSeries R} (hf : constantCoeff f = 0) (k : ℕ) :
    (iterate f k).map hom = iterate (f.map hom) k := by
  induction k with
  | zero => simp [iterate]
  | succ k ih =>
    calc
      (iterate f (k + 1)).map hom =
          ((iterate f k).map hom).subst (f.map hom) :=
        map_subst (.of_constantCoeff_zero hf) _
      _ = iterate (f.map hom) (k + 1) := by rw [ih]; rfl

private theorem mobius_mul (c : R) : mobius c * (1 - C c * X) = X := by
  have h : rescale c (mk 1) * (1 - C c * X) = (1 : PowerSeries R) := by
    simpa using congrArg (rescale c) (mk_one_mul_one_sub_eq_one R)
  simp only [mobius, mul_assoc, h, mul_one]

theorem mod_three_fixed :
    iterate (mobius (1 : ZMod 3)) 3 = (1 + X) * iterate (mobius 1) 2 := by
  rw [mobius_iterate, mobius_iterate]
  norm_num only [Nat.cast_ofNat, mul_one]
  rw [show (3 : ZMod 3) = 0 by decide]
  have hd : (1 - C (2 : ZMod 3) * X : PowerSeries (ZMod 3)) = 1 + X := by
    have hc : -C (2 : ZMod 3) = (1 : PowerSeries (ZMod 3)) := by
      rw [← map_neg, show -(2 : ZMod 3) = 1 by decide, map_one]
    linear_combination X * hc
  have hm := mobius_mul (2 : ZMod 3)
  rw [hd, mul_comm] at hm
  simpa [mobius] using hm.symm

theorem hanna_conjecture (n : ℕ) (hn : 1 ≤ n) : a n % 3 = 1 := by
  let hom := Int.castRingHom (ZMod 3)
  have hz : constantCoeff (generatingSeries.map hom) = 0 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
      generating_equation.1, map_zero]
  have h1 : coeff 1 (generatingSeries.map hom) = 1 := by
    rw [coeff_map, generating_equation.2.1, map_one]
  have hf : iterate (generatingSeries.map hom) 3 =
      (1 + X) * iterate (generatingSeries.map hom) 2 := by
    have h := congrArg (PowerSeries.map hom) generating_equation.2.2
    simpa [map_iterates hom generating_equation.1] using h
  have hm0 : constantCoeff (mobius (1 : ZMod 3)) = 0 := by simp [mobius]
  have hm1 : coeff 1 (mobius (1 : ZMod 3)) = 1 := by simp [mobius]
  have he := unique hz hm0 h1 hm1 hf mod_three_fixed
  have hb : coeff n (mobius (1 : ZMod 3)) = 1 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simp [mobius]
  have hc : (a n : ZMod 3) = 1 := by
    simpa [coeff_map, generatingSeries, hb, hom] using congrArg (coeff n) he
  exact (ZMod.intCast_eq_intCast_iff' (a n) 1 3).mp hc

#print axioms generating_equation
#print axioms generating_unique
#print axioms mod_three_fixed
#print axioms hanna_conjecture

end D5.S1.Recurrence.Invariants.TripleIterateShiftModThree
