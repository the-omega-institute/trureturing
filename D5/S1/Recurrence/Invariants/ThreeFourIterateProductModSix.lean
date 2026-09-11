/- GID: D5/S1/Recurrence/Invariants/ThreeFourIterateProductModSix
   generality: I
   mirror-B: D5/B/S1/Recurrence/Invariants/ThreeFourIterateProductModSix
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Degree contraction and a geometric fixed point prove Hanna A396797 modulo six. -/

import D5.S1.Recurrence.Invariants.CompositionalIterateCongruence

open PowerSeries
open D5.S1.Recurrence.Invariants.CompositionalIterateCongruence
  (iterate mobius mobius_iterate)

namespace D5.S1.Recurrence.Invariants.ThreeFourIterateProductModSix

variable {R : Type*} [CommRing R]

private theorem coeff_eq_of_dvd {f g : PowerSeries R} {d n : ℕ}
    (h : (X : PowerSeries R) ^ d ∣ f - g) (hn : n < d) : coeff n f = coeff n g := by
  simpa only [map_sub, sub_eq_zero] using X_pow_dvd_iff.mp h n hn

private theorem subst_congr {f g u v : PowerSeries R} {d : ℕ}
    (hu : constantCoeff u = 0) (hv : constantCoeff v = 0)
    (hf : (X : PowerSeries R) ^ d ∣ f - g)
    (huv : (X : PowerSeries R) ^ d ∣ u - v) :
    (X : PowerSeries R) ^ d ∣ f.subst u - g.subst v := by
  apply X_pow_dvd_iff.mpr
  intro n hn
  simp only [map_sub, sub_eq_zero]
  rw [coeff_subst' (.of_constantCoeff_zero hu), coeff_subst' (.of_constantCoeff_zero hv)]
  apply finsum_congr
  intro k
  by_cases hk : k < d
  · rw [coeff_eq_of_dvd hf hk,
      coeff_eq_of_dvd (huv.trans (sub_dvd_pow_sub_pow u v k)) hn]
  · have vanishes (w : PowerSeries R) (hw : constantCoeff w = 0) :
        coeff n (w ^ k) = 0 :=
      X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hw) k) n (by omega)
    rw [vanishes u hu, vanishes v hv, smul_zero, smul_zero]

private theorem iterate_constant (f : PowerSeries R) (h : constantCoeff f = 0) (k : ℕ) :
    constantCoeff (iterate f k) = 0 := by
  induction k with
  | zero => simp [iterate]
  | succ k ih => exact constantCoeff_subst_eq_zero h _ ih

private theorem iterate_congr {f g : PowerSeries R} {d : ℕ}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (h : (X : PowerSeries R) ^ d ∣ f - g) (k : ℕ) :
    (X : PowerSeries R) ^ d ∣ iterate f k - iterate g k := by
  induction k with
  | zero => simp [iterate]
  | succ k ih => exact subst_congr hf hg ih h

-- Each factor has zero constant term, so the product gains one degree of agreement.
private theorem product_contract {f g : PowerSeries R} {d : ℕ}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (h : (X : PowerSeries R) ^ d ∣ f - g) (p q : ℕ) :
    (X : PowerSeries R) ^ (d + 1) ∣
      (X + iterate f p * iterate f q) - (X + iterate g p * iterate g q) := by
  have hp := mul_dvd_mul (iterate_congr hf hg h p)
    (X_dvd_iff.mpr (iterate_constant f hf q))
  have hq := mul_dvd_mul (iterate_congr hf hg h q)
    (X_dvd_iff.mpr (iterate_constant g hg p))
  rw [← pow_succ] at hp hq
  convert dvd_add hp hq using 1
  ring

private noncomputable def step (f : PowerSeries R) : PowerSeries R :=
  X + iterate f 3 * iterate f 4

private theorem step_constant {f : PowerSeries R} (h : constantCoeff f = 0) :
    constantCoeff (step f) = 0 := by
  simp [step, iterate_constant f h]

private theorem unique {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (hff : f = step f) (hgg : g = step g) : f = g := by
  have hd : ∀ d : ℕ, (X : PowerSeries R) ^ d ∣ f - g := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      have h : (X : PowerSeries R) ^ (d + 1) ∣ step f - step g :=
        product_contract hf hg ih 3 4
      simpa only [← hff, ← hgg] using h
  ext n
  exact coeff_eq_of_dvd (hd (n + 1)) (Nat.lt_succ_self n)

private noncomputable def approx (d : ℕ) : PowerSeries R := step^[d] 0

private theorem approx_succ (d : ℕ) :
    approx (R := R) (d + 1) = step (approx d) :=
  Function.iterate_succ_apply' step d 0

private theorem approx_constant (d : ℕ) : constantCoeff (approx (R := R) d) = 0 := by
  induction d with
  | zero => simp [approx]
  | succ d ih => rw [approx_succ]; exact step_constant ih

private theorem approx_stable {d e : ℕ} (h : d ≤ e) :
    (X : PowerSeries R) ^ d ∣ approx d - approx e := by
  induction d generalizing e with
  | zero => simp
  | succ d ih =>
    cases e with
    | zero => omega
    | succ e =>
      rw [approx_succ, approx_succ]
      exact product_contract (approx_constant d) (approx_constant e) (ih (by omega)) 3 4

noncomputable def a (n : ℕ) : ℤ := coeff n (approx (n + 1))

noncomputable def generatingSeries : PowerSeries ℤ := mk a

private theorem generating_approx (d : ℕ) :
    (X : PowerSeries ℤ) ^ d ∣ generatingSeries - approx d := by
  apply X_pow_dvd_iff.mpr
  intro n hn
  simp only [map_sub, sub_eq_zero, generatingSeries, coeff_mk, a]
  exact coeff_eq_of_dvd (approx_stable (by omega : n + 1 ≤ d)) (Nat.lt_succ_self n)

theorem generating_equation : constantCoeff generatingSeries = 0 ∧
    generatingSeries = X + iterate generatingSeries 3 * iterate generatingSeries 4 := by
  have hz : constantCoeff generatingSeries = 0 := by
    rw [← coeff_zero_eq_constantCoeff,
      coeff_eq_of_dvd (generating_approx 1) (by omega : 0 < 1), coeff_zero_eq_constantCoeff]
    exact approx_constant 1
  refine ⟨hz, ?_⟩
  ext n
  have h := coeff_eq_of_dvd (generating_approx (n + 2)) (by omega : n < n + 2)
  rw [approx_succ] at h
  exact h.trans (coeff_eq_of_dvd
    (product_contract hz (approx_constant (n + 1)) (generating_approx (n + 1)) 3 4)
    (by omega : n < n + 1 + 1)).symm

theorem generating_unique {B : PowerSeries ℤ} (h0 : constantCoeff B = 0)
    (hB : B = X + iterate B 3 * iterate B 4) : B = generatingSeries :=
  unique h0 generating_equation.1 hB generating_equation.2

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

private theorem denominator_product :
    (1 - C (3 : ZMod 6) * X) * (1 - C 4 * X) = (1 - X : PowerSeries (ZMod 6)) := by
  have hadd : C (3 : ZMod 6) + C 4 = (1 : PowerSeries (ZMod 6)) := by
    rw [← map_add, show (3 : ZMod 6) + 4 = 1 by decide, map_one]
  have hmul : C (3 : ZMod 6) * C 4 = (0 : PowerSeries (ZMod 6)) := by
    rw [← map_mul, show (3 : ZMod 6) * 4 = 0 by decide, map_zero]
  linear_combination -X * hadd + X ^ 2 * hmul

theorem mod_six_fixed :
    mobius (1 : ZMod 6) = X + iterate (mobius 1) 3 * iterate (mobius 1) 4 := by
  rw [mobius_iterate, mobius_iterate]
  norm_num only [Nat.cast_ofNat, mul_one]
  have hu : IsUnit (1 - X : PowerSeries (ZMod 6)) := by
    rw [isUnit_iff_constantCoeff]
    simp
  apply hu.mul_right_cancel
  have hm : mobius (1 : ZMod 6) * (1 - X) = X := by simpa using mobius_mul (1 : ZMod 6)
  rw [hm, add_mul, ← denominator_product, mul_mul_mul_comm, mobius_mul, mobius_mul,
    denominator_product]
  ring

theorem hanna_conjecture (n : ℕ) (hn : 1 ≤ n) : a n % 6 = 1 := by
  let hom := Int.castRingHom (ZMod 6)
  have hz : constantCoeff (generatingSeries.map hom) = 0 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
      generating_equation.1, map_zero]
  have hf : generatingSeries.map hom = step (generatingSeries.map hom) := by
    have h := congrArg (PowerSeries.map hom) generating_equation.2
    simpa [step, map_iterates hom generating_equation.1] using h
  have hm : constantCoeff (mobius (1 : ZMod 6)) = 0 := by simp [mobius]
  have he := unique hz hm hf mod_six_fixed
  have hb : coeff n (mobius (1 : ZMod 6)) = 1 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simp [mobius]
  have hc : (a n : ZMod 6) = 1 := by
    simpa [coeff_map, generatingSeries, hb, hom] using congrArg (coeff n) he
  exact (ZMod.intCast_eq_intCast_iff' (a n) 1 6).mp hc

#print axioms generating_equation
#print axioms generating_unique
#print axioms mod_six_fixed
#print axioms hanna_conjecture

end D5.S1.Recurrence.Invariants.ThreeFourIterateProductModSix
