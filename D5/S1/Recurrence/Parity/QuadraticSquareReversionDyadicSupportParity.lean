/- GID: D5/S1/Recurrence/Parity/QuadraticSquareReversionDyadicSupportParity
   generality: I
   mirror-B: D5/B/S1/Recurrence/Parity/QuadraticSquareReversionDyadicSupportParity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Square-denominator reversion and characteristic-two transport prove Hanna parity. -/

import D5.S1.Recurrence.Invariants.QuadraticReversionDyadicSupportParity

open PowerSeries

namespace D5.S1.Recurrence.Parity.QuadraticSquareReversionDyadicSupportParity

variable {R : Type*} [CommRing R]

private def Agree (d : ℕ) (f g : PowerSeries R) : Prop :=
  ∀ n < d, coeff n f = coeff n g

private theorem agree_iff (d : ℕ) (f g : PowerSeries R) :
    Agree d f g ↔ (X : PowerSeries R) ^ d ∣ f - g := by
  simp [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]

private theorem agree_pow {d : ℕ} {f g : PowerSeries R}
    (h : Agree d f g) (k : ℕ) : Agree d (f ^ k) (g ^ k) :=
  (agree_iff _ _ _).mpr (((agree_iff _ _ _).mp h).trans (sub_dvd_pow_sub_pow f g k))

private theorem pow_low {f : PowerSeries R} (h : constantCoeff f = 0)
    {n k : ℕ} (hn : n < k) : coeff n (f ^ k) = 0 :=
  X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (X_dvd_iff.mpr h) k) n hn

private theorem pow_diag {f : PowerSeries R} (h0 : constantCoeff f = 0)
    (h1 : coeff 1 f = 1) (n : ℕ) : coeff n (f ^ n) = 1 := by
  obtain ⟨u, rfl⟩ := X_dvd_iff.mpr h0
  have hu : constantCoeff u = 1 := by simpa using h1
  simp [mul_pow, coeff_X_pow_mul', hu]

private theorem subst_inner_agree {d : ℕ} {u v : PowerSeries R}
    (hu : constantCoeff u = 0) (hv : constantCoeff v = 0)
    (h : Agree d u v) (f : PowerSeries R) : Agree d (f.subst u) (f.subst v) := by
  intro n hn
  rw [coeff_subst' (.of_constantCoeff_zero hu), coeff_subst' (.of_constantCoeff_zero hv)]
  exact finsum_congr fun k => by rw [agree_pow h k n hn]

private theorem subst_first_difference {d : ℕ} {f g u : PowerSeries R}
    (h0 : constantCoeff u = 0) (h1 : coeff 1 u = 1) (h : Agree d f g)
    (n : ℕ) (hn : n < d + 1) :
    coeff n ((f - g).subst u) = coeff n (f - g) := by
  rw [coeff_subst' (.of_constantCoeff_zero h0), finsum_eq_single _ n]
  · rw [pow_diag h0 h1, smul_eq_mul, mul_one]
  · intro k hk
    by_cases hkn : k < n
    · have hz : coeff k (f - g) = 0 := by rw [map_sub, h k (by omega), sub_self]
      rw [hz, zero_smul]
    · rw [pow_low h0 (by omega : n < k), smul_zero]

private noncomputable def reciprocal (f : PowerSeries R) : PowerSeries R :=
  invOfUnit (1 - f ^ 2) 1

private theorem reciprocal_mul {f : PowerSeries R} (hf : constantCoeff f = 0) :
    reciprocal f * (1 - f ^ 2) = 1 := invOfUnit_mul _ _ (by simp [hf])

private noncomputable def argument (f : PowerSeries R) : PowerSeries R :=
  X - f ^ 2 * reciprocal f

private theorem argument_zero {f : PowerSeries R} (hf : constantCoeff f = 0) :
    constantCoeff (argument f) = 0 := by simp [argument, hf]

private theorem argument_one {f : PowerSeries R} (hf : constantCoeff f = 0) :
    coeff 1 (argument f) = 1 := by
  have hd : X ^ 2 ∣ f ^ 2 * reciprocal f :=
    dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hf) 2) _
  rw [argument, map_sub, X_pow_dvd_iff.mp hd 1 (by omega)]
  simp

-- The difference gains a factor X because f^2-g^2=(f-g)(f+g).
private theorem argument_agree {d : ℕ} {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (h : Agree d f g) : Agree (d + 1) (argument f) (argument g) := by
  have he : f ^ 2 * reciprocal f - g ^ 2 * reciprocal g =
      (f - g) * (f + g) * (reciprocal f * reciprocal g) := by
    have hf' := reciprocal_mul hf
    have hg' := reciprocal_mul hg
    linear_combination g ^ 2 * reciprocal g * hf' - f ^ 2 * reciprocal f * hg'
  have hz : X ∣ f + g := X_dvd_iff.mpr (by simp [hf, hg])
  have hm := mul_dvd_mul ((agree_iff _ _ _).mp h) hz
  rw [← pow_succ] at hm
  apply (agree_iff _ _ _).mpr
  have hd := dvd_mul_of_dvd_left hm (reciprocal f * reciprocal g)
  rw [← he] at hd
  simpa only [argument, sub_sub_sub_cancel_left, neg_sub] using dvd_neg.mpr hd

private noncomputable def step (f : PowerSeries R) : PowerSeries R :=
  f + X - f.subst (argument f)

private theorem step_zero {f : PowerSeries R} (hf : constantCoeff f = 0) :
    constantCoeff (step f) = 0 := by
  have hz : constantCoeff (f.subst (argument f)) = 0 :=
    constantCoeff_subst_eq_zero (argument_zero hf) _ hf
  simp only [step, map_sub, map_add, hf, constantCoeff_X, hz, add_zero, sub_zero]

private theorem step_agree {d : ℕ} {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (h : Agree d f g) : Agree (d + 1) (step f) (step g) := by
  intro n hn
  have hi := subst_inner_agree (argument_zero hf) (argument_zero hg)
    (argument_agree hf hg h) f n hn
  have ho := subst_first_difference (argument_zero hg) (argument_one hg) h n hn
  rw [subst_sub (.of_constantCoeff_zero (argument_zero hg)), map_sub, map_sub] at ho
  simp only [step, map_sub, map_add]
  rw [hi]
  linear_combination -ho

private theorem solution_unique {f g : PowerSeries R}
    (hf0 : constantCoeff f = 0) (hg0 : constantCoeff g = 0)
    (hf : f.subst (argument f) = X) (hg : g.subst (argument g) = X) : f = g := by
  have hsf : step f = f := by simp [step, hf]
  have hsg : step g = g := by simp [step, hg]
  have hall : ∀ d, Agree d f g := by
    intro d
    induction d with
    | zero => intro n hn; omega
    | succ d ih => simpa only [hsf, hsg] using step_agree hf0 hg0 ih
  ext n
  exact hall (n + 1) n (by omega)

private noncomputable def approximation : ℕ → PowerSeries R
  | 0 => 0
  | k + 1 => step (approximation k)

private theorem approximation_zero (n : ℕ) :
    constantCoeff (approximation (R := R) n) = 0 := by
  induction n with
  | zero => simp [approximation]
  | succ n ih => exact step_zero ih

private theorem approximation_stable {d k : ℕ} (h : d ≤ k) :
    Agree d (approximation (R := R) d) (approximation k) := by
  induction d generalizing k with
  | zero => intro n hn; omega
  | succ d ih =>
    cases k with
    | zero => omega
    | succ k => exact step_agree (approximation_zero _) (approximation_zero _) (ih (by omega))

private noncomputable def solution : PowerSeries R :=
  mk fun n => coeff n (approximation (n + 1))

private theorem solution_agree (d : ℕ) :
    Agree d (solution (R := R)) (approximation d) := by
  intro n hn
  simpa only [solution, coeff_mk] using
    approximation_stable (R := R) (by omega : n + 1 ≤ d) n (by omega)

private theorem solution_zero : constantCoeff (solution (R := R)) = 0 := by
  have h := solution_agree (R := R) 1 0 (by omega)
  simpa [coeff_zero_eq_constantCoeff, approximation_zero] using h

private theorem solution_equation :
    (solution (R := R)).subst (argument (solution (R := R))) = X := by
  have hf : (solution (R := R)) = step (solution (R := R)) := by
    ext n
    have hg := solution_agree (R := R) (n + 2) n (by omega)
    have hs := step_agree (solution_zero (R := R)) (approximation_zero (R := R) (n + 1))
      (solution_agree (R := R) (n + 1)) n (by omega)
    exact hg.trans hs.symm
  dsimp [step] at hf
  linear_combination hf

private theorem solution_one : coeff 1 (solution (R := R)) = 1 := by
  have h := solution_agree (R := R) 2 1 (by omega)
  have ha : approximation (R := R) 1 = X := by
    have hz : (0 : PowerSeries R).subst (argument (0 : PowerSeries R)) = 0 := by
      simpa only [map_zero] using (subst_C (a := argument (0 : PowerSeries R)) (0 : R))
    simp [approximation, step, hz]
  change coeff 1 solution = coeff 1 (step (approximation 1)) at h
  rw [ha, step, subst_X (.of_constantCoeff_zero (argument_zero (by simp))),
    map_sub, map_add, argument_one (by simp)] at h
  simpa using h

noncomputable def generatingSeries : PowerSeries ℤ := solution

noncomputable def a (n : ℕ) : ℤ := coeff n generatingSeries

theorem generating_equation : constantCoeff generatingSeries = 0 ∧
    coeff 1 generatingSeries = 1 ∧
    generatingSeries.subst
      (X - generatingSeries ^ 2 * invOfUnit (1 - generatingSeries ^ 2) 1) = X :=
  ⟨solution_zero, solution_one, solution_equation⟩

theorem generating_unique (B : PowerSeries ℤ) (h0 : constantCoeff B = 0)
    (_h1 : coeff 1 B = 1)
    (hB : B.subst (X - B ^ 2 * invOfUnit (1 - B ^ 2) 1) = X) :
    B = generatingSeries := solution_unique h0 solution_zero hB solution_equation

private theorem map_argument {S : Type*} [CommRing S] (hom : R →+* S)
    (f : PowerSeries R) (hf : constantCoeff f = 0) :
    (argument f).map hom = argument (f.map hom) := by
  have hz : constantCoeff (f.map hom) = 0 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff, hf, map_zero]
  have hv : (reciprocal f).map hom = reciprocal (f.map hom) := by
    have hu : IsUnit (1 - (f.map hom) ^ 2) := by
      rw [isUnit_iff_constantCoeff]
      simp [hz]
    apply hu.mul_right_cancel
    rw [reciprocal_mul hz]
    simpa only [map_mul, map_sub, map_one, map_pow] using
      congrArg (PowerSeries.map hom) (reciprocal_mul hf)
  simp only [argument, map_sub, map_X, map_pow, map_mul, hv]

private instance char_two : CharP (PowerSeries (ZMod 2)) 2 :=
  CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (by
    simpa only [map_ofNat, map_zero] using
      congrArg (C (R := ZMod 2)) (show (2 : ZMod 2) = 0 by decide))

-- In characteristic two the two unit denominators have the same square.
private theorem argument_char_two (f : PowerSeries (ZMod 2))
    (hf : constantCoeff f = 0) :
    argument f = X - (f * invOfUnit (1 - f) 1) ^ 2 := by
  have hd : 1 - f ^ 2 = (1 - f) ^ 2 := by
    simp only [CharTwo.sub_eq_add, CharTwo.add_sq, one_pow]
  have hv : reciprocal f = (invOfUnit (1 - f) 1) ^ 2 := by
    have hu : IsUnit (1 - f ^ 2) := by
      rw [isUnit_iff_constantCoeff]
      simp [hf]
    apply hu.mul_right_cancel
    rw [reciprocal_mul hf, hd, ← mul_pow, invOfUnit_mul _ _ (by simp [hf]), one_pow]
  simp only [argument, hv, mul_pow]

theorem mod_two_identity :
    generatingSeries.map (Int.castRingHom (ZMod 2)) =
      Invariants.QuadraticReversionDyadicSupportParity.lacunarySeries := by
  let hom := Int.castRingHom (ZMod 2)
  have hz : constantCoeff (generatingSeries.map hom) = 0 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
      generating_equation.1, map_zero]
  have he : (generatingSeries.map hom).subst (argument (generatingSeries.map hom)) = X := by
    have hm := congrArg (PowerSeries.map hom) generating_equation.2.2
    have hs : PowerSeries.map hom (generatingSeries.subst (argument generatingSeries)) =
        (generatingSeries.map hom).subst ((argument generatingSeries).map hom) :=
      map_subst (.of_constantCoeff_zero (argument_zero generating_equation.1)) _
    change PowerSeries.map hom (generatingSeries.subst (argument generatingSeries)) =
      PowerSeries.map hom X at hm
    rw [hs, map_X, map_argument hom generatingSeries generating_equation.1] at hm
    exact hm
  have hl : constantCoeff Invariants.QuadraticReversionDyadicSupportParity.lacunarySeries = 0 := by
    have hc := congrArg constantCoeff
      Invariants.QuadraticReversionDyadicSupportParity.lacunary_quadratic
    simpa using hc
  apply solution_unique hz hl he
  rw [argument_char_two _ hl]
  exact Invariants.QuadraticReversionDyadicSupportParity.lacunary_reversion

theorem hanna_conjecture (n : ℕ) (_hn : 1 ≤ n) :
    Odd (a n) ↔ ∃ m : ℕ, n + 2 = 3 * 2 ^ m ∨ n + 2 = 4 * 2 ^ m := by
  classical
  have hc := congrArg (coeff n) mod_two_identity
  change (a n : ZMod 2) =
    coeff n Invariants.QuadraticReversionDyadicSupportParity.lacunarySeries at hc
  rw [← ZMod.intCast_eq_one_iff_odd, hc]
  simp only [Invariants.QuadraticReversionDyadicSupportParity.lacunarySeries, coeff_mk]
  split_ifs <;> simp_all

#print axioms generating_equation
#print axioms generating_unique
#print axioms mod_two_identity
#print axioms hanna_conjecture

end D5.S1.Recurrence.Parity.QuadraticSquareReversionDyadicSupportParity
