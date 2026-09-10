/- GID: D5/S1/Recurrence/Parity/ThetaSelfCompositionModFour
   generality: G
   mirror-B: D5/B/S1/Recurrence/Parity/ThetaSelfCompositionModFour
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Triangular self-composition and square-zero perturbation prove Hanna A378581. -/

import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

open PowerSeries

namespace D5.S1.Recurrence.Parity.ThetaSelfCompositionModFour

variable {R : Type*} [CommRing R]

private def Agree (d : ℕ) (f g : PowerSeries R) : Prop :=
  ∀ n < d, coeff n f = coeff n g

private theorem agree_pow {d : ℕ} {f g : PowerSeries R}
    (h : Agree d f g) (k : ℕ) : Agree d (f ^ k) (g ^ k) := by
  have hd : X ^ d ∣ f - g := by
    simpa [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero] using h
  have hp := hd.trans (sub_dvd_pow_sub_pow f g k)
  simpa [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero] using hp

private theorem agree_X {d : ℕ} {f g : PowerSeries R}
    (h : Agree d f g) : Agree (d + 1) (X * f) (X * g) := by
  intro n hn
  cases n with
  | zero => simp
  | succ n => simpa using h n (by omega)

private theorem pow_low (g : PowerSeries R) {n k : ℕ} (h : n < k) :
    coeff n ((X * g) ^ k) = 0 := by
  simp [mul_pow, coeff_X_pow_mul', Nat.not_le.mpr h]

private theorem pow_top (g : PowerSeries R) (hg : constantCoeff g = 1) (n : ℕ) :
    coeff n ((X * g) ^ n) = 1 := by
  simp [mul_pow, coeff_X_pow_mul', hg]

-- The degree-n outer difference survives with multiplier one; all lower terms cancel.
private theorem triangular {d : ℕ} {f g : PowerSeries R}
    (hg : constantCoeff g = 1) (h : Agree d f g) {n : ℕ} (hn : n ≤ d) :
    coeff n (f.subst (X * f)) - coeff n (g.subst (X * g)) =
      coeff n f - coeff n g := by
  have hs : HasSubst (X * g) :=
    .of_constantCoeff_zero (show constantCoeff (X * g) = 0 by simp)
  have hi : coeff n (f.subst (X * f)) = coeff n (f.subst (X * g)) := by
    rw [coeff_subst' (.of_constantCoeff_zero
      (show constantCoeff (X * f) = 0 by simp)), coeff_subst' hs]
    exact finsum_congr fun k => by rw [agree_pow (agree_X h) k n (by omega)]
  rw [hi, ← map_sub, ← subst_sub hs, coeff_subst' hs]
  rw [finsum_eq_single _ n]
  · simp [pow_top g hg]
  · intro k hk
    by_cases hkn : k < n
    · simp [map_sub, h k (by omega)]
    · rw [pow_low g (by omega), smul_zero]

private noncomputable def step (t f : PowerSeries R) : PowerSeries R :=
  t + f - f.subst (X * f)

private theorem subst_constant (f g : PowerSeries R) :
    constantCoeff (f.subst (X * g)) = constantCoeff f := by
  rw [← coeff_zero_eq_constantCoeff, coeff_subst' (.of_constantCoeff_zero
    (show constantCoeff (X * g) = 0 by simp))]
  rw [finsum_eq_single _ 0]
  · simp
  · intro k hk
    rw [pow_low g (by omega), smul_zero]

private theorem step_constant (t f : PowerSeries R) :
    constantCoeff (step t f) = constantCoeff t := by
  simp [step, subst_constant]

private theorem step_agree (t : PowerSeries R) {d : ℕ} {f g : PowerSeries R}
    (hg : constantCoeff g = 1) (h : Agree d f g) :
    Agree (d + 1) (step t f) (step t g) := by
  intro n hn
  have ht := triangular hg h (by omega : n ≤ d)
  simp only [step, map_sub, map_add]
  linear_combination -ht

private theorem solution_unique (t : PowerSeries R) {f g : PowerSeries R}
    (hg : constantCoeff g = 1)
    (hf : f.subst (X * f) = t) (hgE : g.subst (X * g) = t) : f = g := by
  have h : ∀ d, Agree d f g := by
    intro d
    induction d with
    | zero => intro n hn; omega
    | succ d ih =>
      have hs := step_agree t hg ih
      simpa [step, hf, hgE] using hs
  ext n
  exact h (n + 1) n (by omega)

noncomputable def thetaSeries : PowerSeries ℤ :=
  mk fun n => if n = 0 then 1 else if IsSquare n then 2 else 0

theorem coeff_thetaSeries (n : ℕ) :
    coeff n thetaSeries = if n = 0 then 1 else if IsSquare n then 2 else 0 := by
  classical
  simp [thetaSeries]

private theorem theta_zero : constantCoeff thetaSeries = 1 := by
  simp [← coeff_zero_eq_constantCoeff, coeff_thetaSeries]

private noncomputable def approximation : ℕ → PowerSeries ℤ
  | 0 => 1
  | depth + 1 => step thetaSeries (approximation depth)

private theorem approximation_zero (depth : ℕ) : constantCoeff (approximation depth) = 1 := by
  cases depth with
  | zero => simp [approximation]
  | succ depth => rw [approximation, step_constant, theta_zero]

private theorem approximation_stable {depth stage : ℕ} (hle : depth ≤ stage) :
    Agree depth (approximation depth) (approximation stage) := by
  induction depth generalizing stage with
  | zero => intro n hn; omega
  | succ depth ih =>
    cases stage with
    | zero => omega
    | succ stage => exact step_agree _ (approximation_zero stage) (ih (by omega))

noncomputable def a (n : ℕ) : ℤ := coeff n (approximation (n + 1))

noncomputable def generatingSeries : PowerSeries ℤ := mk a

private theorem generating_agree (depth : ℕ) :
    Agree depth generatingSeries (approximation depth) := by
  intro n hn
  simpa only [generatingSeries, coeff_mk, a] using
    approximation_stable (by omega : n + 1 ≤ depth) n (by omega)

theorem generating_equation : constantCoeff generatingSeries = 1 ∧
    generatingSeries.subst (X * generatingSeries) = thetaSeries := by
  have hz : constantCoeff generatingSeries = 1 := by
    rw [← coeff_zero_eq_constantCoeff, generating_agree 1 0 (by omega),
      coeff_zero_eq_constantCoeff, approximation_zero]
  refine ⟨hz, ?_⟩
  have hfixed : generatingSeries = step thetaSeries generatingSeries := by
    ext n
    have hg := generating_agree (n + 2) n (by omega)
    have hs := step_agree thetaSeries (approximation_zero (n + 1))
      (generating_agree (n + 1)) n (by omega)
    exact hg.trans hs.symm
  dsimp [step] at hfixed
  linear_combination hfixed

theorem generating_unique (B : PowerSeries ℤ) (h0 : constantCoeff B = 1)
    (hB : B.subst (X * B) = thetaSeries) : B = generatingSeries :=
  (solution_unique thetaSeries h0 generating_equation.2 hB).symm

private theorem weighted_subst (c : R) (f u v : PowerSeries R)
    (hu : constantCoeff u = 0) (hv : constantCoeff v = 0)
    (h : C c * u = C c * v) : C c * f.subst u = C c * f.subst v := by
  have hp : ∀ k : ℕ, C c * u ^ k = C c * v ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        C c * u ^ (k + 1) = (C c * u ^ k) * u := by ring
        _ = (C c * v ^ k) * u := by rw [ih]
        _ = v ^ k * (C c * u) := by ring
        _ = v ^ k * (C c * v) := by rw [h]
        _ = C c * v ^ (k + 1) := by ring
  have hsu : HasSubst u := .of_constantCoeff_zero hu
  have hsv : HasSubst v := .of_constantCoeff_zero hv
  have hcu : (C c : PowerSeries R).subst u = C c := subst_C c
  have hcv : (C c : PowerSeries R).subst v = C c := subst_C c
  have hmu : (C c * f).subst u = C c * f.subst u := by rw [subst_mul hsu, hcu]
  have hmv : (C c * f).subst v = C c * f.subst v := by rw [subst_mul hsv, hcv]
  rw [← hmu, ← hmv]
  ext n
  rw [coeff_subst' hsu, coeff_subst' hsv]
  apply finsum_congr
  intro k
  have hc := congrArg (coeff n) (hp k)
  simp only [coeff_C_mul] at hc ⊢
  simp only [smul_eq_mul]
  linear_combination coeff k f * hc

private noncomputable def squareSeries : PowerSeries (ZMod 4) :=
  mk fun n => if n = 0 then 0 else if IsSquare n then 1 else 0

private theorem reduced_theta : thetaSeries.map (Int.castRingHom (ZMod 4)) =
    1 + C 2 * squareSeries := by
  classical
  ext n
  simp only [coeff_map, coeff_thetaSeries, map_add, coeff_C_mul, squareSeries, coeff_mk]
  by_cases hn : n = 0
  · simp [hn]
  · by_cases hs : IsSquare n <;> simp [hn, hs, coeff_one]

private theorem reduced_solution :
    (thetaSeries.map (Int.castRingHom (ZMod 4))).subst
      (X * thetaSeries.map (Int.castRingHom (ZMod 4))) =
        thetaSeries.map (Int.castRingHom (ZMod 4)) := by
  rw [reduced_theta]
  have hz : constantCoeff (X * (1 + C 2 * squareSeries)) = 0 := by simp
  have hs : HasSubst (X * (1 + C 2 * squareSeries)) := .of_constantCoeff_zero hz
  have hfour : (C (2 : ZMod 4) : PowerSeries (ZMod 4)) * C 2 = 0 := by
    rw [← map_mul, show (2 : ZMod 4) * 2 = 0 by decide, map_zero]
  have harg : C (2 : ZMod 4) * (X * (1 + C 2 * squareSeries)) = C 2 * X := by
    linear_combination X * squareSeries * hfour
  have hw := weighted_subst (2 : ZMod 4) squareSeries
    (X * (1 + C 2 * squareSeries)) X hz (by simp) harg
  rw [X_subst] at hw
  rw [subst_add hs, subst_mul hs, subst_C]
  have hone : (1 : PowerSeries (ZMod 4)).subst (X * (1 + C 2 * squareSeries)) = 1 := by
    simpa only [map_one] using (subst_C (a := X * (1 + C 2 * squareSeries)) (1 : ZMod 4))
  rw [hone]
  change 1 + C 2 * squareSeries.subst (X * (1 + C 2 * squareSeries)) = _
  rw [hw]

theorem mod_four_identity : generatingSeries.map (Int.castRingHom (ZMod 4)) =
    thetaSeries.map (Int.castRingHom (ZMod 4)) := by
  let hom := Int.castRingHom (ZMod 4)
  have he := congrArg (PowerSeries.map hom) generating_equation.2
  have hm : PowerSeries.map hom (generatingSeries.subst (X * generatingSeries)) =
      (generatingSeries.map hom).subst (PowerSeries.map hom (X * generatingSeries)) :=
    map_subst (.of_constantCoeff_zero
      (show constantCoeff (X * generatingSeries) = 0 by simp)) generatingSeries
  rw [map_mul, map_X] at hm
  rw [hm] at he
  apply solution_unique (thetaSeries.map hom) ?_ he reduced_solution
  rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_thetaSeries]
  simp

theorem hanna_conjecture (n : ℕ) (hn : 0 < n) :
    (a n % 4 = 2 ↔ IsSquare n) ∧ (a n % 4 = 0 ↔ ¬ IsSquare n) := by
  have hc := congrArg (coeff n) mod_four_identity
  simp only [coeff_map, generatingSeries, coeff_mk] at hc
  change (a n : ZMod 4) = ((coeff n thetaSeries : ℤ) : ZMod 4) at hc
  rw [coeff_thetaSeries, if_neg (by omega : n ≠ 0)] at hc
  by_cases hs : IsSquare n
  · rw [if_pos hs] at hc
    have ha : a n % 4 = 2 := (ZMod.intCast_eq_intCast_iff' (a n) 2 4).mp hc
    simp [hs, ha]
  · rw [if_neg hs] at hc
    have ha : a n % 4 = 0 := (ZMod.intCast_eq_intCast_iff' (a n) 0 4).mp hc
    simp [hs, ha]

#print axioms coeff_thetaSeries
#print axioms generating_equation
#print axioms generating_unique
#print axioms mod_four_identity
#print axioms hanna_conjecture

end D5.S1.Recurrence.Parity.ThetaSelfCompositionModFour
