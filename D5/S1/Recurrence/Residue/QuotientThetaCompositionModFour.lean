/- GID: D5/S1/Recurrence/Residue/QuotientThetaCompositionModFour
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/QuotientThetaCompositionModFour
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Inverse agreement and quotient triangularity prove Hanna A378580 modulo four. -/

import D5.S1.Recurrence.Parity.ThetaSelfCompositionModFour
import Mathlib.RingTheory.PowerSeries.Inverse

/-! The quotient equation and coefficient conjecture are recorded in
`Library/ArithSums/hanna2025a378580.md`. The theta series is the frozen
`ThetaSelfCompositionModFour.thetaSeries`; its integer product solution is
used only after coefficientwise reduction modulo four. -/

open PowerSeries
open D5.S1.Recurrence.Parity.ThetaSelfCompositionModFour (thetaSeries coeff_thetaSeries)

namespace D5.S1.Recurrence.Residue.QuotientThetaCompositionModFour

variable {R : Type*} [CommRing R]

private def Agree (d : ℕ) (f g : PowerSeries R) : Prop :=
  ∀ n < d, coeff n f = coeff n g

/-- Inverting constant-one series preserves agreement below any degree. -/
theorem inverse_agreement {d : ℕ} {f g : PowerSeries R}
    (hf : constantCoeff f = 1) (hg : constantCoeff g = 1)
    (h : ∀ n < d, coeff n f = coeff n g) :
    ∀ n < d, coeff n (invOfUnit f 1) = coeff n (invOfUnit g 1) := by
  have hd : X ^ d ∣ g - f := by
    apply X_pow_dvd_iff.mpr
    intro n hn
    simp [map_sub, h n hn]
  have hfi := invOfUnit_mul f 1 hf
  have hgi := mul_invOfUnit g 1 hg
  have he : invOfUnit f 1 - invOfUnit g 1 =
      invOfUnit f 1 * (g - f) * invOfUnit g 1 := by
    calc
      _ = invOfUnit f 1 * (g * invOfUnit g 1) -
          (invOfUnit f 1 * f) * invOfUnit g 1 := by rw [hfi, hgi]; ring
      _ = _ := by ring
  have hi := dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd (invOfUnit f 1))
    (invOfUnit g 1)
  rw [← he] at hi
  simpa [X_pow_dvd_iff, map_sub, sub_eq_zero] using hi

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
theorem quotient_triangular {d : ℕ} {f g : PowerSeries R}
    (hf : constantCoeff f = 1) (hg : constantCoeff g = 1)
    (h : ∀ k < d, coeff k f = coeff k g) {n : ℕ} (hn : n ≤ d) :
    coeff n (f.subst (X * invOfUnit f 1)) - coeff n (g.subst (X * invOfUnit g 1)) =
      coeff n f - coeff n g := by
  have hs : HasSubst (X * invOfUnit g 1) :=
    .of_constantCoeff_zero (show constantCoeff (X * invOfUnit g 1) = 0 by simp)
  have hi : coeff n (f.subst (X * invOfUnit f 1)) = coeff n (f.subst (X * invOfUnit g 1)) := by
    rw [coeff_subst' (.of_constantCoeff_zero
      (show constantCoeff (X * invOfUnit f 1) = 0 by simp)), coeff_subst' hs]
    exact finsum_congr fun k => by
      rw [agree_pow (agree_X (inverse_agreement hf hg h)) k n (by omega)]
  rw [hi, ← map_sub, ← subst_sub hs, coeff_subst' hs]
  rw [finsum_eq_single _ n]
  · simp [pow_top (invOfUnit g 1) (by simp)]
  · intro k hk
    by_cases hkn : k < n
    · simp [map_sub, h k (by omega)]
    · rw [pow_low (invOfUnit g 1) (by omega), smul_zero]

private noncomputable def step (t f : PowerSeries R) : PowerSeries R :=
  t + f - f.subst (X * invOfUnit f 1)

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
    (hf : constantCoeff f = 1) (hg : constantCoeff g = 1) (h : Agree d f g) :
    Agree (d + 1) (step t f) (step t g) := by
  intro n hn
  have ht := quotient_triangular hf hg h (by omega : n ≤ d)
  simp only [step, map_sub, map_add]
  linear_combination -ht

private theorem solution_unique (t : PowerSeries R) {f g : PowerSeries R}
    (hf0 : constantCoeff f = 1) (hg : constantCoeff g = 1)
    (hf : f.subst (X * invOfUnit f 1) = t)
    (hgE : g.subst (X * invOfUnit g 1) = t) : f = g := by
  have h : ∀ d, Agree d f g := by
    intro d
    induction d with
    | zero => intro n hn; omega
    | succ d ih =>
      have hs := step_agree t hf0 hg ih
      simpa [step, hf, hgE] using hs
  ext n
  exact h (n + 1) n (by omega)

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
    | succ stage =>
      exact step_agree _ (approximation_zero depth) (approximation_zero stage) (ih (by omega))

noncomputable def a (n : ℕ) : ℤ := coeff n (approximation (n + 1))

noncomputable def generatingSeries : PowerSeries ℤ := mk a

private theorem generating_agree (depth : ℕ) :
    Agree depth generatingSeries (approximation depth) := by
  intro n hn
  simpa only [generatingSeries, coeff_mk, a] using
    approximation_stable (by omega : n + 1 ≤ depth) n (by omega)

theorem generating_equation : constantCoeff generatingSeries = 1 ∧
    generatingSeries.subst (X * invOfUnit generatingSeries 1) = thetaSeries := by
  have hz : constantCoeff generatingSeries = 1 := by
    rw [← coeff_zero_eq_constantCoeff, generating_agree 1 0 (by omega),
      coeff_zero_eq_constantCoeff, approximation_zero]
  refine ⟨hz, ?_⟩
  have hfixed : generatingSeries = step thetaSeries generatingSeries := by
    ext n
    have hg := generating_agree (n + 2) n (by omega)
    have hs := step_agree thetaSeries hz (approximation_zero (n + 1))
      (generating_agree (n + 1)) n (by omega)
    exact hg.trans hs.symm
  dsimp [step] at hfixed
  linear_combination hfixed

theorem generating_unique (B : PowerSeries ℤ) (h0 : constantCoeff B = 1)
    (hB : B.subst (X * invOfUnit B 1) = thetaSeries) : B = generatingSeries :=
  (solution_unique thetaSeries generating_equation.1 h0 generating_equation.2 hB).symm

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

private theorem reduced_inverse :
    invOfUnit (thetaSeries.map (Int.castRingHom (ZMod 4))) 1 =
      thetaSeries.map (Int.castRingHom (ZMod 4)) := by
  let T := thetaSeries.map (Int.castRingHom (ZMod 4))
  have hz : constantCoeff T = 1 := by
    simp [T, ← coeff_zero_eq_constantCoeff, coeff_thetaSeries]
  have hsq : T * T = 1 := by
    dsimp [T]
    rw [reduced_theta]
    have hfour : (C (2 : ZMod 4) : PowerSeries (ZMod 4)) * C 2 = 0 := by
      rw [← map_mul, show (2 : ZMod 4) * 2 = 0 by decide, map_zero]
    have htwo : (C (2 : ZMod 4) : PowerSeries (ZMod 4)) + C 2 = 0 := by
      rw [← map_add, show (2 : ZMod 4) + 2 = 0 by decide, map_zero]
    linear_combination squareSeries ^ 2 * hfour + squareSeries * htwo
  calc
    invOfUnit T 1 = invOfUnit T 1 * (T * T) := by rw [hsq, mul_one]
    _ = T := by rw [← mul_assoc, invOfUnit_mul T 1 hz, one_mul]

private theorem reduced_solution :
    (thetaSeries.map (Int.castRingHom (ZMod 4))).subst
      (X * invOfUnit (thetaSeries.map (Int.castRingHom (ZMod 4))) 1) =
        thetaSeries.map (Int.castRingHom (ZMod 4)) := by
  rw [reduced_inverse]
  have he := congrArg (PowerSeries.map (Int.castRingHom (ZMod 4)))
    D5.S1.Recurrence.Parity.ThetaSelfCompositionModFour.generating_equation.2
  have hm : PowerSeries.map (Int.castRingHom (ZMod 4))
      (D5.S1.Recurrence.Parity.ThetaSelfCompositionModFour.generatingSeries.subst
        (X * D5.S1.Recurrence.Parity.ThetaSelfCompositionModFour.generatingSeries)) =
      (D5.S1.Recurrence.Parity.ThetaSelfCompositionModFour.generatingSeries.map
        (Int.castRingHom (ZMod 4))).subst
        (PowerSeries.map (Int.castRingHom (ZMod 4))
          (X * D5.S1.Recurrence.Parity.ThetaSelfCompositionModFour.generatingSeries)) :=
    map_subst (.of_constantCoeff_zero
      (show constantCoeff
        (X * D5.S1.Recurrence.Parity.ThetaSelfCompositionModFour.generatingSeries) = 0 by simp)) _
  rw [hm, map_mul, map_X,
    D5.S1.Recurrence.Parity.ThetaSelfCompositionModFour.mod_four_identity] at he
  exact he

private theorem map_inverse {S : Type*} [CommRing S] (hom : R →+* S)
    (f : PowerSeries R) (hf : constantCoeff f = 1) :
    (invOfUnit f 1).map hom = invOfUnit (f.map hom) 1 := by
  have hz : constantCoeff (f.map hom) = 1 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff, hf, map_one]
  apply (isUnit_iff_constantCoeff.mpr (hz ▸ isUnit_one)).mul_left_cancel
  rw [mul_invOfUnit _ 1 hz, ← map_mul, mul_invOfUnit _ 1 hf, map_one]

theorem mod_four_identity : generatingSeries.map (Int.castRingHom (ZMod 4)) =
    thetaSeries.map (Int.castRingHom (ZMod 4)) := by
  let hom := Int.castRingHom (ZMod 4)
  have he := congrArg (PowerSeries.map hom) generating_equation.2
  have hm : PowerSeries.map hom
      (generatingSeries.subst (X * invOfUnit generatingSeries 1)) =
      (generatingSeries.map hom).subst
        (PowerSeries.map hom (X * invOfUnit generatingSeries 1)) :=
    map_subst (.of_constantCoeff_zero
      (show constantCoeff (X * invOfUnit generatingSeries 1) = 0 by simp)) _
  rw [hm, map_mul, map_X, map_inverse hom generatingSeries generating_equation.1] at he
  apply solution_unique (thetaSeries.map hom) ?_ ?_ he reduced_solution
  · rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
      generating_equation.1, map_one]
  · rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_thetaSeries]
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

#print axioms inverse_agreement
#print axioms quotient_triangular
#print axioms a
#print axioms generatingSeries
#print axioms generating_equation
#print axioms generating_unique
#print axioms mod_four_identity
#print axioms hanna_conjecture

end D5.S1.Recurrence.Residue.QuotientThetaCompositionModFour
