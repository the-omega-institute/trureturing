/- GID: D5/S1/Recurrence/Invariants/HannaCompositionSquareModNine
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/HannaCompositionSquareModNine
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: An integral unit factor lifts Hanna's square coefficients to modulo nine. -/

/-
admission_basis: open-problem-resolution (#21670, #21671; Proved)
escape_witness: none
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22693.
proof_shape: FormulaFour.claimFour: not-applicable(definition); consumers: FormulaFour.resultFour
proof_shape: FormulaFour.resultFour: content; consumers: settling conclusion
proof_shape: IsGF: not-applicable(definition); consumers: FormulaFour.claimFour,
FormulaFour.resultFour, claim, rational_identification, rational_spec, result
proof_shape: claim: not-applicable(definition); consumers: result
proof_shape: exists_integral: bind-only; consumers: integralSeries, integral_spec
proof_shape: inner: not-applicable(definition); consumers: inner_agree, inner_order, inner_zero,
integral_mod_nine, map_residual, rational_identification, residual, residual_agree,
residual_base, residual_even, residual_top
proof_shape: inner_agree: bind-only; consumers: residual_agree, residual_top
proof_shape: inner_order: bind-only; consumers: residual_agree, residual_top
proof_shape: inner_zero: bind-only; consumers: integral_mod_nine, map_residual, residual_agree,
residual_base, residual_top
proof_shape: integralSeries: not-applicable(definition); consumers: FormulaFour.resultFour,
integral_mod_nine, integral_spec, rational_identification, rational_spec, result
proof_shape: integral_mod_nine: bind-only; consumers: result
proof_shape: integral_spec: bind-only; consumers: integral_mod_nine, rational_identification,
rational_spec
proof_shape: map_residual: bind-only; consumers: rational_identification, rational_spec,
residual_even
proof_shape: rational_identification: content; consumers: FormulaFour.resultFour, result
proof_shape: rational_spec: bind-only; consumers: FormulaFour.resultFour,
rational_identification, result
proof_shape: residual: not-applicable(definition); consumers: exists_integral, integralSeries,
integral_mod_nine, integral_spec, map_residual, rational_identification, rational_spec,
residual_agree, residual_base, residual_even, residual_top, solution_unique
proof_shape: residual_agree: bind-only; consumers: exists_integral
proof_shape: residual_base: bind-only; consumers: exists_integral
proof_shape: residual_even: bind-only; consumers: exists_integral
proof_shape: residual_top: bind-only; consumers: exists_integral, solution_unique
proof_shape: result: content; consumers: settling conclusion
proof_shape: solution_unique: content; consumers: rational_identification
proof_shape: tail_composition_agree: bind-only; consumers: residual_top
The source predicates retain the normalized rational-series equations.
Proofs apply the original coefficient-agreement and triangular-lifting owners.
-/

import D5.S1.Recurrence.Invariants.CompositionalIterateCongruence
import D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity
import D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality
import D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction
import D5.S1.Recurrence.Invariants.HannaTripleSquareFrobeniusModThree

open PowerSeries

namespace D5.S1.Recurrence.Invariants.HannaCompositionSquareModNine

def IsGF (A : PowerSeries ℚ) : Prop :=
  constantCoeff A = 0 ∧ coeff 1 A = 1 ∧
    A.subst (X ^ 2 + 2 * X ^ 3 + 2 * A ^ 2) = 3 * A ^ 2

def claim : Prop :=
  (∃ A : PowerSeries ℚ, IsGF A) ∧
    ∀ (A : PowerSeries ℚ), IsGF A →
      ∀ (n : ℕ), 3 < n →
        ∃ m : ℤ, coeff n (A ^ 2) = (9 : ℚ) * (m : ℚ)

end D5.S1.Recurrence.Invariants.HannaCompositionSquareModNine

namespace D5.S1.Recurrence.Invariants.HannaCompositionSquareModNine
open D5.S1.Recurrence.Invariants.CompositionalIterateCongruence (Agree)
open D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity (prime_power_subst)
set_option maxHeartbeats 400000

namespace FormulaFour

def claimFour : Prop :=
  (∃ A : PowerSeries ℚ, IsGF A) ∧
    ∀ (A : PowerSeries ℚ), IsGF A →
      ∀ (n k : ℕ), 1 ≤ n → 1 ≤ k →
        ∃ m : ℤ, coeff n (A ^ (3 * k) - (A.subst (X ^ 3)) ^ k) =
          (3 : ℚ) * (m : ℚ)

end FormulaFour

open D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General

section Ring
variable {R : Type*} [CommRing R]

private noncomputable def inner (f : PowerSeries R) : PowerSeries R := X ^ 2 + 2 * X ^ 3 + 2 * f ^ 2
private noncomputable def residual (f : PowerSeries R) : PowerSeries R := f.subst (inner f) - 3 * f ^ 2

private theorem inner_zero {f : PowerSeries R} (hf : constantCoeff f = 0) :
    constantCoeff (inner f) = 0 := by simp [inner, hf]

private theorem inner_order {f : PowerSeries R} (hf : constantCoeff f = 0) :
    (X : PowerSeries R) ^ 2 ∣ inner f := by
  dsimp [inner]
  exact dvd_add (dvd_add (dvd_refl _) (show X ^ 2 ∣ 2 * X ^ 3 from ⟨2 * X, by ring⟩))
    (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hf) 2) _)

private theorem inner_agree {n : ℕ} {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) (h : Agree n f g) :
    Agree (n + 1) (inner f) (inner g) := by
  have hh := agree_power_order (by omega : 0 < 2) hf hg h
  intro k hk
  simp only [inner, map_add, coeff_ofNat_mul]
  rw [hh k (by omega)]

private theorem tail_composition_agree {n : ℕ} (hn : 2 ≤ n)
    {f g u v : PowerSeries R} (hg1 : coeff 1 g = 1)
    (hu : constantCoeff u = 0) (hv : constantCoeff v = 0)
    (hu2 : X ^ 2 ∣ u) (hv2 : X ^ 2 ∣ v)
    (hfg : Agree n f g) (huv : Agree (n + 1) u v) :
    Agree (n + 2) (f.subst u - u) (g.subst v - v) := by
  intro k hk
  have hsu : (f - X).subst u = f.subst u - u := by
    rw [subst_sub (.of_constantCoeff_zero hu), subst_X (.of_constantCoeff_zero hu)]
  have hsv : (g - X).subst v = g.subst v - v := by
    rw [subst_sub (.of_constantCoeff_zero hv), subst_X (.of_constantCoeff_zero hv)]
  rw [← hsu, ← hsv, coeff_subst' (.of_constantCoeff_zero hu), coeff_subst' (.of_constantCoeff_zero hv)]
  apply finsum_congr
  intro e
  by_cases he : e < n
  · have hcoeff : coeff e (f - X) = coeff e (g - X) := by simp only [map_sub, hfg e he]
    rw [hcoeff]
    by_cases he0 : e = 0
    · subst e; simp
    by_cases he1 : e = 1
    · subst e; simp [hg1]
    have hp := agree_power_order (by omega : 0 < e) hu hv huv
    rw [hp k (by omega)]
  · have hk' : k < 2 * e := by omega
    have hup : coeff k (u ^ e) = 0 :=
      X_pow_dvd_iff.mp (show X ^ (2 * e) ∣ u ^ e by
        simpa only [pow_mul] using pow_dvd_pow_of_dvd hu2 e) k hk'
    have hvp : coeff k (v ^ e) = 0 :=
      X_pow_dvd_iff.mp (show X ^ (2 * e) ∣ v ^ e by
        simpa only [pow_mul] using pow_dvd_pow_of_dvd hv2 e) k hk'
    rw [hup, hvp, smul_zero, smul_zero]

private theorem residual_agree {n : ℕ} (hn : 2 ≤ n) {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) (h : Agree n f g) :
    Agree (n + 1) (residual f) (residual g) := by
  have hs := D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.agree_subst_order
    (inner_zero hf) (inner_zero hg) (inner_order hf) (inner_order hg)
    (by omega : n + 1 ≤ 2 * n) h (inner_agree hf hg h)
  have hp2 := agree_power_order (by omega : 0 < 2) hf hg h
  intro k hk
  simp only [residual, map_sub, coeff_ofNat_mul]
  rw [hs k hk, hp2 k (by omega)]

private theorem residual_top {n : ℕ} (hn : 2 ≤ n) {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (hf1 : coeff 1 f = 1) (hg1 : coeff 1 g = 1) (h : Agree n f g) :
    coeff (n + 1) (residual f) - coeff (n + 1) (residual g) =
      (-2 : R) * (coeff n f - coeff n g) := by
  have ht := tail_composition_agree hn hg1 (inner_zero hf) (inner_zero hg)
    (inner_order hf) (inner_order hg) h (inner_agree hf hg h) (n + 1) (by omega)
  have hp := power_top (by omega : 0 < 2) hf hg hf1 hg1 h
  rw [show n + 2 - 1 = n + 1 from Nat.add_succ_sub_one n 1] at hp
  simp only [map_sub, inner, map_add, coeff_ofNat_mul] at ht
  simp only [residual, inner, map_sub, coeff_ofNat_mul]
  linear_combination ht - hp

private theorem residual_base : Agree 3 (residual (X : PowerSeries R)) 0 := by
  have hz : constantCoeff (inner (X : PowerSeries R)) = 0 := inner_zero (by simp)
  have he : residual (X : PowerSeries R) = X ^ 3 * 2 := by
    rw [residual, subst_X (.of_constantCoeff_zero hz)]
    dsimp [inner]; ring
  intro k hk
  simpa only [map_zero] using X_pow_dvd_iff.mp (⟨2, he⟩ : X ^ 3 ∣ residual (X : PowerSeries R)) k hk

private theorem map_residual {S : Type*} [CommRing S] (hom : R →+* S) (f : PowerSeries R)
    (hf : constantCoeff f = 0) :
    PowerSeries.map hom (residual f) = residual (PowerSeries.map hom f) := by
  have h := map_subst (h := hom) (.of_constantCoeff_zero (inner_zero hf)) f
  change PowerSeries.map hom (f.subst (inner f)) =
    (PowerSeries.map hom f).subst (PowerSeries.map hom (inner f)) at h
  have hi : PowerSeries.map hom (inner f) = inner (PowerSeries.map hom f) := by
    simp only [inner, map_add, map_mul, map_pow, map_ofNat, map_X]
  rw [hi] at h
  simp only [residual, map_sub, map_mul, map_pow, map_ofNat, h]

private theorem solution_unique [NoZeroDivisors R] (h2 : (2 : R) ≠ 0)
    {f g : PowerSeries R} (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (hf1 : coeff 1 f = 1) (hg1 : coeff 1 g = 1)
    (he : residual f = 0) (he' : residual g = 0) : f = g := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n; simpa only [coeff_zero_eq_constantCoeff, hf] using hg.symm
    by_cases hn1 : n = 1
    · subst n; exact hf1.trans hg1.symm
    have ht := residual_top (by omega : 2 ≤ n) hf hg hf1 hg1 ih
    rw [he, he', map_zero, sub_self] at ht
    exact sub_eq_zero.mp ((mul_eq_zero.mp ht.symm).resolve_left (neg_ne_zero.mpr h2))

end Ring

private theorem residual_even (f : PowerSeries ℤ) (hf : constantCoeff f = 0) (n : ℕ) :
    (2 : ℤ) ∣ coeff n (residual f) := by
  let hom := Int.castRingHom (ZMod 2)
  have h2 : (2 : PowerSeries (ZMod 2)) = 0 := by
    rw [← map_ofNat C 2, show (2 : ZMod 2) = 0 from
      CharP.cast_eq_zero (ZMod 2) 2, map_zero]
  have h3 : (3 : PowerSeries (ZMod 2)) = 1 := by
    rw [← map_ofNat C 3, show (3 : ZMod 2) = 1 from
      CharP.cast_eq_mod (ZMod 2) 2 3, map_one]
  have he : PowerSeries.map hom (residual f) = 0 := by
    rw [map_residual hom f hf]
    simp only [residual, inner, h2, h3, zero_mul, add_zero, one_mul]
    rw [← prime_power_subst, sub_self]
  have hc := congrArg (coeff n) he
  change ((coeff n (residual f) : ℤ) : ZMod 2) = 0 at hc
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc

private theorem exists_integral : ∃ f : PowerSeries ℤ,
    constantCoeff f = 0 ∧ coeff 1 f = 1 ∧ residual f = 0 := by
  obtain ⟨f, hf, he⟩ :=
    D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.exists_lifted
      residual X 2 1 (-2 : ℤ) (fun t => t / 2)
      (by
        intro n hn f g hf hg h
        exact residual_agree hn (normal_of_agree hf).1 (normal_of_agree hg).1 h)
      (by
        intro n hn f g hf hg h
        exact residual_top hn (normal_of_agree hf).1 (normal_of_agree hg).1 (normal_of_agree hf).2 (normal_of_agree hg).2 h)
      (by
        intro f hf n
        have hd := Int.mul_ediv_cancel' (residual_even f (normal_of_agree hf).1 n)
        linear_combination -hd)
      (by simpa using (residual_base (R := ℤ)))
  exact ⟨f, (normal_of_agree hf).1, (normal_of_agree hf).2, he⟩

private noncomputable def integralSeries : PowerSeries ℤ := Classical.choose exists_integral

private theorem integral_spec : constantCoeff integralSeries = 0 ∧ coeff 1 integralSeries = 1 ∧
    residual integralSeries = 0 := Classical.choose_spec exists_integral

private theorem rational_spec : IsGF (PowerSeries.map (Int.castRingHom ℚ) integralSeries) := by
  have he := congrArg (PowerSeries.map (Int.castRingHom ℚ)) integral_spec.2.2
  rw [map_residual _ _ integral_spec.1, map_zero] at he
  refine ⟨?_, by simp only [coeff_map, integral_spec.2.1, map_one], ?_⟩
  · rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff, integral_spec.1, map_zero]
  · dsimp only [residual, inner] at he
    exact sub_eq_zero.mp he

private theorem rational_identification {f : PowerSeries ℚ} (hf : IsGF f) :
    f = PowerSeries.map (Int.castRingHom ℚ) integralSeries := by
  apply solution_unique (by norm_num : (2 : ℚ) ≠ 0) hf.1 rational_spec.1 hf.2.1 rational_spec.2.1
  · exact sub_eq_zero.mpr hf.2.2
  · have h := congrArg (PowerSeries.map (Int.castRingHom ℚ)) integral_spec.2.2
    simpa only [map_residual _ _ integral_spec.1, map_zero] using h

private theorem integral_mod_nine : ∃ Q : PowerSeries ℤ,
    integralSeries ^ 2 - (X ^ 2 + 2 * X ^ 3) = 9 * Q := by
  have hdiv : (X : PowerSeries ℤ) ^ 2 ∣ integralSeries - X := by
    apply X_pow_dvd_iff.mpr
    intro k hk
    rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
    · simp [coeff_zero_eq_constantCoeff, integral_spec.1]
    · simp [integral_spec.2.1]
  obtain ⟨Q, hQ⟩ := hdiv
  have hA : integralSeries = X + X ^ 2 * Q := by exact Eq.symm (add_eq_of_eq_sub' (id (Eq.symm hQ)))
  let H := inner integralSeries
  have hH : constantCoeff H = 0 := inner_zero integral_spec.1
  have hsubst : integralSeries.subst H = H + H ^ 2 * Q.subst H := by
    conv_lhs => rw [hA]
    rw [subst_add (.of_constantCoeff_zero hH), subst_mul (.of_constantCoeff_zero hH),
      subst_pow (.of_constantCoeff_zero hH), subst_X (.of_constantCoeff_zero hH)]
  have he : integralSeries.subst H = 3 * integralSeries ^ 2 := sub_eq_zero.mp integral_spec.2.2
  let U : PowerSeries ℤ := 1 + H * Q.subst H
  let V : PowerSeries ℤ := invOfUnit U 1
  have hU : constantCoeff U = 1 := by simp [U, hH]
  have hV : U * V = 1 := mul_invOfUnit U 1 hU
  have hfac : H * U = 3 * integralSeries ^ 2 := by
    dsimp [U]; linear_combination he - hsubst
  have hthree : H = 3 * (integralSeries ^ 2 * V) := by
    linear_combination V * hfac - H * hV
  refine ⟨(integralSeries ^ 2 * V) ^ 2 * Q.subst H, ?_⟩
  have hdiff : integralSeries ^ 2 - (X ^ 2 + 2 * X ^ 3) = H ^ 2 * Q.subst H := by
    dsimp only [H, inner] at he hsubst ⊢
    linear_combination hsubst - he
  rw [hdiff, hthree]
  ring

theorem result : D5.S1.Recurrence.Invariants.HannaCompositionSquareModNine.claim := by
  refine ⟨⟨_, rational_spec⟩, ?_⟩
  intro f hf n hn
  rw [rational_identification hf]
  obtain ⟨Q, hQ⟩ := integral_mod_nine
  have hd := congrArg (coeff n) hQ
  have hX2 : coeff n ((X : PowerSeries ℤ) ^ 2) = 0 := by simp [coeff_X_pow, show n ≠ 2 by omega]
  have hX3 : coeff n ((X : PowerSeries ℤ) ^ 3) = 0 := by simp [coeff_X_pow, show n ≠ 3 by omega]
  simp only [map_sub, map_add, coeff_ofNat_mul, hX2, hX3, mul_zero, add_zero, sub_zero] at hd
  refine ⟨coeff n Q, ?_⟩
  rw [← map_pow, coeff_map]
  simpa only [Int.coe_castRingHom, Int.cast_mul, Int.cast_ofNat] using congrArg (fun z : ℤ => (z : ℚ)) hd

namespace FormulaFour

theorem resultFour : D5.S1.Recurrence.Invariants.HannaCompositionSquareModNine.FormulaFour.claimFour := by
  refine ⟨⟨_, rational_spec⟩, ?_⟩
  intro f hf n k _hn _hk
  rw [rational_identification hf]
  obtain ⟨m, hm⟩ := D5.S1.Recurrence.Invariants.HannaTripleSquareFrobeniusModThree.integral_frobenius integralSeries n k
  refine ⟨m, ?_⟩
  have he : PowerSeries.map (Int.castRingHom ℚ)
      (integralSeries ^ (3 * k) - (integralSeries.subst (X ^ 3)) ^ k) =
      (PowerSeries.map (Int.castRingHom ℚ) integralSeries) ^ (3 * k) -
        ((PowerSeries.map (Int.castRingHom ℚ) integralSeries).subst (X ^ 3)) ^ k := by
    simp only [map_sub, map_pow,
      D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction.map_subst_pow _ _ 3 (by decide)]
  rw [← he, coeff_map]
  simpa only [Int.coe_castRingHom, Int.cast_mul, Int.cast_ofNat] using congrArg (fun z : ℤ => (z : ℚ)) hm

end FormulaFour


end D5.S1.Recurrence.Invariants.HannaCompositionSquareModNine
