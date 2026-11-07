/- GID: D5/S1/Recurrence/Invariants/HannaTripleSquareFrobeniusModThree
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/HannaTripleSquareFrobeniusModThree
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Integral normalized series satisfy Hanna's two modulo-three congruences. -/

/-
admission_basis: open-problem-resolution (#21672, #21673; Proved)
escape_witness: none
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22693.
proof_shape: FormulaFourB.claimFourB: not-applicable(definition); consumers:
FormulaFourB.resultFourB
proof_shape: FormulaFourB.resultFourB: content; consumers: settling conclusion
proof_shape: IsGF: not-applicable(definition); consumers: FormulaFourB.claimFourB,
FormulaFourB.resultFourB, claim, rational_identification, rational_spec, result
proof_shape: claim: not-applicable(definition); consumers: result
proof_shape: exists_integral: bind-only; consumers: integralSeries, integral_spec
proof_shape: integralSeries: not-applicable(definition); consumers: FormulaFourB.resultFourB,
integral_mod_three, integral_spec, rational_identification, rational_spec, result
proof_shape: integral_frobenius: bind-only; consumers:
D5.S1.Recurrence.Invariants.HannaCompositionSquareModNine.FormulaFour.resultFour, result
proof_shape: integral_mod_three: bind-only; consumers: FormulaFourB.resultFourB
proof_shape: integral_spec: bind-only; consumers: integral_mod_three, rational_identification,
rational_spec
proof_shape: map_residual: bind-only; consumers: integral_mod_three, rational_identification,
rational_spec, residual_even
proof_shape: rational_identification: content; consumers: FormulaFourB.resultFourB, result
proof_shape: rational_spec: bind-only; consumers: FormulaFourB.resultFourB,
rational_identification, result
proof_shape: residual: not-applicable(definition); consumers: exists_integral, integralSeries,
integral_mod_three, integral_spec, map_residual, rational_identification, rational_spec,
residual_agree, residual_base, residual_even, residual_top, solution_unique
proof_shape: residual_agree: bind-only; consumers: exists_integral
proof_shape: residual_base: bind-only; consumers: exists_integral
proof_shape: residual_even: bind-only; consumers: exists_integral
proof_shape: residual_top: bind-only; consumers: exists_integral, solution_unique
proof_shape: result: content; consumers: settling conclusion
proof_shape: solution_unique: content; consumers: rational_identification
The source predicates retain the normalized rational-series equations.
Proofs apply the original coefficient-agreement and triangular-lifting owners.
-/

import D5.S1.Recurrence.Invariants.CompositionalIterateCongruence
import D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity
import D5.S1.Recurrence.Invariants.UnitReversionSquareParity
import D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction
import D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality

open PowerSeries
open D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction (map_subst_pow)
set_option maxHeartbeats 400000
open D5.S1.Recurrence.Invariants.CompositionalIterateCongruence (Agree)
open D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity (prime_power_subst)

namespace D5.S1.Recurrence.Invariants.HannaTripleSquareFrobeniusModThree

def IsGF (A : PowerSeries ℚ) : Prop :=
  constantCoeff A = 0 ∧ coeff 1 A = 1 ∧
    A.subst (3 * X ^ 2) = 2 * X ^ 2 + A ^ 2 - 2 * A ^ 3

def claim : Prop :=
  (∃ A : PowerSeries ℚ, IsGF A) ∧
    ∀ (A : PowerSeries ℚ), IsGF A →
      ∀ (n : ℕ),
        ∃ m : ℤ, coeff n (A ^ 3 - A.subst (X ^ 3)) = (3 : ℚ) * (m : ℚ)

namespace FormulaFourB

def claimFourB : Prop :=
  (∃ A : PowerSeries ℚ, IsGF A) ∧
    ∀ (A : PowerSeries ℚ), IsGF A →
      ∀ (n : ℕ),
        ∃ m : ℤ, coeff n (A ^ 2 - (X ^ 2 + 2 * A.subst (X ^ 3))) =
          (3 : ℚ) * (m : ℚ)

end FormulaFourB

open D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General

section Ring
variable {R : Type*} [CommRing R]

private noncomputable def residual (f : PowerSeries R) : PowerSeries R :=
  f.subst (3 * X ^ 2) - 2 * X ^ 2 - f ^ 2 + 2 * f ^ 3

private theorem residual_agree {n : ℕ} (hn : 2 ≤ n) {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) (h : Agree n f g) :
    Agree (n + 1) (residual f) (residual g) := by
  have hs := D5.S1.Recurrence.Invariants.UnitReversionSquareParity.subst_outer_agree
    h (show (X : PowerSeries R) ^ 2 ∣ 3 * X ^ 2 from ⟨3, by ring⟩)
  have hp2 := agree_power_order (by omega : 0 < 2) hf hg h
  have hp3 := agree_power_order (by omega : 0 < 3) hf hg h
  intro k hk
  simp only [residual, map_add, map_sub, coeff_ofNat_mul]
  rw [hs k (by omega), hp2 k (by omega), hp3 k (by omega)]

private theorem residual_top {n : ℕ} (hn : 2 ≤ n) {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (hf1 : coeff 1 f = 1) (hg1 : coeff 1 g = 1) (h : Agree n f g) :
    coeff (n + 1) (residual f) - coeff (n + 1) (residual g) =
      (-2 : R) * (coeff n f - coeff n g) := by
  have hs := D5.S1.Recurrence.Invariants.UnitReversionSquareParity.subst_outer_agree
    h (show (X : PowerSeries R) ^ 2 ∣ 3 * X ^ 2 from ⟨3, by ring⟩)
  have hp3 := agree_power_order (by omega : 0 < 3) hf hg h
  have hp2 := power_top (by omega : 0 < 2) hf hg hf1 hg1 h
  have hc := hs (n + 1) (by omega)
  have hd := hp3 (n + 1) (by omega)
  simp only [residual, map_add, map_sub, coeff_ofNat_mul]
  rw [hc, hd]
  have he : n + 2 - 1 = n + 1 := by exact Nat.add_succ_sub_one n 1
  rw [he] at hp2
  linear_combination -hp2

private theorem residual_base : Agree 3 (residual (X : PowerSeries R)) 0 := by
  have he : residual (X : PowerSeries R) = X ^ 3 * 2 := by
    rw [residual, subst_X (.of_constantCoeff_zero (by simp : constantCoeff (3 * (X : PowerSeries R) ^ 2) = 0))]
    ring
  intro k hk
  simpa only [map_zero] using X_pow_dvd_iff.mp (⟨2, he⟩ : X ^ 3 ∣ residual (X : PowerSeries R)) k hk

private theorem map_residual {S : Type*} [CommRing S] (hom : R →+* S) (f : PowerSeries R) :
    PowerSeries.map hom (residual f) = residual (PowerSeries.map hom f) := by
  have h := map_subst (h := hom) (.of_constantCoeff_zero
    (by simp : constantCoeff (3 * (X : PowerSeries R) ^ 2) = 0)) f
  change PowerSeries.map hom (f.subst (3 * X ^ 2)) = (PowerSeries.map hom f).subst (PowerSeries.map hom (3 * X ^ 2)) at h
  simp only [map_mul, map_ofNat, map_pow, map_X] at h
  simp only [residual, map_add, map_sub, map_mul, map_pow, map_ofNat, map_X, h]

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

private theorem residual_even (f : PowerSeries ℤ) (n : ℕ) :
    (2 : ℤ) ∣ coeff n (residual f) := by
  let hom := Int.castRingHom (ZMod 2)
  have h2 : (2 : PowerSeries (ZMod 2)) = 0 := by
    rw [← map_ofNat C 2, show (2 : ZMod 2) = 0 from
      CharP.cast_eq_zero (ZMod 2) 2, map_zero]
  have h3 : (3 : PowerSeries (ZMod 2)) = 1 := by
    rw [← map_ofNat C 3, show (3 : ZMod 2) = 1 from
      CharP.cast_eq_mod (ZMod 2) 2 3, map_one]
  have he : PowerSeries.map hom (residual f) = 0 := by
    rw [map_residual]
    simp only [residual, h2, h3, zero_mul, one_mul, sub_zero, add_zero]
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
        have hd := Int.mul_ediv_cancel' (residual_even f n)
        linear_combination -hd)
      (by simpa using (residual_base (R := ℤ)))
  exact ⟨f, (normal_of_agree hf).1, (normal_of_agree hf).2, he⟩

private noncomputable def integralSeries : PowerSeries ℤ := Classical.choose exists_integral

private theorem integral_spec : constantCoeff integralSeries = 0 ∧ coeff 1 integralSeries = 1 ∧
    residual integralSeries = 0 := Classical.choose_spec exists_integral

private theorem rational_spec : IsGF (PowerSeries.map (Int.castRingHom ℚ) integralSeries) := by
  have he := congrArg (PowerSeries.map (Int.castRingHom ℚ)) integral_spec.2.2
  rw [map_residual, map_zero] at he
  refine ⟨?_, by simp only [coeff_map, integral_spec.2.1, map_one], ?_⟩
  · rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff, integral_spec.1, map_zero]
  · dsimp only [residual] at he
    linear_combination he

private theorem rational_identification {f : PowerSeries ℚ} (hf : IsGF f) :
    f = PowerSeries.map (Int.castRingHom ℚ) integralSeries := by
  apply solution_unique (by norm_num : (2 : ℚ) ≠ 0) hf.1 rational_spec.1 hf.2.1 rational_spec.2.1
  · dsimp [residual]
    linear_combination hf.2.2
  · have h := congrArg (PowerSeries.map (Int.castRingHom ℚ)) integral_spec.2.2
    simpa only [map_residual, map_zero] using h


theorem integral_frobenius (f : PowerSeries ℤ) (n k : ℕ) :
    (3 : ℤ) ∣ coeff n (f ^ (3 * k) - (f.subst (X ^ 3)) ^ k) := by
  let hom := Int.castRingHom (ZMod 3)
  have he : PowerSeries.map hom (f ^ (3 * k) - (f.subst (X ^ 3)) ^ k) = 0 := by
    simp only [map_sub, map_pow, map_subst_pow hom f 3 (by decide)]
    rw [pow_mul, prime_power_subst, sub_self]
  have hc := congrArg (coeff n) he
  change ((coeff n (f ^ (3 * k) - (f.subst (X ^ 3)) ^ k) : ℤ) : ZMod 3) = 0 at hc
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc

theorem result : D5.S1.Recurrence.Invariants.HannaTripleSquareFrobeniusModThree.claim := by
  refine ⟨⟨_, rational_spec⟩, ?_⟩
  intro f hf n
  rw [rational_identification hf]
  obtain ⟨m, hm⟩ := integral_frobenius integralSeries n 1
  simp only [mul_one, pow_one] at hm
  refine ⟨m, ?_⟩
  have he : PowerSeries.map (Int.castRingHom ℚ) (integralSeries ^ 3 - integralSeries.subst (X ^ 3)) =
      (PowerSeries.map (Int.castRingHom ℚ) integralSeries) ^ 3 -
        (PowerSeries.map (Int.castRingHom ℚ) integralSeries).subst (X ^ 3) := by
    simp only [map_sub, map_pow, map_subst_pow _ _ 3 (by decide)]
  rw [← he, coeff_map]
  simpa only [Int.coe_castRingHom, Int.cast_mul, Int.cast_ofNat] using congrArg (fun z : ℤ => (z : ℚ)) hm

private theorem integral_mod_three (n : ℕ) :
    (3 : ℤ) ∣ coeff n (integralSeries ^ 2 - (X ^ 2 + 2 * integralSeries.subst (X ^ 3))) := by
  let hom := Int.castRingHom (ZMod 3)
  let f := PowerSeries.map hom integralSeries
  have hf0 : constantCoeff f = 0 := by
    dsimp only [f]
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff, integral_spec.1, map_zero]
  have h3 : (3 : PowerSeries (ZMod 3)) = 0 := by
    rw [← map_ofNat C 3, show (3 : ZMod 3) = 0 from
      CharP.cast_eq_zero (ZMod 3) 3, map_zero]
  have he : residual f = 0 := by
    have h := congrArg (PowerSeries.map hom) integral_spec.2.2
    simpa only [map_residual, map_zero] using h
  have he' : -2 * X ^ 2 - f ^ 2 + 2 * f ^ 3 = 0 := by
    simpa only [residual, h3, zero_mul, subst_zero_of_constantCoeff_zero hf0, zero_sub,
      neg_mul] using he
  have hz : f ^ 2 - (X ^ 2 + 2 * f.subst (X ^ 3)) = 0 := by
    rw [← prime_power_subst]
    linear_combination -he' - X ^ 2 * h3
  have hm : PowerSeries.map hom
      (integralSeries ^ 2 - (X ^ 2 + 2 * integralSeries.subst (X ^ 3))) = 0 := by
    simpa only [map_sub, map_pow, map_add, map_mul, map_ofNat, map_X,
      map_subst_pow _ _ 3 (by decide)] using hz
  have hc := congrArg (coeff n) hm
  change ((coeff n (integralSeries ^ 2 - (X ^ 2 + 2 * integralSeries.subst (X ^ 3))) : ℤ) : ZMod 3) = 0 at hc
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc

namespace FormulaFourB

theorem resultFourB : D5.S1.Recurrence.Invariants.HannaTripleSquareFrobeniusModThree.FormulaFourB.claimFourB := by
  refine ⟨⟨_, rational_spec⟩, ?_⟩
  intro f hf n
  rw [rational_identification hf]
  obtain ⟨m, hm⟩ := integral_mod_three n
  refine ⟨m, ?_⟩
  have he : PowerSeries.map (Int.castRingHom ℚ)
      (integralSeries ^ 2 - (X ^ 2 + 2 * integralSeries.subst (X ^ 3))) =
      (PowerSeries.map (Int.castRingHom ℚ) integralSeries) ^ 2 -
        (X ^ 2 + 2 * (PowerSeries.map (Int.castRingHom ℚ) integralSeries).subst (X ^ 3)) := by
    simp only [map_sub, map_pow, map_add, map_mul, map_ofNat, map_X,
      map_subst_pow _ _ 3 (by decide)]
  rw [← he, coeff_map]
  simpa only [Int.coe_castRingHom, Int.cast_mul, Int.cast_ofNat] using congrArg (fun z : ℤ => (z : ℚ)) hm

end FormulaFourB


end D5.S1.Recurrence.Invariants.HannaTripleSquareFrobeniusModThree
