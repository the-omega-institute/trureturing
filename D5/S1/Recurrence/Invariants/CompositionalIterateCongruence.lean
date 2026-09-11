/- GID: D5/S1/Recurrence/Invariants/CompositionalIterateCongruence
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/CompositionalIterateCongruence
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Degree contraction and a mod-ten geometric fixed point prove Hanna A396807. -/

import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown

open PowerSeries
namespace D5.S1.Recurrence.Invariants.CompositionalIterateCongruence
variable {R : Type*} [CommRing R]

private def Agree (degree : ℕ) (left right : PowerSeries R) : Prop :=
  ∀ index < degree, coeff index left = coeff index right

private theorem agree_iff (degree : ℕ) (left right : PowerSeries R) :
    Agree degree left right ↔ (X : PowerSeries R) ^ degree ∣ left - right := by
  simp [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]

private theorem agree_pow {degree : ℕ} {left right : PowerSeries R}
    (hyp : Agree degree left right) (exponent : ℕ) :
    Agree degree (left ^ exponent) (right ^ exponent) := by
  exact (agree_iff _ _ _).mpr ((agree_iff _ _ _).mp hyp |>.trans
    (sub_dvd_pow_sub_pow left right exponent))

private theorem coeff_pow_zero {series : PowerSeries R} (hz : constantCoeff series = 0)
    {index exponent : ℕ} (hi : index < exponent) : coeff index (series ^ exponent) = 0 :=
  X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hz) exponent) index hi

private theorem agree_subst {degree : ℕ} {left right inner other : PowerSeries R}
    (hz : constantCoeff inner = 0) (hw : constantCoeff other = 0)
    (outer_agree : Agree degree left right) (inner_agree : Agree degree inner other) :
    Agree degree (left.subst inner) (right.subst other) := by
  intro index hi
  rw [coeff_subst' (.of_constantCoeff_zero hz), coeff_subst' (.of_constantCoeff_zero hw)]
  apply finsum_congr
  intro exponent
  by_cases he : exponent < degree
  · rw [outer_agree exponent he, agree_pow inner_agree exponent index hi]
  · rw [coeff_pow_zero hz (by omega : index < exponent),
      coeff_pow_zero hw (by omega : index < exponent), smul_zero, smul_zero]

noncomputable def iterate (series : PowerSeries R) : ℕ → PowerSeries R
  | 0 => X
  | count + 1 => (iterate series count).subst series

private theorem iterate_zero (series : PowerSeries R) (hz : constantCoeff series = 0)
    (count : ℕ) : constantCoeff (iterate series count) = 0 := by
  induction count with
  | zero => simp [iterate]
  | succ count ih => exact constantCoeff_subst_eq_zero hz _ ih

private theorem iterate_agree {degree : ℕ} {left right : PowerSeries R}
    (hl : constantCoeff left = 0) (hr : constantCoeff right = 0)
    (hyp : Agree degree left right) (count : ℕ) :
    Agree degree (iterate left count) (iterate right count) := by
  induction count with
  | zero => intro index hi; rfl
  | succ count ih => exact agree_subst hl hr ih hyp

noncomputable def step (series : PowerSeries R) : PowerSeries R :=
  X + iterate series 5 * iterate series 6

private theorem step_zero {series : PowerSeries R} (hz : constantCoeff series = 0) :
    constantCoeff (step series) = 0 := by
  simp [step, iterate_zero series hz]

private theorem step_agree {degree : ℕ} {left right : PowerSeries R}
    (hl : constantCoeff left = 0) (hr : constantCoeff right = 0)
    (hyp : Agree degree left right) : Agree (degree + 1) (step left) (step right) := by
  have h5 := (agree_iff _ _ _).mp (iterate_agree hl hr hyp 5)
  have h6 := (agree_iff _ _ _).mp (iterate_agree hl hr hyp 6)
  have z5 := X_dvd_iff.mpr (iterate_zero right hr 5)
  have z6 := X_dvd_iff.mpr (iterate_zero left hl 6)
  apply (agree_iff _ _ _).mpr
  have first := mul_dvd_mul h5 z6
  have second := mul_dvd_mul z5 h6
  rw [← pow_succ] at first
  rw [mul_comm X, ← pow_succ] at second
  convert dvd_add first second using 1
  simp [step]
  ring

theorem fixed_unique {left right : PowerSeries R}
    (hl : constantCoeff left = 0) (hr : constantCoeff right = 0)
    (fl : left = step left) (fr : right = step right) : left = right := by
  have agree : ∀ degree, Agree degree left right := by
    intro degree
    induction degree with
    | zero => intro index hi; omega
    | succ degree ih => simpa only [← fl, ← fr] using step_agree hl hr ih
  ext index
  exact agree (index + 1) index (by omega)

noncomputable def approximation : ℕ → PowerSeries R
  | 0 => 0
  | depth + 1 => step (approximation depth)

private theorem approximation_zero (depth : ℕ) :
    constantCoeff (approximation (R := R) depth) = 0 := by
  induction depth with
  | zero => simp [approximation]
  | succ depth ih => exact step_zero ih

private theorem approximation_stable {depth stage : ℕ} (hle : depth ≤ stage) :
    Agree depth (approximation (R := R) depth) (approximation stage) := by
  induction depth generalizing stage with
  | zero => intro index hi; omega
  | succ depth ih =>
    cases stage with
    | zero => omega
    | succ stage =>
      exact step_agree (approximation_zero depth) (approximation_zero stage)
        (ih (by omega))

noncomputable def a (index : ℕ) : ℤ :=
  coeff index (approximation (R := ℤ) (index + 1))

noncomputable def generatingSeries : PowerSeries ℤ := mk a

private theorem generating_agree (depth : ℕ) :
    Agree depth generatingSeries (approximation depth) := by
  intro index hi
  simpa only [generatingSeries, coeff_mk, a] using
    approximation_stable (R := ℤ) (by omega : index + 1 ≤ depth) index (by omega)

theorem generating_equation : constantCoeff generatingSeries = 0 ∧
    generatingSeries = X + iterate generatingSeries 5 * iterate generatingSeries 6 := by
  have hz : constantCoeff generatingSeries = 0 := by
    rw [← coeff_zero_eq_constantCoeff]
    rw [generating_agree 1 0 (by omega), coeff_zero_eq_constantCoeff]
    exact approximation_zero 1
  refine ⟨hz, ?_⟩
  ext index
  have hg := generating_agree (index + 2) index (by omega)
  have hs := step_agree hz (approximation_zero (index + 1))
    (generating_agree (index + 1)) index (by omega)
  exact hg.trans hs.symm

private theorem map_iterate {S : Type*} [CommRing S] (hom : R →+* S)
    (series : PowerSeries R) (hz : constantCoeff series = 0) (count : ℕ) :
    (iterate series count).map hom = iterate (series.map hom) count := by
  induction count with
  | zero => simp [iterate]
  | succ count ih =>
    change (iterate series count |>.subst series).map hom =
      (iterate (series.map hom) count).subst (series.map hom)
    rw [show (iterate series count |>.subst series).map hom =
      ((iterate series count).map hom).subst (series.map hom) from
      map_subst (.of_constantCoeff_zero hz) _, ih]

private theorem map_step {S : Type*} [CommRing S] (hom : R →+* S)
    (series : PowerSeries R) (hz : constantCoeff series = 0) :
    (step series).map hom = step (series.map hom) := by
  simp [step, map_iterate hom series hz]

noncomputable def mobius (parameter : R) : PowerSeries R :=
  X * rescale parameter (mk 1)

private noncomputable def denominator (parameter : R) : PowerSeries R := 1 - C parameter * X

private theorem denominator_unit (parameter : R) : IsUnit (denominator parameter) := by
  rw [isUnit_iff_constantCoeff]
  simp [denominator]

private theorem geometric_inverse (parameter : R) :
    rescale parameter (mk 1) * denominator parameter = 1 := by
  simpa [denominator] using congrArg (rescale parameter) (mk_one_mul_one_sub_eq_one R)

private theorem mobius_denominator (parameter : R) :
    mobius parameter * denominator parameter = X := by
  rw [mobius, mul_assoc, geometric_inverse, mul_one]

private theorem mobius_zero (parameter : R) : constantCoeff (mobius parameter) = 0 := by
  simp [mobius]

private theorem mobius_composition (left right : R) :
    (mobius left).subst (mobius right) = mobius (left + right) := by
  have hs : HasSubst (mobius right) := .of_constantCoeff_zero (mobius_zero right)
  have ho : subst (mobius right) (1 : PowerSeries R) = 1 := by
    rw [← coe_substAlgHom hs]
    exact map_one _
  have hconst : subst (mobius right) (C left) = C left := by
    exact subst_C left
  have he := congrArg (subst (mobius right)) (mobius_denominator left)
  have hc : (mobius left).subst (mobius right) * (1 - C left * mobius right) =
      mobius right := by
    simpa only [denominator, subst_mul hs, subst_sub hs, subst_X hs, hconst, ho] using he
  apply (denominator_unit (left + right)).mul_right_cancel
  rw [mobius_denominator]
  calc
    (mobius left).subst (mobius right) * denominator (left + right) =
        ((mobius left).subst (mobius right) * (1 - C left * mobius right)) *
          denominator right := by
      have hm := mobius_denominator right
      dsimp [denominator] at *
      rw [map_add]
      linear_combination C left * (mobius left).subst (mobius right) * hm
    _ = X := by rw [hc, mobius_denominator]

theorem mobius_iterate (parameter : R) (count : ℕ) :
    iterate (mobius parameter) count = mobius (count * parameter) := by
  induction count with
  | zero => simp [iterate, mobius]
  | succ count ih =>
    rw [iterate, ih, mobius_composition]
    congr 1
    push_cast
    ring

private theorem denominator_ten :
    denominator (5 : ZMod 10) * denominator 6 = denominator 1 := by
  have hadd : C (5 : ZMod 10) + C 6 = C 1 := by
    rw [← map_add]
    congr 1
  have hmul : C (5 : ZMod 10) * C 6 = 0 := by
    rw [← map_mul]
    rw [show (5 : ZMod 10) * 6 = 0 by decide, map_zero]
  dsimp [denominator]
  linear_combination -X * hadd + X ^ 2 * hmul

theorem mod_ten_fixed :
    mobius (1 : ZMod 10) = X + iterate (mobius 1) 5 * iterate (mobius 1) 6 := by
  rw [mobius_iterate, mobius_iterate]
  norm_num only [Nat.cast_ofNat, mul_one]
  apply (denominator_unit (1 : ZMod 10)).mul_right_cancel
  rw [mobius_denominator, add_mul]
  calc
    X = X * denominator (1 : ZMod 10) + X * X := by simp [denominator]; ring
    _ = X * denominator (1 : ZMod 10) +
        (mobius 5 * denominator 5) * (mobius 6 * denominator 6) := by
      rw [mobius_denominator, mobius_denominator]
    _ = X * denominator (1 : ZMod 10) + mobius 5 * mobius 6 * denominator 1 := by
      rw [← denominator_ten]
      ring

theorem coefficient_congruence (index : ℕ) (hi : 1 ≤ index) : a index % 10 = 1 := by
  let hom := Int.castRingHom (ZMod 10)
  have hz : constantCoeff (generatingSeries.map hom) = 0 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
      generating_equation.1, map_zero]
  have hf : generatingSeries.map hom = step (generatingSeries.map hom) := by
    calc
      generatingSeries.map hom = (step generatingSeries).map hom :=
        congrArg (PowerSeries.map hom) generating_equation.2
      _ = step (generatingSeries.map hom) := map_step hom _ generating_equation.1
  have he := fixed_unique hz (mobius_zero (1 : ZMod 10)) hf mod_ten_fixed
  have hb : coeff index (mobius (1 : ZMod 10)) = 1 := by
    obtain ⟨prior, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : index ≠ 0)
    simp [mobius]
  have hc : (a index : ZMod 10) = 1 := by
    have hcoeff := congrArg (coeff index) he
    simpa [coeff_map, generatingSeries, hb, hom] using hcoeff
  exact (ZMod.intCast_eq_intCast_iff' (a index) 1 10).mp hc

#print axioms fixed_unique
#print axioms generating_equation
#print axioms mobius_iterate
#print axioms mod_ten_fixed
#print axioms coefficient_congruence

end D5.S1.Recurrence.Invariants.CompositionalIterateCongruence
