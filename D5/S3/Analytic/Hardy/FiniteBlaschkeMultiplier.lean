/- GID: D5/S3/Analytic/Hardy/FiniteBlaschkeMultiplier
   generality: G
   mirror-B: D5/B/S3/Analytic/Hardy/FiniteBlaschkeMultiplier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecificLimits.Normed, mathlib/module/Mathlib.Analysis.Complex.UnitDisc.Basic]
   utility: none
   digest: Disk zeros and a unit phase produce the actual isometric finite Blaschke multiplier on full Hardy coefficients. -/

/-
The unilateral coefficient shift and its Neumann resolvent construct each disk Blaschke factor.
The data has only the zeros and unit phase, with no assumed operator properties. Every factor
and finite product is proved isometric and has the exact analytic multiplication law.
Positive degree is needed for strict disk mapping. The source condition B(0)=0 is not automatic
for this general data and remains a condition on source-facing branch constructions.
The model-space dimension and normalized all-phase Clark basis are separate required results.
-/

import D5.S3.Analytic.Hardy.HardyCoefficientRealization
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.UnitDisc.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.Separable

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open D5.S3.Analytic.Hardy.HardyCoefficientRealization
open scoped InnerProductSpace ComplexConjugate
namespace D5.S3.Analytic.Hardy.FiniteBlaschkeMultiplier

private def shifted (f : H2) : Nat → Complex
  | 0 => 0
  | n+1 => f n

private theorem shifted_hasSum (f : H2) : HasSum (fun n => ‖shifted f n‖^2) (‖f‖^2) := by
  apply (hasSum_nat_add_iff' 1).mp
  simpa [shifted] using lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal) f

private def shiftVector (f : H2) : H2 :=
  ⟨shifted f, memℓp_gen (by simpa using (shifted_hasSum f).summable)⟩

def shift : H2 →ₗᵢ[Complex] H2 where
  toFun := shiftVector
  map_add' f g := by
    apply lp.ext
    funext n
    change shifted (f+g) n = shifted f n + shifted g n
    cases n <;> simp [shifted]
  map_smul' c f := by
    apply lp.ext
    funext n
    cases n <;> simp [shiftVector, shifted]
  norm_map' f := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← coefficient_norm_sq]
    exact (shifted_hasSum f).tsum_eq

theorem shift_zero (f : H2) : shift f 0 = 0 := rfl
theorem shift_succ (f : H2) (n : Nat) : shift f (n+1) = f n := rfl

theorem shift_evaluate (f : H2) {z : Complex} (hz : ‖z‖ < 1) :
    evaluate (shift f) z = z * evaluate f z := by
  apply (evaluate_hasSum (shift f) hz).unique
  apply (hasSum_nat_add_iff' 1).mp
  simpa [shift_zero, shift_succ, pow_succ, mul_comm, mul_left_comm, mul_assoc] using
    (evaluate_hasSum f hz).mul_left z

def denominatorUnit (a : Complex) (ha : ‖a‖ < 1) : (H2 →L[Complex] H2)ˣ :=
  Units.oneSub (star a • shift.toContinuousLinearMap) (by
    calc
      ‖star a • shift.toContinuousLinearMap‖ = ‖a‖ * ‖shift.toContinuousLinearMap‖ := by
        rw [norm_smul, norm_star]
      _ ≤ ‖a‖ := mul_le_of_le_one_right (norm_nonneg _) (by
        apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
        intro f
        simp)
      _ < 1 := ha)

def factor (a : Complex) (ha : ‖a‖ < 1) : H2 →L[Complex] H2 :=
  (shift.toContinuousLinearMap - a • 1) * (↑((denominatorUnit a ha)⁻¹) : H2 →L[Complex] H2)

theorem factor_evaluate (a : Complex) (ha : ‖a‖ < 1) (f : H2) {z : Complex} (hz : ‖z‖ < 1) :
    evaluate (factor a ha f) z = ((z-a)/(1-star a*z)) * evaluate f z := by
  let y := (↑((denominatorUnit a ha)⁻¹) : H2 →L[Complex] H2) f
  have hy : y - star a • shift y = f := by
    have h := congrArg (fun T : H2 →L[Complex] H2 => T f)
      (Units.val_inv (denominatorUnit a ha))
    simpa [denominatorUnit, Units.oneSub, mul_apply_eq_comp, y] using h
  have he := congrArg (eval z hz) hy
  simp only [map_sub, map_smul, eval_apply, shift_evaluate _ hz] at he
  have hden : 1 - star a * z ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    have hh : ‖star a * z‖ < 1 := by
      rw [norm_mul, norm_star]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right ha.le (norm_nonneg z)) (by simpa using hz)
    rw [← h, norm_one] at hh
    exact lt_irrefl _ hh
  change evaluate (shift y - a • y) z = _
  rw [← eval_apply z hz, map_sub, map_smul, eval_apply, eval_apply, shift_evaluate _ hz]
  simp only [smul_eq_mul] at he ⊢
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hden).mpr
  linear_combination (z-a) * he

theorem factor_isometry (a : Complex) (ha : ‖a‖ < 1) : Isometry (factor a ha) := by
  apply AddMonoidHomClass.isometry_of_norm (factor a ha)
  intro f
  let y := (↑((denominatorUnit a ha)⁻¹) : H2 →L[Complex] H2) f
  have hy : y - star a • shift y = f := by
    have h := congrArg (fun T : H2 →L[Complex] H2 => T f)
      (Units.val_inv (denominatorUnit a ha))
    simpa [denominatorUnit, Units.oneSub, mul_apply_eq_comp, y] using h
  change ‖shift y - a • y‖ = ‖f‖
  rw [← hy]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [@norm_sub_sq Complex, norm_smul, LinearIsometry.norm_map, norm_star,
    inner_smul_right]
  rw [← inner_conj_symm (shift y) y]
  simp only [RCLike.star_def]
  simp only [RCLike.mul_re, RCLike.conj_re,
    RCLike.conj_im, neg_mul, sub_neg_eq_add]
  ring

structure FiniteBlaschkeData (m : Nat) where
  zeros : Fin m → Complex.UnitDisc
  phase : Circle

def value {m : Nat} (B : FiniteBlaschkeData m) (z : Complex) : Complex :=
  (B.phase : Complex) * (List.ofFn (fun j =>
    (z-(B.zeros j : Complex))/(1-star (B.zeros j : Complex)*z))).prod

def mul {m : Nat} (B : FiniteBlaschkeData m) : H2 →L[Complex] H2 :=
  (B.phase : Complex) • ((List.ofFn B.zeros).map
    (fun a : Complex.UnitDisc => factor (a : Complex) a.norm_lt_one)).prod

private theorem list_eval (as : List Complex.UnitDisc) (f : H2) {z : Complex} (hz : ‖z‖ < 1) :
    evaluate ((as.map (fun a : Complex.UnitDisc => factor (a : Complex) a.norm_lt_one)).prod f) z =
    (as.map (fun a : Complex.UnitDisc => (z-(a : Complex))/(1-star (a : Complex)*z))).prod * evaluate f z := by
  induction as generalizing f with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.prod_cons, mul_apply_eq_comp]
    rw [factor_evaluate _ _ _ hz, ih]
    ring

theorem mul_eval {m : Nat} (B : FiniteBlaschkeData m) (f : H2) {z : Complex} (hz : ‖z‖ < 1) :
    evaluate (mul B f) z = value B z * evaluate f z := by
  have he := (eval z hz).map_smul (B.phase : Complex)
    (((List.ofFn B.zeros).map (fun a : Complex.UnitDisc => factor (a : Complex) a.norm_lt_one)).prod f)
  change evaluate (mul B f) z = (B.phase : Complex) • evaluate _ z at he
  rw [he, list_eval _ _ hz]
  simp [value, List.map_ofFn, Function.comp_def, smul_eq_mul, mul_assoc]

private theorem list_isometry (as : List Complex.UnitDisc) :
    Isometry ((as.map (fun a : Complex.UnitDisc => factor (a : Complex) a.norm_lt_one)).prod) := by
  induction as with
  | nil => simpa using (isometry_id : Isometry (id : H2 → H2))
  | cons a as ih =>
    exact (factor_isometry (a : Complex) a.norm_lt_one).comp ih

theorem mul_isometry {m : Nat} (B : FiniteBlaschkeData m) : Isometry (mul B) := by
  apply AddMonoidHomClass.isometry_of_norm (mul B)
  intro f
  change ‖(B.phase : Complex) •
    (((List.ofFn B.zeros).map (fun a : Complex.UnitDisc => factor (a : Complex) a.norm_lt_one)).prod f)‖ = ‖f‖
  rw [norm_smul, Circle.norm_coe, one_mul]
  exact (list_isometry (List.ofFn B.zeros)).norm_map_of_map_zero (by simp) f

private theorem factor_norm_defect (a : Complex.UnitDisc) (z : Complex) :
    ‖1-star (a : Complex)*z‖^2 - ‖z-(a : Complex)‖^2 =
      (1-‖(a : Complex)‖^2)*(1-‖z‖^2) := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.normSq_mul,
    Complex.normSq_one, Complex.normSq_conj, Complex.star_def, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im]
  ring

private theorem factor_maps_disk (a : Complex.UnitDisc) {z : Complex} (hz : ‖z‖ < 1) :
    ‖(z-(a : Complex))/(1-star (a : Complex)*z)‖ < 1 := by
  have ha := a.norm_lt_one
  have hpos : 0 < (1-‖(a : Complex)‖^2)*(1-‖z‖^2) := by
    have h1 : 0 ≤ ‖(a : Complex)‖ := norm_nonneg _
    have h2 : 0 ≤ ‖z‖ := norm_nonneg _
    apply mul_pos <;> nlinarith
  have hid := factor_norm_defect a z
  have hlt : ‖z-(a : Complex)‖ < ‖1-star (a : Complex)*z‖ := by
    nlinarith [norm_nonneg (z-(a : Complex)), norm_nonneg (1-star (a : Complex)*z)]
  rw [norm_div]
  exact (div_lt_one (lt_of_le_of_lt (norm_nonneg _) hlt)).mpr hlt

private theorem list_value_norm (as : List Complex.UnitDisc) {z : Complex} (hz : ‖z‖ < 1) :
    ‖(as.map (fun a : Complex.UnitDisc => (z-(a : Complex))/(1-star (a : Complex)*z))).prod‖ ≤ 1 := by
  induction as with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.prod_cons, norm_mul]
    exact (mul_le_mul_of_nonneg_right (factor_maps_disk a hz).le (norm_nonneg _)).trans
      (by simpa using ih)

theorem maps_unitDisc {m : Nat} (B : FiniteBlaschkeData m) (hm : 0 < m) {z : Complex} (hz : ‖z‖ < 1) :
    ‖value B z‖ < 1 := by
  have hne : List.ofFn B.zeros ≠ [] := by
    intro h
    have := congrArg List.length h
    simp at this
    omega
  obtain ⟨a, as, heq⟩ := List.exists_cons_of_ne_nil hne
  have hmap : List.ofFn (fun j => (z-(B.zeros j : Complex))/(1-star (B.zeros j : Complex)*z)) =
      (List.ofFn B.zeros).map (fun a : Complex.UnitDisc => (z-(a : Complex))/(1-star (a : Complex)*z)) := by
    rw [List.map_ofFn]
    rfl
  rw [value, norm_mul, Circle.norm_coe, one_mul, hmap, heq]
  simp only [List.map_cons, List.prod_cons, norm_mul]
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left (list_value_norm as hz) (norm_nonneg _))
    (by simpa using factor_maps_disk a hz)

#print axioms shift

open Polynomial

def numerator {m : Nat} (B : FiniteBlaschkeData m) : Polynomial Complex :=
  ∏ j, (X - C (B.zeros j : Complex))
def denominator {m : Nat} (B : FiniteBlaschkeData m) : Polynomial Complex :=
  ∏ j, (1 - C (star (B.zeros j : Complex)) * X)
def fibrePolynomial {m : Nat} (B : FiniteBlaschkeData m) (alpha : Circle) :
    Polynomial Complex := C (B.phase : Complex) * numerator B - C (alpha : Complex) * denominator B
def poissonWeight {m : Nat} (B : FiniteBlaschkeData m) (zeta : Circle) : Real :=
  ∑ j, (1 - ‖(B.zeros j : Complex)‖ ^ 2) / ‖(zeta : Complex) - (B.zeros j : Complex)‖ ^ 2

theorem factor_denominator_ne_zero_closed (a : Complex.UnitDisc) (z : Complex)
    (hz : ‖z‖ ≤ 1) : 1 - star (a : Complex) * z ≠ 0 := by
  apply sub_ne_zero.mpr
  intro h
  have hn : ‖star (a : Complex) * z‖ < 1 := by
    rw [norm_mul, norm_star]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) hz) a.norm_lt_one
  rw [← h, norm_one] at hn
  exact (lt_irrefl _ hn)

theorem denominator_ne_zero_closed {m : Nat} (B : FiniteBlaschkeData m) (z : Complex)
    (hz : ‖z‖ ≤ 1) : (denominator B).eval z ≠ 0 := by
  classical
  simp only [denominator, eval_prod, eval_sub, eval_one, eval_mul, eval_C, eval_X]
  exact Finset.prod_ne_zero_iff.mpr (fun j _ => factor_denominator_ne_zero_closed (B.zeros j) z hz)

theorem value_eq_polynomial_div {m : Nat} (B : FiniteBlaschkeData m) (z : Complex) :
    value B z = (B.phase : Complex) * (numerator B).eval z / (denominator B).eval z := by
  simp only [value, numerator, denominator, eval_prod, eval_sub, eval_mul, eval_C,
    eval_X, eval_one, List.prod_ofFn, Finset.prod_div_distrib, mul_div_assoc]

theorem zero_parameter {m : Nat} (B : FiniteBlaschkeData m) (h0 : value B 0 = 0) :
    ∃ j, (B.zeros j : Complex) = 0 := by
  classical
  rw [value_eq_polynomial_div] at h0
  have hp : (numerator B).eval 0 = 0 := by
    rcases (div_eq_zero_iff).mp h0 with h | h
    · exact (mul_eq_zero.mp h).resolve_left B.phase.coe_ne_zero
    · exact (denominator_ne_zero_closed B 0 (by simp) h).elim
  simpa only [numerator, eval_prod, eval_sub, eval_X, eval_C, zero_sub,
    Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, neg_eq_zero] using hp

theorem numerator_natDegree {m : Nat} (B : FiniteBlaschkeData m) :
    (numerator B).natDegree = m := by
  rw [numerator, natDegree_prod_of_monic _ _ (fun j _ => monic_X_sub_C _)]
  simp

theorem denominator_natDegree_lt {m : Nat} (B : FiniteBlaschkeData m)
    (h0 : value B 0 = 0) : (denominator B).natDegree < m := by
  classical
  obtain ⟨j, hj⟩ := zero_parameter B h0
  have heq : denominator B = ∏ k ∈ Finset.univ.erase j,
      (1 - C (star (B.zeros k : Complex)) * X) := by
    rw [denominator, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j), hj]
    simp
  rw [heq]
  have hb (k : Fin m) : (1 - C (star (B.zeros k : Complex)) * X).natDegree ≤ 1 := by
    apply (natDegree_sub_le _ _).trans
    simp only [natDegree_one, max_le_iff, zero_le, true_and]
    exact (natDegree_mul_le).trans (by simp)
  have hle := (natDegree_prod_le (Finset.univ.erase j)
    (fun k => (1 - C (star (B.zeros k : Complex)) * X))).trans
      (Finset.sum_le_sum (fun k _ => hb k))
  exact lt_of_le_of_lt hle (by
    simpa using Finset.card_erase_lt_of_mem (Finset.mem_univ j))

theorem fibrePolynomial_natDegree {m : Nat} (B : FiniteBlaschkeData m) (alpha : Circle)
    (h0 : value B 0 = 0) : (fibrePolynomial B alpha).natDegree = m := by
  rw [fibrePolynomial, natDegree_sub_eq_left_of_natDegree_lt]
  · rw [natDegree_C_mul B.phase.coe_ne_zero, numerator_natDegree]
  · rw [natDegree_C_mul B.phase.coe_ne_zero, natDegree_C_mul alpha.coe_ne_zero,
      numerator_natDegree]
    exact denominator_natDegree_lt B h0

theorem fibre_root {m : Nat} (B : FiniteBlaschkeData m) (alpha : Circle) (z : Complex)
    (hm : 0 < m) (_h0 : value B 0 = 0) (hr : (fibrePolynomial B alpha).eval z = 0) :
    ‖z‖ = 1 ∧ value B z = (alpha : Complex) := by
  classical
  have hr' : (B.phase : Complex) * (numerator B).eval z =
      (alpha : Complex) * (denominator B).eval z := by
    simpa only [fibrePolynomial, eval_sub, eval_mul, eval_C, sub_eq_zero] using hr
  have hq : (denominator B).eval z ≠ 0 := by
    intro hq
    have hp : (numerator B).eval z = 0 := by
      rw [hq, mul_zero] at hr'
      exact (mul_eq_zero.mp hr').resolve_left B.phase.coe_ne_zero
    obtain ⟨j, hj⟩ : ∃ j, z = (B.zeros j : Complex) := by
      simpa only [numerator, eval_prod, eval_sub, eval_X, eval_C,
        Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, sub_eq_zero] using hp
    exact denominator_ne_zero_closed B z (hj ▸ (B.zeros j).norm_lt_one.le) hq
  have hv : value B z = (alpha : Complex) := by
    rw [value_eq_polynomial_div, hr', mul_div_cancel_right₀ _ hq]
  refine ⟨?_, hv⟩
  apply le_antisymm
  · by_contra! hz
    have hfactor (j : Fin m) :
        ‖1 - star (B.zeros j : Complex) * z‖ < ‖z - (B.zeros j : Complex)‖ := by
      have ha := (B.zeros j).norm_lt_one
      have hid := factor_norm_defect (B.zeros j) z
      have ha' : 0 < 1 - ‖(B.zeros j : Complex)‖^2 := by
        nlinarith [norm_nonneg (B.zeros j : Complex)]
      have hz' : 1 - ‖z‖^2 < 0 := by nlinarith
      have hneg := mul_neg_of_pos_of_neg ha' hz'
      nlinarith [norm_nonneg (1-star (B.zeros j : Complex)*z),
        norm_nonneg (z-(B.zeros j : Complex))]
    have hqj : ∀ j : Fin m, 0 < ‖1-star (B.zeros j : Complex)*z‖ := by
      have h := hq
      simp only [denominator, eval_prod, eval_sub, eval_one, eval_mul, eval_C, eval_X,
        Finset.prod_ne_zero_iff, Finset.mem_univ, forall_const] at h
      exact fun j => norm_pos_iff.mpr (h j)
    have hlt := Finset.prod_lt_prod₀ (s := Finset.univ)
      (fun j _ => hqj j) (fun j _ => (hfactor j).le)
      ⟨⟨0, hm⟩, Finset.mem_univ _, hfactor ⟨0, hm⟩⟩
    have hn := congrArg norm hr'
    simp only [norm_mul, Circle.norm_coe, one_mul, numerator, denominator, eval_prod,
      eval_sub, eval_mul, eval_C, eval_X, eval_one, norm_prod] at hn
    exact (ne_of_lt hlt) hn.symm
  · by_contra! hz
    have h := maps_unitDisc B hm hz
    rw [hv, Circle.norm_coe] at h
    exact (lt_irrefl _ h)

theorem poissonWeight_pos {m : Nat} (B : FiniteBlaschkeData m) (zeta : Circle)
    (hm : 0 < m) : 0 < poissonWeight B zeta := by
  classical
  apply Finset.sum_pos
  · intro j _
    apply div_pos
    · have ha := (B.zeros j).norm_lt_one
      nlinarith [norm_nonneg (B.zeros j : Complex)]
    · apply sq_pos_of_pos
      apply norm_pos_iff.mpr
      intro h
      have he := congrArg norm (sub_eq_zero.mp h)
      rw [Circle.norm_coe] at he
      exact (B.zeros j).norm_lt_one.ne' he
  · exact ⟨⟨0, hm⟩, Finset.mem_univ _⟩

theorem value_hasDerivAt_circle {m : Nat} (B : FiniteBlaschkeData m) (zeta : Circle) :
    HasDerivAt (value B)
      (value B zeta / (zeta : Complex) * (poissonWeight B zeta : Complex)) zeta := by
  classical
  let z : Complex := zeta
  let F (j : Fin m) (w : Complex) := (w-(B.zeros j : Complex))/(1-star (B.zeros j : Complex)*w)
  let p (j : Fin m) : Real :=
    (1-‖(B.zeros j : Complex)‖^2)/‖z-(B.zeros j : Complex)‖^2
  have hz : z ≠ 0 := zeta.coe_ne_zero
  have hf (j : Fin m) : HasDerivAt (F j) (F j z / z * (p j : Complex)) z := by
    let a : Complex := B.zeros j
    have hd : 1-star a*z ≠ 0 := factor_denominator_ne_zero_closed (B.zeros j) z
      (by rw [show z = (zeta : Complex) from rfl, Circle.norm_coe])
    have hza : z-a ≠ 0 := by
      intro h
      have hnorm := congrArg norm (sub_eq_zero.mp h)
      change ‖(zeta : Complex)‖ = ‖(B.zeros j : Complex)‖ at hnorm
      rw [Circle.norm_coe] at hnorm
      exact (B.zeros j).norm_lt_one.ne' hnorm
    have hzstar : z * star z = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      change ((‖(zeta : Complex)‖^2 : Real) : Complex) = 1
      rw [Circle.norm_coe]
      norm_num
    have hden : 1-star a*z = z*star (z-a) := by
      rw [star_sub, mul_sub, hzstar]
      ring
    have ha2 : ((‖a‖^2 : Real) : Complex) = a*star a := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hza2 : ((‖z-a‖^2 : Real) : Complex) = (z-a)*star (z-a) := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hraw := ((hasDerivAt_id z).sub_const a).div
      ((hasDerivAt_const z (1 : Complex)).sub ((hasDerivAt_id z).const_mul (star a))) hd
    convert! hraw using 1
    dsimp [F, p]
    change ((z-a)/(1-star a*z))/z *
      (((1-‖a‖^2)/‖z-a‖^2 : Real) : Complex) = _
    push_cast
    push_cast at ha2 hza2
    rw [ha2, hza2]
    simp only [← Complex.star_def]
    rw [hden]
    have hs : star z - star a ≠ 0 := by
      simpa only [star_sub] using (star_ne_zero.mpr hza)
    simp only [star_sub]
    field_simp [hz, hza, hs]
    linear_combination -hzstar
  have hprod := (HasDerivAt.fun_finsetProd (u := Finset.univ) (fun j _ => hf j)).const_mul
    (B.phase : Complex)
  have heq : value B = fun w => (B.phase : Complex) * ∏ j, F j w := by
    funext w
    simp only [value, List.prod_ofFn, F]
  rw [heq]
  convert! hprod using 1
  rw [poissonWeight, Complex.ofReal_sum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [smul_eq_mul]
  have hmul : (∏ k, F k z) = (∏ k ∈ Finset.univ.erase j, F k z) * F j z :=
    (Finset.prod_erase_mul _ _ hj).symm
  change ((B.phase : Complex) * ∏ k, F k z) / z * (p j : Complex) =
    (B.phase : Complex) * ((∏ k ∈ Finset.univ.erase j, F k z) * (F j z / z * (p j : Complex)))
  rw [hmul]
  ring

theorem fibre_derivative {m : Nat} (B : FiniteBlaschkeData m) (alpha zeta : Circle)
    (hv : value B zeta = (alpha : Complex)) :
    (fibrePolynomial B alpha).derivative.eval (zeta : Complex) =
      (denominator B).eval (zeta : Complex) * ((alpha : Complex) / (zeta : Complex)) *
        (poissonWeight B zeta : Complex) := by
  have hq := denominator_ne_zero_closed B (zeta : Complex) (le_of_eq (Circle.norm_coe zeta))
  have hvq := value_eq_polynomial_div B (zeta : Complex)
  have hraw := (((numerator B).hasDerivAt (zeta : Complex)).const_mul (B.phase : Complex)).div
    ((denominator B).hasDerivAt (zeta : Complex)) hq
  have hB : HasDerivAt (value B)
      (((B.phase : Complex) * (numerator B).derivative.eval (zeta : Complex) *
        (denominator B).eval (zeta : Complex) -
        ((B.phase : Complex) * (numerator B).eval (zeta : Complex)) *
          (denominator B).derivative.eval (zeta : Complex)) /
        (denominator B).eval (zeta : Complex)^2) (zeta : Complex) := by
    convert! hraw using 1
    exact _root_.funext (value_eq_polynomial_div B)
  have hd := hB.unique (value_hasDerivAt_circle B zeta)
  rw [hv] at hd hvq
  have hpq : (B.phase : Complex) * (numerator B).eval (zeta : Complex) =
      (alpha : Complex) * (denominator B).eval (zeta : Complex) := by
    exact (eq_div_iff hq).mp hvq |>.symm
  simp only [fibrePolynomial, derivative_sub, derivative_mul, derivative_C, zero_mul,
    zero_add, eval_sub, eval_mul, eval_C]
  rw [hpq] at hd
  field_simp at hd
  apply (mul_right_cancel₀ zeta.coe_ne_zero)
  field_simp
  linear_combination hd

theorem phase_fibre {m : Nat} (B : FiniteBlaschkeData m) (alpha : Circle)
    (hm : 0 < m) (h0 : value B 0 = 0) : ∃ zeta : Fin m → Circle,
    Function.Injective zeta ∧
    (∀ z : Complex, value B z = (alpha : Complex) ∧ ‖z‖ = 1 ↔
      ∃ j, z = (zeta j : Complex)) ∧
    (∀ j, (fibrePolynomial B alpha).derivative.eval (zeta j : Complex) ≠ 0) := by
  classical
  let R := fibrePolynomial B alpha
  have hR : R ≠ 0 := by
    intro h
    have hd := fibrePolynomial_natDegree B alpha h0
    change R.natDegree = m at hd
    rw [h, natDegree_zero] at hd
    omega
  have hsimple (z : Complex) (hz : R.eval z = 0) : R.derivative.eval z ≠ 0 := by
    have hr := fibre_root B alpha z hm h0 hz
    let zeta : Circle := ⟨z, by simpa [Submonoid.unitSphere, Metric.mem_sphere] using hr.1⟩
    have hd := fibre_derivative B alpha zeta hr.2
    change R.derivative.eval z = _ at hd
    rw [hd]
    apply mul_ne_zero
    · exact mul_ne_zero (denominator_ne_zero_closed B z hr.1.le)
        (div_ne_zero alpha.coe_ne_zero zeta.coe_ne_zero)
    · exact_mod_cast (poissonWeight_pos B zeta hm).ne'
  have hsep : R.Separable := by
    change IsCoprime R R.derivative
    rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed Complex Complex R R.derivative]
    intro z
    simp only [aeval_def]
    by_cases hz : R.eval z = 0
    · exact Or.inr (hsimple z hz)
    · exact Or.inl hz
  let Z := R.roots.toFinset
  have hcard : Z.card = m := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep),
      ← (IsAlgClosed.splits R).natDegree_eq_card_roots]
    exact fibrePolynomial_natDegree B alpha h0
  let e : Fin m ≃ Z := (Finset.equivFinOfCardEq hcard).symm
  have hz (j : Fin m) : R.eval (e j : Complex) = 0 := by
    exact (mem_roots hR).mp (Multiset.mem_toFinset.mp (e j).property)
  let zeta (j : Fin m) : Circle := ⟨e j, by
    simpa [Submonoid.unitSphere, Metric.mem_sphere] using (fibre_root B alpha _ hm h0 (hz j)).1⟩
  refine ⟨zeta, ?_, ?_, ?_⟩
  · intro i j hij
    apply e.injective
    exact Subtype.ext (congrArg (fun z : Circle => (z : Complex)) hij)
  · intro z
    constructor
    · rintro ⟨hv, hn⟩
      have heq := value_eq_polynomial_div B z
      rw [hv] at heq
      have hp : R.eval z = 0 := by
        have heq' := (eq_div_iff (denominator_ne_zero_closed B z hn.le)).mp heq
        simp only [R, fibrePolynomial, eval_sub, eval_mul, eval_C]
        exact sub_eq_zero.mpr heq'.symm
      let t : Z := ⟨z, Multiset.mem_toFinset.mpr ((mem_roots hR).mpr hp)⟩
      refine ⟨e.symm t, ?_⟩
      change z = (e (e.symm t) : Complex)
      simp only [Equiv.apply_symm_apply]
      rfl
    · rintro ⟨j, rfl⟩
      exact ⟨(fibre_root B alpha _ hm h0 (hz j)).2, (zeta j).norm_coe⟩
  · intro j
    exact hsimple _ (hz j)

#print axioms phase_fibre

#print axioms factor_evaluate
#print axioms factor_isometry
#print axioms mul_eval
#print axioms mul_isometry
#print axioms maps_unitDisc
end D5.S3.Analytic.Hardy.FiniteBlaschkeMultiplier
