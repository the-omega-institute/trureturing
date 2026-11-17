/- GID: D5/S3/Quantum/Matrix/HiaiHarmonicArithmetic
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/HiaiHarmonicArithmetic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Necessity of exponents at least one in the harmonic arithmetic matrix comparison. -/

import D5.S3.Quantum.Matrix.TwoPointFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Slope

/- admission_basis: open-problem-resolution (preregistration #31152). -/
noncomputable section
namespace D5.S3.Quantum.Matrix.HiaiHarmonicArithmetic

open Filter Topology
open _root_.Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

private abbrev MatTwo := Matrix (Fin 2) (Fin 2) ℂ

def symmetricTwo (a b c : ℝ) : MatTwo := !![(a : ℂ), (b : ℂ); (b : ℂ), (c : ℂ)]
private def familyCore (d g z : ℝ) : MatTwo :=
  symmetricTwo (1-g*z) (g*Real.sqrt (z*(1-z))) (d+g*z)
private def gapRoot (d g z : ℝ) : ℝ :=
  Real.sqrt (1 + 4 * g * (g - (1-d)) / (1-d)^2 * z)
private def upperEigen (d g z : ℝ) : ℝ := (1+d+(1-d)*gapRoot d g z)/2
private def lowerEigen (d g z : ℝ) : ℝ := (1+d-(1-d)*gapRoot d g z)/2
private def dividedPower (d g v z : ℝ) : ℝ :=
  ((upperEigen d g z)^v-(lowerEigen d g z)^v)/((1-d)*gapRoot d g z)
private def upperEntry (d g v z : ℝ) : ℝ :=
  (upperEigen d g z)^v + dividedPower d g v z * (1-g*z-upperEigen d g z)
private def lowerEntry (d g v z : ℝ) : ℝ :=
  (upperEigen d g z)^v + dividedPower d g v z * (d+g*z-upperEigen d g z)

lemma symmetricTwo_selfAdjoint (a b c : ℝ) :
    IsSelfAdjoint (symmetricTwo a b c) := by
  change (symmetricTwo a b c)ᴴ = symmetricTwo a b c
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symmetricTwo, Matrix.conjTranspose_apply]

lemma symmetricTwo_involution {a b c e : ℝ} (he : e ≠ 0)
    (hs : e^2 = (a-c)^2+4*b^2) :
    let H := symmetricTwo ((a-c)/e) (2*b/e) ((c-a)/e)
    IsSelfAdjoint H ∧ H*H = 1 := by
  dsimp
  refine ⟨symmetricTwo_selfAdjoint _ _ _, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symmetricTwo, Matrix.mul_apply, Fin.sum_univ_two, ← Complex.ofReal_mul,
      ← Complex.ofReal_add, ← Complex.ofReal_div, ← Complex.ofReal_sub]
  all_goals norm_cast
  all_goals field_simp
  all_goals nlinarith [hs]

lemma symmetricTwo_cfc (f : ℝ → ℝ) {a b c e : ℝ} (he : e ≠ 0)
    (hs : e^2 = (a-c)^2+4*b^2) :
    cfc f (symmetricTwo a b c) =
      ((f ((a+c+e)/2)+f ((a+c-e)/2))/2) • (1 : MatTwo) +
      ((f ((a+c+e)/2)-f ((a+c-e)/2))/2) •
        symmetricTwo ((a-c)/e) (2*b/e) ((c-a)/e) := by
  let H := symmetricTwo ((a-c)/e) (2*b/e) ((c-a)/e)
  have hh := symmetricTwo_involution he hs
  have heq : symmetricTwo a b c = ((a+c)/2) • (1 : MatTwo)+(e/2) • H := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [H, symmetricTwo, Matrix.smul_apply, Complex.real_smul,
        ← Complex.ofReal_mul, ← Complex.ofReal_add]
    all_goals push_cast
    all_goals field_simp
    all_goals ring
  rw [heq, QuantumTwoPointFunctionalCalculus.two_point_cfc _ _ _ _ hh.1 hh.2]
  convert rfl using 1 <;> congr 4 <;> ring

private lemma familyPower_entries {d g z v : ℝ} (hd : d ≠ 1)
    (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hw : gapRoot d g z ≠ 0) (hcore : (familyCore d g z).PosSemidef) :
    CFC.rpow (familyCore d g z) v =
      symmetricTwo (upperEntry d g v z)
        (dividedPower d g v z * g * Real.sqrt (z*(1-z))) (lowerEntry d g v z) := by
  have hδ : 1-d ≠ 0 := sub_ne_zero.mpr hd.symm
  have hwpos : 0 ≤ 1+4*g*(g-(1-d))/(1-d)^2*z := by
    have hh := Real.sq_sqrt (show 0 ≤ z*(1-z) from mul_nonneg hz (sub_nonneg.mpr hz1))
    have hnum : 0 ≤ (1-d-2*g*z)^2+4*g^2*(z*(1-z)) := by positivity
    have hid : 1+4*g*(g-(1-d))/(1-d)^2*z =
        ((1-d-2*g*z)^2+4*g^2*(z*(1-z)))/(1-d)^2 := by
      field_simp
      <;> ring
    rw [hid]
    positivity
  have he : (1-d)*gapRoot d g z ≠ 0 := mul_ne_zero hδ hw
  have hs : ((1-d)*gapRoot d g z)^2 =
      ((1-g*z)-(d+g*z))^2+4*(g*Real.sqrt (z*(1-z)))^2 := by
    have hw2 : (gapRoot d g z)^2 = 1+4*g*(g-(1-d))/(1-d)^2*z :=
      Real.sq_sqrt hwpos
    rw [mul_pow, hw2, mul_pow,
      Real.sq_sqrt (mul_nonneg hz (sub_nonneg.mpr hz1))]
    field_simp
    <;> ring
  rw [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hcore.nonneg]
  rw [familyCore, symmetricTwo_cfc (fun x : ℝ => x^v) he hs]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symmetricTwo, upperEntry, lowerEntry, dividedPower, upperEigen, lowerEigen,
      Matrix.smul_apply, Complex.real_smul, ← Complex.ofReal_mul, ← Complex.ofReal_add,
      ← Complex.ofReal_sub, ← Complex.ofReal_div]
  all_goals push_cast
  all_goals field_simp
  all_goals ring

private def rotationTwo (z : ℝ) : MatTwo :=
  !![(Real.sqrt (1-z) : ℂ), -(Real.sqrt z : ℂ);
     (Real.sqrt z : ℂ), (Real.sqrt (1-z) : ℂ)]

private lemma rotatedCore_posDef {d z : ℝ} (hd : 0 < d) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    (familyCore d (1-d) z).PosDef := by
  have hs : (Real.sqrt z)^2 = z := Real.sq_sqrt hz
  have hc : (Real.sqrt (1-z))^2 = 1-z := Real.sq_sqrt (sub_nonneg.mpr hz1)
  have hU : IsUnit (rotationTwo z) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have hdet : (rotationTwo z).det = 1 := by
      simp [rotationTwo, Matrix.det_fin_two, ← Complex.ofReal_mul,
        ← Complex.ofReal_pow, ← Complex.ofReal_add]
      norm_cast
      nlinarith
    rw [hdet]
    exact isUnit_one
  have hD : (Matrix.diagonal ![(1 : ℂ), (d : ℂ)]).PosDef := by
    apply Matrix.posDef_diagonal_iff.mpr
    intro i
    fin_cases i
    · norm_num
    · simpa using (show (0 : ℂ) < (d : ℂ) by exact_mod_cast hd)
  have hid : familyCore d (1-d) z = rotationTwo z *
      Matrix.diagonal ![(1 : ℂ), (d : ℂ)] * star (rotationTwo z) := by
    have hroot : Real.sqrt (z*(1-z)) = Real.sqrt z * Real.sqrt (1-z) :=
      Real.sqrt_mul hz _
    have hcd : (Real.sqrt (1-z))^2*d = (1-z)*d := congrArg (fun y : ℝ => y*d) hc
    have hsd : (Real.sqrt z)^2*d = z*d := congrArg (fun y : ℝ => y*d) hs
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [familyCore, symmetricTwo, rotationTwo, Matrix.mul_apply, Matrix.vecMul, dotProduct,
        Fin.sum_univ_two, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
        ← Complex.ofReal_mul, ← Complex.ofReal_add, ← Complex.ofReal_sub,
        ← Complex.ofReal_pow, hroot]
    all_goals try push_cast
    all_goals norm_cast
    all_goals nlinarith [hc, hs, hcd, hsd]
  rw [hid]
  exact (_root_.Matrix.IsUnit.posDef_star_right_conjugate_iff hU).mpr hD

private lemma rotatedCore_rpow {d z : ℝ} (hd : 0 < d) (hd1 : d ≠ 1)
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (v : ℝ) :
    CFC.rpow (familyCore d (1-d) z) v = familyCore (d^v) (1-d^v) z := by
  have hδ : 1-d ≠ 0 := sub_ne_zero.mpr hd1.symm
  have hw : gapRoot d (1-d) z = 1 := by simp [gapRoot]
  rw [familyPower_entries hd1 hz hz1 (by rw [hw]; norm_num)
    (rotatedCore_posDef hd hz hz1).posSemidef]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symmetricTwo, familyCore, upperEntry, lowerEntry, dividedPower,
      upperEigen, lowerEigen, hw, Real.one_rpow, ← Complex.ofReal_mul,
      ← Complex.ofReal_add, ← Complex.ofReal_sub, ← Complex.ofReal_div]
  all_goals push_cast
  all_goals field_simp
  all_goals first | simp | ring

private lemma family_power_sum {a x z : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (t : ℝ) :
    (1-a) • CFC.rpow (familyCore x (1-x) 0) t +
      a • CFC.rpow (familyCore (x^2) (1-x^2) z) t =
      familyCore ((1-a)*x^t+a*x^(2*t)) (a*(1-x^(2*t))) z := by
  have hxne : x ≠ 1 := ne_of_lt hx1
  have hx2ne : x^2 ≠ 1 := by nlinarith
  rw [rotatedCore_rpow hx hxne (le_refl 0) (by norm_num) t,
    rotatedCore_rpow (sq_pos_of_pos hx) hx2ne hz hz1 t]
  rw [← Real.rpow_natCast_mul hx.le 2 t]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [familyCore, symmetricTwo, Matrix.smul_apply, Complex.real_smul]
  all_goals push_cast
  all_goals ring

private lemma family_power_sum_posDef {a x z : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hx : 0 < x) (hx1 : x < 1) (hz : 0 ≤ z) (hz1 : z ≤ 1) (t : ℝ) :
    (familyCore ((1-a)*x^t+a*x^(2*t)) (a*(1-x^(2*t))) z).PosDef := by
  rw [← family_power_sum hx hx1 hz hz1 t]
  have hA := rotatedCore_posDef hx (le_refl (0 : ℝ)) (show (0 : ℝ) ≤ 1 by norm_num)
  have hB := rotatedCore_posDef (sq_pos_of_pos hx) hz hz1
  exact (((hA.isStrictlyPositive.rpow _ t).posDef).smul (by linarith)).add
    (((hB.isStrictlyPositive.rpow _ t).posDef).smul ha)

private def scalarD (a t x : ℝ) : ℝ := (1-a)*x^t+a*x^(2*t)
private def scalarM (a t x : ℝ) : ℝ := scalarD a t x ^ (1/t)
private def scalarK (a t x : ℝ) : ℝ := a*(1+x^t)/(1+a*x^t)
private def scalarH (a t x : ℝ) : ℝ := a*(1-a)*(1-(x^t)^2)/(t*(1+a*x^t))
private def scalarCoefficient (a r s x : ℝ) : ℝ :=
  (scalarM a s x-scalarM a r x)*(scalarH a r x-scalarH a s x) -
    (scalarK a s x-scalarK a r x)^2*(1-scalarM a s x)*(1-scalarM a r x)

private theorem scalarM_positive_factor {a t x : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (ht : t ≠ 0) (hx : 0 < x) :
    scalarM a t x = x*((1-a)+a*x^t)^(1/t) := by
  have he : scalarD a t x = x^t*((1-a)+a*x^t) := by
    rw [scalarD, show 2*t=t*2 by ring, Real.rpow_mul hx.le]
    rw [Real.rpow_two]
    ring
  rw [scalarM, he, Real.mul_rpow (Real.rpow_nonneg hx.le _)
    (by have := Real.rpow_pos_of_pos hx t; positivity), ← Real.rpow_mul hx.le]
  have hcancel : t*(1/t) = 1 := by field_simp
  rw [hcancel, Real.rpow_one]

private theorem scalarM_negative_factor {a r x : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hr : r ≠ 0) (hx : 0 < x) :
    scalarM a r x = x^2*(a+(1-a)*x^(-r))^(1/r) := by
  have he : scalarD a r x = x^(2*r)*(a+(1-a)*x^(-r)) := by
    have hp : x^(2*r)*x^(-r) = x^r := by
      rw [← Real.rpow_add hx]
      congr 1
      ring
    dsimp [scalarD]
    rw [mul_add, mul_left_comm (x^(2*r)) (1-a), hp]
    ring
  rw [scalarM, he, Real.mul_rpow (Real.rpow_nonneg hx.le _)
    (by have := Real.rpow_pos_of_pos hx (-r); positivity), ← Real.rpow_mul hx.le]
  have hcancel : 2*r*(1/r) = 2 := by field_simp
  rw [hcancel, Real.rpow_two]

private theorem scalarK_negative_factor {a r x : ℝ}
    (ha : 0 < a) (hx : 0 < x) :
    scalarK a r x = a*(x^(-r)+1)/(x^(-r)+a) := by
  have hy : 0 < x^r := Real.rpow_pos_of_pos hx r
  rw [scalarK, Real.rpow_neg hx.le]
  field_simp

private theorem scalarH_negative_factor {a r x : ℝ}
    (ha : 0 < a) (hr : r ≠ 0) (hx : 0 < x) :
    x^(-r)*scalarH a r x =
      a*(1-a)*((x^(-r))^2-1)/(r*(x^(-r)+a)) := by
  have hy : 0 < x^r := Real.rpow_pos_of_pos hx r
  have hd : 0 < 1+a*x^r := by positivity
  have hd' : 0 < (x^r)⁻¹+a := by positivity
  rw [scalarH, Real.rpow_neg hx.le]
  field_simp

private theorem scalar_rpow_zero {t : ℝ} (ht : 0 < t) :
    Tendsto (fun x : ℝ => x^t) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 0) :=
  (tendsto_id.mono_left nhdsWithin_le_nhds).rpow_const_nhds_zero ht

private theorem scalarM_positive_limit {a s : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hs : 0 < s) :
    Tendsto (scalarM a s) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 0) := by
  have hid : Tendsto (fun x : ℝ => x) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hv : Tendsto (fun x : ℝ => ((1-a)+a*x^s)^(1/s))
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 ((1-a)^(1/s))) := by
    have hb := (tendsto_const_nhds (x := 1-a)).add ((tendsto_const_nhds (x := a)).mul (scalar_rpow_zero hs))
    simpa using hb.rpow_const (p := 1/s) (.inl (by linarith))
  have he : scalarM a s =ᶠ[𝓝[Set.Ioi (0 : ℝ)] 0]
      fun x => x*((1-a)+a*x^s)^(1/s) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact scalarM_positive_factor ha ha1 hs.ne' hx
  have hl : Tendsto (fun x => x*((1-a)+a*x^s)^(1/s)) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 0) := by simpa using hid.mul hv
  exact hl.congr' he.symm

private theorem scalarM_negative_limit {a r : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hr : r < 0) :
    Tendsto (scalarM a r) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 0) := by
  have hid : Tendsto (fun x : ℝ => x) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hv : Tendsto (fun x : ℝ => (a+(1-a)*x^(-r))^(1/r))
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (a^(1/r))) := by
    have hb := (tendsto_const_nhds (x := a)).add
      ((tendsto_const_nhds (x := 1-a)).mul (scalar_rpow_zero (neg_pos.mpr hr)))
    simpa using hb.rpow_const (p := 1/r) (.inl (by simpa using ha.ne'))
  have he : scalarM a r =ᶠ[𝓝[Set.Ioi (0 : ℝ)] 0]
      fun x => x^2*(a+(1-a)*x^(-r))^(1/r) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact scalarM_negative_factor ha ha1 hr.ne hx
  have hl : Tendsto (fun x => x^2*(a+(1-a)*x^(-r))^(1/r)) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 0) := by simpa using (hid.pow 2).mul hv
  exact hl.congr' he.symm

private theorem scalarK_positive_limit {a s : ℝ} (hs : 0 < s) :
    Tendsto (scalarK a s) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 a) := by
  have hy := scalar_rpow_zero hs
  have hnum := (tendsto_const_nhds (x := a)).mul ((tendsto_const_nhds (x := 1)).add hy)
  have hden := (tendsto_const_nhds (x := 1)).add ((tendsto_const_nhds (x := a)).mul hy)
  convert hnum.div hden (by norm_num : (1:ℝ)+a*0 ≠ 0) using 1 <;> first | rfl | simp [scalarK]

private theorem scalarK_negative_limit {a r : ℝ} (ha : 0 < a) (hr : r < 0) :
    Tendsto (scalarK a r) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 1) := by
  have hy := scalar_rpow_zero (neg_pos.mpr hr)
  have he : scalarK a r =ᶠ[𝓝[Set.Ioi (0 : ℝ)] 0]
      fun x => a*(x^(-r)+1)/(x^(-r)+a) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact scalarK_negative_factor ha hx
  have hlim := ((tendsto_const_nhds (x := a)).mul (hy.add (tendsto_const_nhds (x := 1)))).div
    (hy.add (tendsto_const_nhds (x := a))) (by simpa using ha.ne')
  have hl : Tendsto (fun x => a*(x^(-r)+1)/(x^(-r)+a)) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 1) := by
    convert hlim using 1 <;> simp [ha.ne']
  exact hl.congr' he.symm

private theorem scalarH_positive_limit {a s : ℝ} (hs : 0 < s) :
    Tendsto (scalarH a s) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (a*(1-a)/s)) := by
  have hy := scalar_rpow_zero hs
  have hnum := (tendsto_const_nhds (x := a*(1-a))).mul
    ((tendsto_const_nhds (x := 1)).sub (hy.pow 2))
  have hden := (tendsto_const_nhds (x := s)).mul
    ((tendsto_const_nhds (x := 1)).add ((tendsto_const_nhds (x := a)).mul hy))
  convert hnum.div hden (by simpa using hs.ne') using 1 <;> first | rfl | simp [scalarH]

private theorem scalarH_negative_scaled_limit {a r : ℝ}
    (ha : 0 < a) (hr : r < 0) :
    Tendsto (fun x => x^(-r)*scalarH a r x) (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝 (-(1-a)/r)) := by
  have hy := scalar_rpow_zero (neg_pos.mpr hr)
  have he : (fun x => x^(-r)*scalarH a r x) =ᶠ[𝓝[Set.Ioi (0 : ℝ)] 0]
      fun x => a*(1-a)*((x^(-r))^2-1)/(r*(x^(-r)+a)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact scalarH_negative_factor ha hr.ne hx
  have hnum := (tendsto_const_nhds (x := a*(1-a))).mul ((hy.pow 2).sub (tendsto_const_nhds (x := 1)))
  have hden := (tendsto_const_nhds (x := r)).mul (hy.add (tendsto_const_nhds (x := a)))
  have hl := hnum.div hden (show r*(0+a) ≠ 0 by exact mul_ne_zero hr.ne (by simpa using ha.ne'))
  have hv : a*(1-a)*((0:ℝ)^2-1)/(r*(0+a)) = -(1-a)/r := by
    field_simp
    <;> ring
  rw [hv] at hl
  exact hl.congr' he.symm

private theorem scalarM_positive_mul_H_limit {a r s : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hr : r < 0) (hr1 : -1 < r) (hs : 0 < s) :
    Tendsto (fun x => scalarM a s x*scalarH a r x)
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 0) := by
  have hv : Tendsto (fun x : ℝ => ((1-a)+a*x^s)^(1/s))
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 ((1-a)^(1/s))) := by
    have hb := (tendsto_const_nhds (x := 1-a)).add ((tendsto_const_nhds (x := a)).mul (scalar_rpow_zero hs))
    simpa using hb.rpow_const (p := 1/s) (.inl (by linarith))
  have he : (fun x => scalarM a s x*scalarH a r x) =ᶠ[𝓝[Set.Ioi (0 : ℝ)] 0]
      fun x => x^(1+r)*((1-a)+a*x^s)^(1/s)*(x^(-r)*scalarH a r x) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [scalarM_positive_factor ha ha1 hs.ne' hx]
    have hp : x^(1+r)*x^(-r) = x := by
      rw [← Real.rpow_add hx]
      rw [show (1+r)+ -r = 1 by ring, Real.rpow_one]
    calc
      x * ((1-a)+a*x^s)^(1/s) * scalarH a r x =
          (x^(1+r)*x^(-r))*((1-a)+a*x^s)^(1/s)*scalarH a r x := by rw [hp]
      _ = _ := by ring
  have hl := ((scalar_rpow_zero (show 0 < 1+r by linarith)).mul hv).mul
    (scalarH_negative_scaled_limit ha hr)
  have hl' : Tendsto (fun x => x^(1+r)*((1-a)+a*x^s)^(1/s)*(x^(-r)*scalarH a r x)) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 0) := by simpa using hl
  exact hl'.congr' he.symm

private theorem scalarM_negative_mul_H_limit {a r : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hr : r < 0) (hr1 : -1 < r) :
    Tendsto (fun x => scalarM a r x*scalarH a r x)
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 0) := by
  have hv : Tendsto (fun x : ℝ => (a+(1-a)*x^(-r))^(1/r))
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (a^(1/r))) := by
    have hb := (tendsto_const_nhds (x := a)).add
      ((tendsto_const_nhds (x := 1-a)).mul (scalar_rpow_zero (neg_pos.mpr hr)))
    simpa using hb.rpow_const (p := 1/r) (.inl (by simpa using ha.ne'))
  have he : (fun x => scalarM a r x*scalarH a r x) =ᶠ[𝓝[Set.Ioi (0 : ℝ)] 0]
      fun x => x^(2+r)*(a+(1-a)*x^(-r))^(1/r)*(x^(-r)*scalarH a r x) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [scalarM_negative_factor ha ha1 hr.ne hx]
    have hp : x^(2+r)*x^(-r) = x^2 := by
      rw [← Real.rpow_add hx]
      rw [show (2+r)+ -r = 2 by ring, Real.rpow_two]
    calc
      x^2 * (a+(1-a)*x^(-r))^(1/r) * scalarH a r x =
          (x^(2+r)*x^(-r))*(a+(1-a)*x^(-r))^(1/r)*scalarH a r x := by rw [hp]
      _ = _ := by ring
  have hl := ((scalar_rpow_zero (show 0 < 2+r by linarith)).mul hv).mul
    (scalarH_negative_scaled_limit ha hr)
  have hl' : Tendsto (fun x => x^(2+r)*(a+(1-a)*x^(-r))^(1/r)*(x^(-r)*scalarH a r x)) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 0) := by simpa using hl
  exact hl'.congr' he.symm

private theorem scalarCoefficient_limit {a r s : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hr : r < 0) (hr1 : -1 < r) (hs : 0 < s) :
    Tendsto (scalarCoefficient a r s) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (-(1-a)^2)) := by
  have hms := scalarM_positive_limit ha ha1 hs
  have hmr := scalarM_negative_limit ha ha1 hr
  have hdiag := ((scalarM_positive_mul_H_limit ha ha1 hr hr1 hs).sub
    (scalarM_negative_mul_H_limit ha ha1 hr hr1)).sub
    ((hms.sub hmr).mul (scalarH_positive_limit (a := a) hs))
  have hoff := (((scalarK_positive_limit (a := a) hs).sub
    (scalarK_negative_limit ha hr)).pow 2).mul
    (((tendsto_const_nhds (x := 1)).sub hms).mul ((tendsto_const_nhds (x := 1)).sub hmr))
  have he : scalarCoefficient a r s =
      fun x => ((scalarM a s x*scalarH a r x - scalarM a r x*scalarH a r x) -
        (scalarM a s x-scalarM a r x)*scalarH a s x) -
        (scalarK a s x-scalarK a r x)^2*((1-scalarM a s x)*(1-scalarM a r x)) := by
    funext x
    dsimp [scalarCoefficient]
    ring
  rw [he]
  convert hdiag.sub hoff using 1 <;> simp <;> ring

private theorem scalarD_pos {a t x : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx : 0 < x) :
    0 < scalarD a t x := by
  dsimp [scalarD]
  have h1 := Real.rpow_pos_of_pos hx t
  have h2 := Real.rpow_pos_of_pos hx (2*t)
  positivity

private theorem scalarD_ne_one {a t x : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (ht : t ≠ 0) (hx : 0 < x) (hx1 : x < 1) :
    scalarD a t x ≠ 1 := by
  rcases lt_or_gt_of_ne ht with ht | ht
  · have h1 := Real.one_lt_rpow_of_pos_of_lt_one_of_neg hx hx1 ht
    have h2 := Real.one_lt_rpow_of_pos_of_lt_one_of_neg hx hx1 (show 2*t < 0 by linarith)
    have hd : 1 < scalarD a t x := by
      dsimp [scalarD]
      nlinarith [mul_pos (show 0 < 1-a by linarith) (sub_pos.mpr h1),
        mul_pos ha (sub_pos.mpr h2)]
    exact hd.ne'
  · have h1 := Real.rpow_lt_one hx.le hx1 ht
    have h2 := Real.rpow_lt_one hx.le hx1 (show 0 < 2*t by linarith)
    have hd : scalarD a t x < 1 := by
      dsimp [scalarD]
      nlinarith [mul_pos (show 0 < 1-a by linarith) (sub_pos.mpr h1),
        mul_pos ha (sub_pos.mpr h2)]
    exact hd.ne

private theorem scalarK_eq_quotient {a t x : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (ht : t ≠ 0) (hx : 0 < x) (hx1 : x < 1) :
    a*(1-x^(2*t))/(1-scalarD a t x) = scalarK a t x := by
  have hd := sub_ne_zero.mpr (scalarD_ne_one ha ha1 ht hx hx1).symm
  have hy : 0 < x^t := Real.rpow_pos_of_pos hx t
  have hp : 0 < 1+a*x^t := by positivity
  rw [scalarK]
  apply (div_eq_div_iff hd hp.ne').2
  rw [scalarD, show 2*t=t*2 by ring, Real.rpow_mul hx.le, Real.rpow_two]
  ring

private theorem scalarH_eq_quotient {a t x : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (ht : t ≠ 0) (hx : 0 < x) (hx1 : x < 1) :
    (a*(1-x^(2*t))*(a*(1-x^(2*t))-(1-scalarD a t x))/(1-scalarD a t x))*(1/t) =
      -scalarH a t x := by
  have hd := sub_ne_zero.mpr (scalarD_ne_one ha ha1 ht hx hx1).symm
  have hy : 0 < x^t := Real.rpow_pos_of_pos hx t
  have hp : 0 < 1+a*x^t := by positivity
  rw [scalarH]
  field_simp [hd, hp.ne', ht]
  rw [scalarD, show 2*t=t*2 by ring, Real.rpow_mul hx.le, Real.rpow_two]
  ring

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open _root_.Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]
local instance : Pow (Matrix n n ℂ) ℝ := ⟨CFC.rpow⟩

/-- The weighted quasi-arithmetic mean, with nonzero parameter on its intended domain. -/
def powerMean (α t : ℝ) (A B : Matrix n n ℂ) : Matrix n n ℂ :=
  ((1 - α) • A ^ t + α • B ^ t) ^ (1 / t)

/-- The quasi-harmonic mean is the positive power of the weighted harmonic mean. -/
def harmonicMean (α p : ℝ) (A B : Matrix n n ℂ) : Matrix n n ℂ :=
  (((1 - α) • (A ^ p)⁻¹ + α • (B ^ p)⁻¹)⁻¹) ^ (1 / p)

private theorem inv_eq_rpow {A : Matrix n n ℂ} (hA : A.PosDef) :
    A⁻¹ = A ^ (-1 : ℝ) := by
  rw [Matrix.nonsing_inv_eq_ringInverse]
  exact CFC.inverse_eq_rpow_neg_one hA.isStrictlyPositive

private theorem inv_rpow {A : Matrix n n ℂ} (hA : A.PosDef) (t : ℝ) :
    (A ^ t)⁻¹ = A ^ (-t) := by
  by_cases ht : t = 0
  · subst t
    simp [CFC.rpow_zero _ hA.posSemidef.nonneg, CFC.one_rpow]
  · rw [Matrix.nonsing_inv_eq_ringInverse]
    exact CFC.inverse_rpow A t ht hA.isStrictlyPositive

theorem rpow_inv {A : Matrix n n ℂ} (hA : A.PosDef) (t : ℝ) :
    A⁻¹ ^ t = A ^ (-t) := by
  rw [inv_eq_rpow hA, CFC.rpow_rpow A (-1) t (by norm_num) hA.isStrictlyPositive]
  congr 1
  ring

private theorem weighted_power_posDef {α : ℝ} (hα : 0 < α) (hα' : α < 1)
    {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef) (t : ℝ) :
    ((1 - α) • A ^ t + α • B ^ t).PosDef := by
  exact ((hA.isStrictlyPositive.rpow A t).posDef.smul (sub_pos.mpr hα')).add
    ((hB.isStrictlyPositive.rpow B t).posDef.smul hα)

private theorem powerMean_posDef {α : ℝ} (hα : 0 < α) (hα' : α < 1)
    {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef) (t : ℝ) :
    (powerMean α t A B).PosDef :=
  ((weighted_power_posDef hα hα' hA hB t).isStrictlyPositive.rpow _ _).posDef

private theorem harmonicMean_eq_powerMean {α : ℝ} (hα : 0 < α) (hα' : α < 1)
    {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef) (p : ℝ) :
    harmonicMean α p A B = powerMean α (-p) A B := by
  unfold harmonicMean powerMean
  rw [inv_rpow hA p, inv_rpow hB p,
    rpow_inv (weighted_power_posDef hα hα' hA hB (-p))]
  congr 1
  simp

private theorem powerMean_inv_inputs {α : ℝ} (hα : 0 < α) (hα' : α < 1)
    {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef) (t : ℝ) :
    powerMean α t A⁻¹ B⁻¹ = (powerMean α (-t) A B)⁻¹ := by
  unfold powerMean
  rw [rpow_inv hA, rpow_inv hB,
    inv_rpow (weighted_power_posDef hα hα' hA hB (-t))]
  congr 1
  simp

private theorem powerMean_order_duality {α p q : ℝ} (hα : 0 < α) (hα' : α < 1)
    (h : ∀ A B : Matrix n n ℂ, A.PosDef → B.PosDef →
      powerMean α (-p) A B ≤ powerMean α q A B) :
    ∀ A B : Matrix n n ℂ, A.PosDef → B.PosDef →
      powerMean α (-q) A B ≤ powerMean α p A B := by
  intro A B hA hB
  have hi := h A⁻¹ B⁻¹ hA.inv hB.inv
  rw [powerMean_inv_inputs hα hα' hA hB,
    powerMean_inv_inputs hα hα' hA hB, neg_neg] at hi
  have hc := CStarAlgebra.rpow_neg_one_le_rpow_neg_one hi
    (powerMean_posDef hα hα' hA hB p).inv.isStrictlyPositive
  simpa only [← inv_eq_rpow (powerMean_posDef hα hα' hA hB (-q)).inv,
    ← inv_eq_rpow (powerMean_posDef hα hα' hA hB p).inv,
    Matrix.nonsing_inv_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).mp (powerMean_posDef hα hα' hA hB (-q)).isUnit),
    Matrix.nonsing_inv_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).mp (powerMean_posDef hα hα' hA hB p).isUnit)] using hc

open Filter Topology Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

private lemma spectral_values (d g v : ℝ) :
    gapRoot d g 0 = 1 ∧ upperEigen d g 0 = 1 ∧ lowerEigen d g 0 = d ∧
    dividedPower d g v 0 = (1-d^v)/(1-d) ∧ upperEntry d g v 0 = 1 := by
  have hw : gapRoot d g 0 = 1 := by simp [gapRoot]
  have hu : upperEigen d g 0 = 1 := by rw [upperEigen, hw]; ring
  have hl : lowerEigen d g 0 = d := by rw [lowerEigen, hw]; ring
  simp [hw, hu, hl, dividedPower, upperEntry]

private lemma lowerEntry_zero {d : ℝ} (hd : d ≠ 1) (g v : ℝ) :
    lowerEntry d g v 0 = d^v := by
  have hδ : 1-d ≠ 0 := sub_ne_zero.mpr hd.symm
  rw [lowerEntry, (spectral_values d g v).2.1,
    (spectral_values d g v).2.2.2.1, Real.one_rpow]
  field_simp
  <;> ring

private lemma spectral_derivatives {d : ℝ} (hd : 0 < d) (hd1 : d ≠ 1) (g v : ℝ) :
    HasDerivAt (upperEntry d g v)
      (g*(g-(1-d))/(1-d)*v - (g/(1-d))^2*(1-d^v)) 0 ∧
    ContinuousAt (lowerEntry d g v) 0 ∧
    ContinuousAt (dividedPower d g v) 0 := by
  have hδ : 1-d ≠ 0 := sub_ne_zero.mpr (Ne.symm hd1)
  have hroot : HasDerivAt (gapRoot d g)
      (2*g*(g-(1-d))/(1-d)^2) 0 := by
    have hh := ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).add
      ((hasDerivAt_id (0 : ℝ)).const_mul (4*g*(g-(1-d))/(1-d)^2))).sqrt
      (by norm_num)
    change HasDerivAt (gapRoot d g) _ 0 at hh
    convert hh using 1 <;> simp <;> ring
  have hu : HasDerivAt (upperEigen d g) (g*(g-(1-d))/(1-d)) 0 := by
    have hh := ((hasDerivAt_const (0 : ℝ) (1+d)).add
      (hroot.const_mul (1-d))).div_const 2
    change HasDerivAt (upperEigen d g) _ 0 at hh
    convert hh using 1 <;> field_simp [hδ] <;> ring
  have hl : HasDerivAt (lowerEigen d g) (-g*(g-(1-d))/(1-d)) 0 := by
    have hh := ((hasDerivAt_const (0 : ℝ) (1+d)).sub
      (hroot.const_mul (1-d))).div_const 2
    change HasDerivAt (lowerEigen d g) _ 0 at hh
    convert hh using 1 <;> field_simp [hδ] <;> ring
  have hu0 : upperEigen d g 0 = 1 := (spectral_values d g v).2.1
  have hl0 : lowerEigen d g 0 = d := (spectral_values d g v).2.2.1
  have hup := hu.rpow_const (p := v) (Or.inl (by rw [hu0]; norm_num))
  simp only [hu0, Real.one_rpow, mul_one] at hup
  have hlp := hl.rpow_const (p := v) (Or.inl (by rw [hl0]; exact hd.ne'))
  have hb := (hup.sub hlp).div (hroot.const_mul (1-d))
    (by simpa [gapRoot] using hδ)
  change HasDerivAt (dividedPower d g v) _ 0 at hb
  have he := hup.add (hb.mul
    (((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub
      ((hasDerivAt_id (0 : ℝ)).const_mul g)).sub hu))
  change HasDerivAt (upperEntry d g v) _ 0 at he
  refine ⟨?_, ?_, hb.continuousAt⟩
  · convert he using 1
    simp [upperEigen, lowerEigen, dividedPower, gapRoot]
    field_simp [hδ]
    <;> ring
  · exact (hup.continuousAt.add (hb.continuousAt.mul
      ((continuousAt_const.add (continuousAt_id.const_mul g)).sub hu.continuousAt)))

private def determinantModel (d g v e h w z : ℝ) : ℝ :=
  (upperEntry d g v z-upperEntry e h w z)*
    (lowerEntry d g v z-lowerEntry e h w z) -
    (g*dividedPower d g v z-h*dividedPower e h w z)^2*z*(1-z)

private lemma determinant_slope {d e : ℝ} (hd : 0 < d) (he : 0 < e)
    (hd1 : d ≠ 1) (he1 : e ≠ 1) (g h v w : ℝ) :
    Tendsto (fun z => determinantModel d g v e h w z / z) (𝓝[>] 0)
      (𝓝 ((d^v-e^w)*
        ((g*(g-(1-d))/(1-d)*v-(g/(1-d))^2*(1-d^v)) -
         (h*(h-(1-e))/(1-e)*w-(h/(1-e))^2*(1-e^w))) -
        (g*((1-d^v)/(1-d))-h*((1-e^w)/(1-e)))^2)) := by
  have hdv := spectral_derivatives hd hd1 g v
  have hew := spectral_derivatives he he1 h w
  have hu := (hdv.1.sub hew.1).tendsto_slope_zero_right
  have huv : upperEntry d g v 0-upperEntry e h w 0 = 0 := by
    rw [(spectral_values d g v).2.2.2.2, (spectral_values e h w).2.2.2.2]
    ring
  simp only [Pi.sub_apply, zero_add, huv, sub_zero, smul_eq_mul] at hu
  have hv := (hdv.2.1.tendsto.sub hew.2.1.tendsto).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  rw [lowerEntry_zero hd1, lowerEntry_zero he1] at hv
  have hb := ((hdv.2.2.tendsto.const_mul g).sub
    (hew.2.2.tendsto.const_mul h)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  rw [(spectral_values d g v).2.2.2.1, (spectral_values e h w).2.2.2.1] at hb
  have hz : Tendsto (fun z : ℝ => 1-z) (𝓝[>] 0) (𝓝 1) := by
    simpa using (tendsto_const_nhds.sub (tendsto_id.mono_left nhdsWithin_le_nhds) :
      Tendsto (fun z : ℝ => 1-z) (𝓝[>] 0) (𝓝 (1-0)))
  have ht := (hu.mul hv).sub ((hb.pow 2).mul hz)
  simp only [mul_one] at ht
  convert ht.congr' ?_ using 1
  · ring
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hzn : z ≠ 0 := ne_of_gt hz
    dsimp [determinantModel]
    field_simp
    <;> ring

private lemma mean_determinant_limit {a r s x : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hr : r ≠ 0) (hs : s ≠ 0)
    (hx : 0 < x) (hx1 : x < 1) :
    Tendsto (fun z => determinantModel (scalarD a s x) (a*(1-x^(2*s))) (1/s)
      (scalarD a r x) (a*(1-x^(2*r))) (1/r) z / z) (𝓝[>] 0)
      (𝓝 (scalarCoefficient a r s x)) := by
  have hlim := determinant_slope (scalarD_pos ha ha1 hx) (scalarD_pos ha ha1 hx)
    (scalarD_ne_one ha ha1 hs hx hx1) (scalarD_ne_one ha ha1 hr hx hx1)
    (a*(1-x^(2*s))) (a*(1-x^(2*r))) (1/s) (1/r)
  have hks := scalarK_eq_quotient ha ha1 hs hx hx1
  have hkr := scalarK_eq_quotient ha ha1 hr hx hx1
  have hhs := scalarH_eq_quotient ha ha1 hs hx hx1
  have hhr := scalarH_eq_quotient ha ha1 hr hx hx1
  have hos : a*(1-x^(2*s))*((1-(scalarD a s x)^(1/s))/(1-scalarD a s x)) =
      scalarK a s x*(1-(scalarD a s x)^(1/s)) := by rw [← hks]; ring
  have hor : a*(1-x^(2*r))*((1-(scalarD a r x)^(1/r))/(1-scalarD a r x)) =
      scalarK a r x*(1-(scalarD a r x)^(1/r)) := by rw [← hkr]; ring
  rw [hhs, hhr, hks, hkr, hos, hor] at hlim
  convert hlim using 1
  dsimp [scalarCoefficient, scalarM]
  ring

private lemma determinant_real {a b c e f h z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    (symmetricTwo a (b*Real.sqrt (z*(1-z))) c -
      symmetricTwo e (f*Real.sqrt (z*(1-z))) h).det =
      (((a-e)*(c-h)-(b-f)^2*z*(1-z) : ℝ) : ℂ) := by
  have hs := Real.sq_sqrt (mul_nonneg hz (sub_nonneg.mpr hz1))
  simp only [symmetricTwo, Matrix.det_fin_two, Matrix.sub_apply, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  push_cast
  norm_cast
  linear_combination -(b-f)^2*hs

private lemma coefficient_nonneg {a r s x : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hr : r ≠ 0) (hs : s ≠ 0)
    (hx : 0 < x) (hx1 : x < 1)
    (horder : ∀ A B : MatTwo, A.PosDef → B.PosDef →
      powerMean a r A B ≤ powerMean a s A B) : 0 ≤ scalarCoefficient a r s x := by
  have hw (t : ℝ) : ∀ᶠ z in 𝓝 (0 : ℝ), gapRoot (scalarD a t x) (a*(1-x^(2*t))) z ≠ 0 := by
    have hc : ContinuousAt (gapRoot (scalarD a t x) (a*(1-x^(2*t)))) 0 := by
      unfold gapRoot
      fun_prop
    exact hc.eventually_ne (by simp [gapRoot])
  apply ge_of_tendsto (mean_determinant_limit ha ha1 hr hs hx hx1)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds,
    (hw r).filter_mono nhdsWithin_le_nhds, (hw s).filter_mono nhdsWithin_le_nhds]
    with z hz hz1 hwr hws
  have hA := rotatedCore_posDef hx (le_refl (0 : ℝ)) (show (0 : ℝ) ≤ 1 by norm_num)
  have hB := rotatedCore_posDef (sq_pos_of_pos hx) hz.le hz1.le
  have ho := horder _ _ hA hB
  have hmr : powerMean a r (familyCore x (1-x) 0) (familyCore (x^2) (1-x^2) z) =
      symmetricTwo (upperEntry (scalarD a r x) (a*(1-x^(2*r))) (1/r) z)
        ((dividedPower (scalarD a r x) (a*(1-x^(2*r))) (1/r) z * a*(1-x^(2*r)))*
          Real.sqrt (z*(1-z)))
        (lowerEntry (scalarD a r x) (a*(1-x^(2*r))) (1/r) z) := by
    unfold powerMean
    simp only [← CFC.rpow_eq_pow]
    rw [family_power_sum hx hx1 hz.le hz1.le]
    change CFC.rpow (familyCore (scalarD a r x) (a*(1-x^(2*r))) z) (1/r) = _
    rw [familyPower_entries (scalarD_ne_one ha ha1 hr hx hx1) hz.le hz1.le hwr
        (family_power_sum_posDef ha ha1 hx hx1 hz.le hz1.le r).posSemidef]
    congr 2
    ring
  have hms : powerMean a s (familyCore x (1-x) 0) (familyCore (x^2) (1-x^2) z) =
      symmetricTwo (upperEntry (scalarD a s x) (a*(1-x^(2*s))) (1/s) z)
        ((dividedPower (scalarD a s x) (a*(1-x^(2*s))) (1/s) z * a*(1-x^(2*s)))*
          Real.sqrt (z*(1-z)))
        (lowerEntry (scalarD a s x) (a*(1-x^(2*s))) (1/s) z) := by
    unfold powerMean
    simp only [← CFC.rpow_eq_pow]
    rw [family_power_sum hx hx1 hz.le hz1.le]
    change CFC.rpow (familyCore (scalarD a s x) (a*(1-x^(2*s))) z) (1/s) = _
    rw [familyPower_entries (scalarD_ne_one ha ha1 hs hx hx1) hz.le hz1.le hws
        (family_power_sum_posDef ha ha1 hx hx1 hz.le hz1.le s).posSemidef]
    congr 2
    ring
  rw [hmr, hms] at ho
  have hdet := (Matrix.le_iff.mp ho).det_nonneg
  rw [determinant_real hz.le hz1.le] at hdet
  have hreal : 0 ≤ determinantModel (scalarD a s x) (a*(1-x^(2*s))) (1/s)
      (scalarD a r x) (a*(1-x^(2*r))) (1/r) z := by
    have hh := (Complex.nonneg_iff.mp hdet).1
    simp only [Complex.ofReal_re] at hh
    dsimp [determinantModel]
    convert hh using 1 <;> ring
  exact div_nonneg hreal hz.le

private lemma first_exponent {a p q : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hp : 0 < p) (hq : 0 < q)
    (horder : ∀ A B : MatTwo, A.PosDef → B.PosDef →
      powerMean a (-p) A B ≤ powerMean a q A B) : 1 ≤ p := by
  by_contra hp1
  have hp1' : p < 1 := lt_of_not_ge hp1
  have hlim := scalarCoefficient_limit ha ha1 (neg_lt_zero.mpr hp)
    (by linarith : -1 < -p) hq
  have hnonneg : 0 ≤ -(1-a)^2 := by
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
      with x hx hx1
    exact coefficient_nonneg ha ha1 (neg_ne_zero.mpr hp.ne') hq.ne' hx hx1 horder
  nlinarith [sq_pos_of_pos (sub_pos.mpr ha1)]

/-- Universal harmonic to arithmetic comparison forces both parameters to be at least one. -/
theorem result {α p q : ℝ} (hα : 0 < α) (hα1 : α < 1) (hp : 0 < p) (hq : 0 < q)
    (h : ∀ A B : Matrix (Fin 2) (Fin 2) ℂ, A.PosDef → B.PosDef →
      harmonicMean α p A B ≤ powerMean α q A B) : 1 ≤ p ∧ 1 ≤ q := by
  have hh : ∀ A B : MatTwo, A.PosDef → B.PosDef →
      powerMean α (-p) A B ≤ powerMean α q A B := by
    intro A B hA hB
    rw [← harmonicMean_eq_powerMean hα hα1 hA hB]
    exact h A B hA hB
  exact ⟨first_exponent hα hα1 hp hq hh,
    first_exponent hα hα1 hq hp (powerMean_order_duality hα hα1 hh)⟩

#print axioms result
end D5.S3.Quantum.Matrix.HiaiHarmonicArithmetic
