/- GID: D5/S3/Quantum/Analysis/RefinedBMVPositiveCenterShortGapNormalization
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Logarithmic derivative bounds for the short-gap normalization. -/

import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterCollisionRadicand
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterTailMarginal
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MixedNormalization
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-! # Short-gap normalization for the refined BMV kernel -/

open Filter Set
open scoped Topology

namespace RefinedBMV.PositiveCenter

/-- The weight under the square root in the short-gap normalization. -/
noncomputable def shortGapWeight (h t : ℝ) : ℝ :=
  Real.exp (-((3+2*h)*t)) - 1 + (3+2*h)*upperTailGap h t -
    ((3+h)*(3+2*h)/2)*(upperTailGap h t)^2*Real.exp (-t)

theorem shortGapWeight_pos {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    0 < shortGapWeight h t := by
  rw [shortGapWeight, collisionWeight_eq hh]
  have := collisionWeight_pos h t
  positivity

private theorem hasDerivAt_shortGapWeight {h t : ℝ} (hh : 0 < h) :
    let a := upperTailGap h t
    let b := Real.exp (-(h*t))
    let k := 3+2*h
    let c := (3+h)*k/2
    HasDerivAt (shortGapWeight h)
      (k*(b-Real.exp (-(k*t))) + c*a*Real.exp (-t)*(a-2*b)) t := by
  dsimp only
  let k : ℝ := 3+2*h
  let c : ℝ := (3+h)*k/2
  have hlin : HasDerivAt (fun s : ℝ ↦ k*s) k t := by
    simpa only [mul_one] using (hasDerivAt_id' t).const_mul k
  have he : HasDerivAt (fun s : ℝ ↦ -(k*s)) (-k) t := HasDerivAt.neg hlin
  have hneg : HasDerivAt (fun s : ℝ ↦ -s) (-1) t := HasDerivAt.neg (hasDerivAt_id' t)
  have ha := hasDerivAt_upperTailGap (t := t) hh
  have hd : HasDerivAt (shortGapWeight h) _ t :=
    ((he.exp.sub_const 1).add (ha.const_mul k)).sub
      (((ha.pow 2).const_mul c).mul hneg.exp)
  convert hd using 1
  simp only [Pi.pow_apply]
  dsimp [k, c]
  ring

private theorem shortGap_gap_lower {h t : ℝ} (hh : 0 < h) (hhmax : h ≤ 3 / 11)
    (ht : 4 ≤ t) : 11 / 6 < upperTailGap h t := by
  have ht₀ : 0 < t := by linarith
  have hx : 0 ≤ h*t := by positivity
  have hden : 0 < 1+h*t := by positivity
  have hb : Real.exp (-(h*t)) ≤ 1/(1+h*t) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ hden (by linarith only [Real.add_one_le_exp (h*t)])
  have ha : t/(1+h*t) ≤ upperTailGap h t := by
    apply (le_div_iff₀ hh).2
    apply (le_sub_comm).mp
    calc
      Real.exp (-(h*t)) ≤ 1/(1+h*t) := hb
      _ = 1 - t/(1+h*t)*h := by field_simp [hden.ne']; ring
  apply lt_of_lt_of_le _ ha
  apply (lt_div_iff₀ hden).2
  have hht := mul_le_mul_of_nonneg_right hhmax ht₀.le
  linarith only [ht, hht]

private theorem sinh_le_shortGap_endpoint {x : ℝ} (hx : 0 ≤ x) (hxmax : x ≤ 6 / 11) :
    Real.sinh x ≤ x*(121/115) := by
  have hfac (n : ℕ) : 6^n ≤ Nat.factorial (2*n+1) := by
    induction n with
    | zero => decide
    | succ n ih =>
      have hstep : 6 ≤ (2*n+3)*(2*n+2) :=
        Nat.mul_le_mul (by omega : 3 ≤ 2*n+3) (by omega : 2 ≤ 2*n+2)
      calc
        6^(n+1) = 6*6^n := by rw [pow_succ, mul_comm]
        _ ≤ ((2*n+3)*(2*n+2))*Nat.factorial (2*n+1) := Nat.mul_le_mul hstep ih
        _ = Nat.factorial (2*(n+1)+1) := by
          rw [show 2*(n+1)+1 = (2*n+1+1)+1 by omega,
            Nat.factorial_succ (2*n+1+1), Nat.factorial_succ (2*n+1)]
          ring
  let r : ℝ := (6/11)^2/6
  have hgeo : HasSum (fun n : ℕ ↦ x*r^n) (x*(121/115)) := by
    have hs := (hasSum_geometric_of_lt_one (r := r)
      (by norm_num [r]) (by norm_num [r])).mul_left x
    have hr : (1-r)⁻¹ = (121/115 : ℝ) := by norm_num [r]
    simpa only [hr] using hs
  rw [Real.sinh_eq_tsum, ← hgeo.tsum_eq]
  refine (Real.hasSum_sinh x).summable.tsum_le_tsum (fun n ↦ ?_) hgeo.summable
  have hfn : (6 : ℝ)^n ≤ (Nat.factorial (2*n+1) : ℝ) := by exact_mod_cast hfac n
  calc
    x^(2*n+1)/(Nat.factorial (2*n+1) : ℝ) ≤
        x^(2*n+1)/(6 : ℝ)^n :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hfn
    _ ≤ x*r^n := by
      rw [pow_succ, pow_mul, mul_comm ((x^2)^n), mul_div_assoc]
      dsimp only [r]
      rw [div_pow]
      gcongr

private theorem shortGap_correction_bound {h t : ℝ} (hh : 0 < h) (hhmax : h ≤ 3 / 11)
    (ht : 4 ≤ t) :
    ((3+h)/2)*(upperTailGap h t)^2*Real.exp (-((1-h)*t)) < 3/5 := by
  let S : ℝ → ℝ := fun s ↦ (upperTailGap h s)^2*Real.exp (-((1-h)*s))
  have hd (s : ℝ) : HasDerivAt S
      ((2*upperTailGap h s*Real.exp (-(h*s)) -
        (1-h)*(upperTailGap h s)^2)*Real.exp (-((1-h)*s))) s := by
    have hlin : HasDerivAt (fun u : ℝ ↦ (1-h)*u) (1-h) s := by
      simpa only [mul_one] using (hasDerivAt_id' s).const_mul (1-h)
    have he : HasDerivAt (fun u : ℝ ↦ -((1-h)*u)) (-(1-h)) s := HasDerivAt.neg hlin
    convert ((hasDerivAt_upperTailGap (t := s) hh).pow 2).mul he.exp using 1
    simp only [Pi.pow_apply]
    ring
  have hmono : AntitoneOn S (Ici 4) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 4)
      (fun s _ ↦ (hd s).continuousAt.continuousWithinAt)
      (fun s _ ↦ (hd s).differentiableAt.differentiableWithinAt)
    intro s hs
    have hs₄ : 4 ≤ s := interior_subset hs
    have hs₀ : 0 < s := by linarith
    have hL := (upperTailSlope_bounds hh hs₀).2.1.trans
      (div_le_div_of_nonneg_left zero_le_one (by norm_num : (0 : ℝ) < 4) hs₄)
    have ha : 0 < upperTailGap h s := by
      rw [expGapMean_eq hh]
      exact mul_pos hs₀ (expGapMean_pos h s)
    have hb := upperTailGap_logDeriv hh hs₀
    rw [(hasDerivAt_upperTailGap hh).deriv] at hb
    rw [(hd s).deriv, (div_eq_iff ha.ne').1 hb]
    have hsign : 2*upperTailSlope h s - (1-h) ≤ 0 := by linarith only [hhmax, hL]
    convert mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (upperTailGap h s)) hsign)
      (Real.exp_pos (-((1-h)*s))).le using 1
    ring
  have hS := hmono (self_mem_Ici : (4 : ℝ) ∈ Ici 4) (mem_Ici.mpr ht) ht
  have hsplit : Real.exp (-((1-h)*4)) = Real.exp (-(4 : ℝ))*Real.exp (2*h)^2 := by
    rw [pow_two, ← mul_assoc, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hhyper : upperTailGap h 4 * Real.exp (2*h) = 2*Real.sinh (2*h)/h := by
    rw [upperTailGap, div_mul_eq_mul_div, sub_mul, one_mul, ← Real.exp_add, Real.sinh_eq]
    rw [show -(h*4)+2*h = -(2*h) by ring]
    ring
  have hscaled : upperTailGap h 4 * Real.exp (2*h) ≤ 4*(121/115) := by
    rw [hhyper]
    apply (div_le_iff₀ hh).2
    linarith only [sinh_le_shortGap_endpoint (x := 2*h)
      (by positivity) (by linarith only [hhmax])]
  have hgap₄ := shortGap_gap_lower hh hhmax (t := 4) le_rfl
  have hsquare := pow_le_pow_left₀
    (mul_nonneg (by linarith only [hgap₄]) (Real.exp_pos (2*h)).le) hscaled 2
  have hexp₄ : 50 < Real.exp 4 := by
    have hexp : Real.exp 4 = (Real.exp 1)^4 := by
      convert Real.exp_nat_mul (1 : ℝ) 4 using 2 <;> norm_num
    rw [hexp]
    have hb : (27/10 : ℝ) ≤ Real.exp 1 := le_of_lt <|
      lt_trans (by norm_num) Real.exp_one_gt_d9
    exact lt_of_lt_of_le (by norm_num : (50 : ℝ) < (27/10)^4)
      (pow_le_pow_left₀ (by norm_num) hb 4)
  have he₄ : Real.exp (-(4 : ℝ)) < 1/50 := by
    rw [Real.exp_neg, one_div, inv_lt_inv₀ (Real.exp_pos _) (by norm_num)]
    exact hexp₄
  have hS₄ : S 4 ≤ (4*(121/115))^2*(1/50) := calc
    S 4 = (upperTailGap h 4*Real.exp (2*h))^2*Real.exp (-(4 : ℝ)) := by
      dsimp only [S]
      rw [hsplit]
      ring
    _ ≤ _ := mul_le_mul hsquare he₄.le (Real.exp_pos _).le (by positivity)
  calc
    _ = ((3+h)/2)*S t := by dsimp only [S]; ring
    _ ≤ (18/11)*((4*(121/115))^2*(1/50)) := mul_le_mul
      (by linarith only [hhmax]) (hS.trans hS₄) (by dsimp only [S]; positivity) (by norm_num)
    _ < _ := by norm_num

/-- Logarithmic derivatives of the two normalizing factors on the unbounded
short-gap tail. -/
theorem shortGapNormalization_bounds {h t : ℝ} (hh : 0 < h) (hhmax : h ≤ 3 / 11)
    (ht : 4 ≤ t) :
    let P := fun s ↦ upperTailGap h s / Real.sqrt (shortGapWeight h s)
    let V := fun s ↦ 1 / Real.sqrt (shortGapWeight h s)
    let α := deriv P t / P t
    let β := deriv V t / V t
    0 ≤ α ∧ α < 1/7 ∧ -(1/t) ≤ β ∧ β < 0 := by
  dsimp only
  let a := upperTailGap h t
  let b := Real.exp (-(h*t))
  let k : ℝ := 3+2*h
  let g : ℝ := 3+h
  let c : ℝ := g*k/2
  let E := Real.exp (-(k*t))
  let W := shortGapWeight h t
  let w := k*(b-E)+c*a*Real.exp (-t)*(a-2*b)
  have ht₀ : 0 < t := by linarith
  have ha₁ : 11/6 < a := shortGap_gap_lower hh hhmax ht
  have ha : 0 < a := by linarith only [ha₁]
  have hb : 0 < b := Real.exp_pos _
  have hk : 3 ≤ k := by dsimp [k]; linarith
  have hk₀ : 0 < k := by linarith only [hk]
  have hg : 3 ≤ g := by dsimp [g]; linarith
  have hc : 0 < c := by dsimp only [c]; positivity
  have hW : 0 < W := shortGapWeight_pos hh ht₀
  have hwd : HasDerivAt (shortGapWeight h) w t := hasDerivAt_shortGapWeight hh
  have hW_le : W ≤ k*a := by
    have he : E ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (neg_nonpos.mpr (mul_nonneg hk₀.le ht₀.le))
    have hcorr : 0 ≤ c*a^2*Real.exp (-t) := by positivity
    change E - 1 + k*a - c*a^2*Real.exp (-t) ≤ k*a
    linarith only [he, hcorr]
  have hL : b/a = upperTailSlope h t := by
    simpa only [(hasDerivAt_upperTailGap (t := t) hh).deriv] using
      upperTailGap_logDeriv hh ht₀
  have hL_le : b/a ≤ 1/t := by
    rw [hL]
    exact (upperTailSlope_bounds hh ht₀).2.1
  have hhalf : 0 ≤ a-2*b := by
    have hb₄ := (div_le_iff₀ ha).1 <| hL_le.trans
      (div_le_div_of_nonneg_left zero_le_one (by norm_num : (0 : ℝ) < 4) ht)
    linarith only [ha, hb₄]
  have hE_lt : E < b := Real.exp_lt_exp.mpr (by
    have hgap : 0 < (3+h)*t := by positivity
    dsimp only [k]
    linarith only [hgap])
  have hw_ge : k*(b-E) ≤ w := by
    have hcorr : 0 ≤ c*a*Real.exp (-t)*(a-2*b) := by positivity
    exact le_add_of_nonneg_right hcorr
  have hw_pos : 0 < w := (mul_pos hk₀ (sub_pos.mpr hE_lt)).trans_le hw_ge
  have hscalar : 2/(k*a) + (g/2)*a^2*Real.exp (-((1-h)*t)) < 1 := by
    have hka : 3*(11/6) < k*a :=
      (mul_lt_mul_of_pos_left ha₁ (by norm_num : (0 : ℝ) < 3)).trans_le
        (mul_le_mul_of_nonneg_right hk ha.le)
    have hfirst : 2/(k*a) ≤ 4/11 := calc
      _ ≤ 2/(3*(11/6)) :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hka.le
      _ = _ := by norm_num
    linarith only [hfirst, shortGap_correction_bound hh hhmax ht]
  have hcore : 0 < b*(k*a-2) - c*a^3*Real.exp (-t) := by
    have hka₀ : 0 < k*a := mul_pos hk₀ ha
    have hprod : b*Real.exp (-((1-h)*t)) = Real.exp (-t) := by
      dsimp only [b]
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      0 < b*(k*a)*(1-(2/(k*a)+(g/2)*a^2*Real.exp (-((1-h)*t)))) :=
        mul_pos (mul_pos hb hka₀) (sub_pos.mpr hscalar)
      _ = b*(k*a-2) - c*a^3*(b*Real.exp (-((1-h)*t))) := by
        dsimp only [c]
        field_simp [hka₀.ne']
        <;> ring
      _ = _ := by rw [hprod]
  have hnum : 0 < 2*b*W-a*w := by
    have hidentity : 2*b*W-a*w = b*(k*a-2) - c*a^3*Real.exp (-t) + (2*b+k*a)*E := by
      change 2*b*(E-1+k*a-c*a^2*Real.exp (-t)) -
        a*(k*(b-E)+c*a*Real.exp (-t)*(a-2*b)) = _
      ring
    rw [hidentity]
    exact add_pos hcore (mul_pos (by positivity) (Real.exp_pos _))
  have hsqrt := hwd.sqrt hW.ne'
  have hs : 0 < Real.sqrt W := Real.sqrt_pos.2 hW
  have hsq : (Real.sqrt W)^2 = W := Real.sq_sqrt hW.le
  have hα :
      deriv (fun s ↦ upperTailGap h s / Real.sqrt (shortGapWeight h s)) t /
          (a/Real.sqrt W) = b/a-w/(2*W) := by
    rw [((hasDerivAt_upperTailGap hh).fun_div hsqrt hs.ne').deriv]
    change (b*Real.sqrt W-a*(w/(2*Real.sqrt W)))/(Real.sqrt W)^2 /
      (a/Real.sqrt W) = _
    calc
      _ = b/a-w/(2*(Real.sqrt W)^2) := by field_simp [hs.ne', ha.ne'] <;> ring
      _ = _ := by rw [hsq]
  have hβ :
      deriv (fun s ↦ 1 / Real.sqrt (shortGapWeight h s)) t /
          (1/Real.sqrt W) = -(w/(2*W)) := by
    rw [((hasDerivAt_const t (1 : ℝ)).fun_div hsqrt hs.ne').deriv]
    change (0*Real.sqrt W-1*(w/(2*Real.sqrt W)))/(Real.sqrt W)^2 /
      (1/Real.sqrt W) = _
    calc
      _ = -(w/(2*(Real.sqrt W)^2)) := by field_simp [hs.ne'] <;> ring
      _ = _ := by rw [hsq]
  change
    0 ≤ deriv (fun s ↦ upperTailGap h s / Real.sqrt (shortGapWeight h s)) t /
        (a/Real.sqrt W) ∧
    deriv (fun s ↦ upperTailGap h s / Real.sqrt (shortGapWeight h s)) t /
        (a/Real.sqrt W) < 1/7 ∧
    -(1/t) ≤ deriv (fun s ↦ 1 / Real.sqrt (shortGapWeight h s)) t /
        (1/Real.sqrt W) ∧
    deriv (fun s ↦ 1 / Real.sqrt (shortGapWeight h s)) t /
        (1/Real.sqrt W) < 0
  rw [hα, hβ]
  have hα_pos : 0 < b/a-w/(2*W) := by
    calc
      0 < (2*b*W-a*w)/(2*a*W) := div_pos hnum (by positivity)
      _ = _ := by field_simp [ha.ne', hW.ne']
  have hw_bound : (b-E)/(2*a) ≤ w/(2*W) := calc
    _ = (k*(b-E))/(2*(k*a)) := by field_simp [hk₀.ne', ha.ne']
    _ ≤ (k*(b-E))/(2*W) := div_le_div_of_nonneg_left (by positivity)
      (by positivity) (mul_le_mul_of_nonneg_left hW_le (by norm_num))
    _ ≤ _ := div_le_div_of_nonneg_right hw_ge (by positivity)
  have hE : E = b*Real.exp (-(g*t)) := by
    dsimp only [E, b, g, k]
    rw [← Real.exp_add]
    congr 1
    ring
  have hExp : Real.exp (-(g*t)) ≤ 1/13 := by
    have hgt : 12 ≤ g*t :=
      (show (12 : ℝ) = 3*4 by norm_num).le.trans
        (mul_le_mul hg ht (by norm_num) (by positivity))
    have he := Real.add_one_le_exp (g*t)
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) (by linarith only [he, hgt])
  have hα_upper : b/a-w/(2*W) < 1/7 := calc
    _ ≤ b/a-(b-E)/(2*a) := sub_le_sub_left hw_bound _
    _ = (b/a)*(1+Real.exp (-(g*t)))/2 := by rw [hE]; ring
    _ ≤ (1/4)*(1+1/13)/2 := by
      have hratio := hL_le.trans
        (div_le_div_of_nonneg_left zero_le_one (by norm_num : (0 : ℝ) < 4) ht)
      exact div_le_div_of_nonneg_right
        (mul_le_mul hratio (by linarith only [hExp]) (by positivity) (by norm_num)) (by norm_num)
    _ < _ := by norm_num
  exact ⟨hα_pos.le, hα_upper, by linarith only [hL_le, hα_pos],
    neg_neg_of_pos (div_pos hw_pos (by positivity))⟩

/-- The difference between the two normalization slopes is the logarithmic gap slope. -/
theorem shortGapNormalization_logDiff {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    let P := fun s ↦ upperTailGap h s / Real.sqrt (shortGapWeight h s)
    let V := fun s ↦ 1 / Real.sqrt (shortGapWeight h s)
    deriv P t / P t - deriv V t / V t = upperTailSlope h t := by
  let a := upperTailGap h
  let V : ℝ → ℝ := fun s ↦ 1 / Real.sqrt (shortGapWeight h s)
  let P : ℝ → ℝ := fun s ↦ a s / Real.sqrt (shortGapWeight h s)
  change deriv P t / P t - deriv V t / V t = _
  have hP : P = fun s ↦ a s * V s := by funext s; simp only [P, V, div_eq_mul_inv, one_mul]
  have ha : 0 < a t := by
    unfold a
    rw [expGapMean_eq hh]
    exact mul_pos ht (expGapMean_pos _ _)
  have hW := shortGapWeight_pos hh ht
  have hV : 0 < V t := one_div_pos.mpr (Real.sqrt_pos.mpr hW)
  have hdV : DifferentiableAt ℝ V t := by
    exact (differentiableAt_const (c := 1)).div
      ((hasDerivAt_shortGapWeight hh).sqrt hW.ne').differentiableAt (Real.sqrt_pos.mpr hW).ne'
  have hda : HasDerivAt a (Real.exp (-(h*t))) t := hasDerivAt_upperTailGap hh
  have hp := (hda.fun_mul hdV.hasDerivAt).deriv
  rw [hP, hp]
  have hlog : Real.exp (-(h*t)) / a t = upperTailSlope h t := by
    simpa only [(hasDerivAt_upperTailGap (t := t) hh).deriv] using upperTailGap_logDeriv hh ht
  rw [← hlog]
  field_simp [ha.ne', hV.ne']
  exact add_sub_cancel_right _ _

/-- The upper normalization helps absorb the geometric correction at larger gaps. -/
theorem shortGap_upperLogDeriv_le {h t : ℝ} (hh : 0 < h) (hhmax : h ≤ 3 / 11)
    (ht : 4 ≤ t) :
    let V := fun s ↦ 1 / Real.sqrt (shortGapWeight h s)
    deriv V t / V t ≤ -upperTailSlope h t / 2 := by
  let a := upperTailGap h t
  let b := Real.exp (-(h*t))
  let k : ℝ := 3+2*h
  let g : ℝ := 3+h
  let c : ℝ := g*k/2
  let E := Real.exp (-(k*t))
  let W := shortGapWeight h t
  let w := k*(b-E)+c*a*Real.exp (-t)*(a-2*b)
  have ht₀ : 0 < t := by linarith
  have ha : 0 < a := (by norm_num : (0 : ℝ) < 11 / 6).trans
    (shortGap_gap_lower hh hhmax ht)
  have hW : 0 < W := shortGapWeight_pos hh ht₀
  have hL : b/a = upperTailSlope h t := by
    simpa only [(hasDerivAt_upperTailGap (t := t) hh).deriv] using upperTailGap_logDeriv hh ht₀
  have hba : b ≤ a := by
    have h.inv : 1 / t ≤ 1 := (div_le_one ht₀).mpr (by linarith)
    have hratio := (upperTailSlope_bounds hh ht₀).2.1.trans h.inv
    rw [← hL] at hratio
    simpa using (div_le_iff₀ ha).mp hratio
  have hgeom : b - (b+k*a)*E ≥ 0 := by
    have hb₁ : b ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hh.le ht₀.le))
    have hka := mul_le_mul_of_nonneg_left (upperTailGap_le (t := t) hh) (show 0 ≤ k by positivity)
    have hgt : 0 ≤ g*t := by positivity
    have hexp := Real.sum_le_exp_of_nonneg hgt 3
    norm_num [Finset.sum_range_succ, Nat.factorial] at hexp
    have hgt₃ : 3*t ≤ g*t := mul_le_mul_of_nonneg_right (by dsimp [g]; linarith) ht₀.le
    have hgt₂ := pow_le_pow_left₀ (show 0 ≤ 3*t by positivity) hgt₃ 2
    have hht := mul_le_mul_of_nonneg_right (show h ≤ 1 by linarith) ht₀.le
    have ht₂ : t ≤ t^2 := by nlinarith only [mul_nonneg ht₀.le (show 0 ≤ t-1 by linarith)]
    have hlarge : b+k*a ≤ Real.exp (g*t) := by
      dsimp only [k] at hka ⊢
      dsimp only [g] at hexp hgt₂
      nlinarith only [hexp, hgt₂, hht, ht₂, hb₁, hka, sq_nonneg t]
    have hprod : Real.exp (g*t)*E = b := by
      dsimp [E, b]
      rw [← Real.exp_add]
      congr 1
      dsimp [g, k]
      ring
    exact sub_nonneg.mpr ((mul_le_mul_of_nonneg_right hlarge (Real.exp_pos _).le).trans_eq hprod)
  have hcompare : b*W ≤ a*w := by
    have h := add_nonneg hgeom (mul_nonneg
      (show 0 ≤ c*a^2*Real.exp (-t) by dsimp only [c]; positivity) (sub_nonneg.mpr hba))
    change b*(E-1+k*a-c*a^2*Real.exp (-t)) ≤ a*(k*(b-E)+c*a*Real.exp (-t)*(a-2*b))
    nlinarith only [h]
  have hs : 0 < Real.sqrt W := Real.sqrt_pos.2 hW
  have hs₂ : (Real.sqrt W)^2 = W := Real.sq_sqrt hW.le
  have hW' : HasDerivAt (shortGapWeight h) w t := hasDerivAt_shortGapWeight hh
  change deriv (fun s ↦ 1 / Real.sqrt (shortGapWeight h s)) t / (1 / Real.sqrt W) ≤ _
  rw [((hasDerivAt_const t (1 : ℝ)).fun_div (hW'.sqrt hW.ne') hs.ne').deriv, ← hL]
  have he : (0 * Real.sqrt W - 1 * (w / (2 * Real.sqrt W))) / (Real.sqrt W)^2 /
      (1 / Real.sqrt W) = -(w / (2 * W)) := by
    calc
      _ = -(w / (2 * (Real.sqrt W)^2)) := by simp only [zero_mul, one_mul, zero_sub]; field_simp [hs.ne']
      _ = _ := by rw [hs₂]
  rw [he, neg_div]
  apply neg_le_neg
  rw [div_div]
  exact (div_le_div_iff₀ (by positivity : 0 < a * 2) (by positivity : 0 < 2 * W)).mpr
    (by nlinarith only [hcompare])

/-- A four-point lower bound for the mean of the exponential on a symmetric
interval. The even moments agree through degree four. -/
theorem fourPoint_cosh_lt_sinh_div {z : ℝ} (hz : 0 < z) :
    (9 / 14 : ℝ) * Real.cosh (z / 3) +
      (5 / 14) * Real.cosh (Real.sqrt (11 / 15) * z) < Real.sinh z / z := by
  let m (n : ℕ) : ℝ := (9 / 14) * (1 / 9) ^ n + (5 / 14) * (11 / 15) ^ n
  let f (n : ℕ) : ℝ := m n * (z ^ (2 * n) / ((2 * n).factorial : ℝ))
  let g (n : ℕ) : ℝ := z ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) / z
  have hmoment (n : ℕ) : m n ≤ 1 / (2 * (n : ℝ) + 1) := by
    induction n with
    | zero => norm_num [m]
    | succ n ih =>
      by_cases hn : n < 3
      · interval_cases n <;> norm_num [m]
      · have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 3 ≤ n by omega)
        have hstep : m (n + 1) ≤ (11 / 15) * m n := by
          have hpow : 0 ≤ (1 / 9 : ℝ) ^ n := by positivity
          dsimp only [m]
          rw [pow_succ, pow_succ]
          nlinarith only [hpow]
        have hrate : (11 / 15 : ℝ) * (1 / (2 * n + 1)) ≤ 1 / (2 * (n + 1 : ℕ) + 1) := by
          push_cast
          rw [mul_one_div]
          exact (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by linarith)
        exact hstep.trans ((mul_le_mul_of_nonneg_left ih (by norm_num)).trans hrate)
  have hterms : (fun n : ℕ ↦ (9 / 14 : ℝ) * ((z / 3) ^ (2 * n) / ((2 * n).factorial : ℝ)) +
      (5 / 14) * ((Real.sqrt (11 / 15) * z) ^ (2 * n) / ((2 * n).factorial : ℝ))) = f := by
    funext n
    have hleft : (z / 3) ^ (2 * n) = (1 / 9 : ℝ) ^ n * z ^ (2 * n) := by
      rw [div_pow, pow_mul (3 : ℝ), show (3 : ℝ) ^ 2 = 9 by norm_num, one_div_pow]
      ring
    have hright : (Real.sqrt (11 / 15) * z) ^ (2 * n) =
        (11 / 15 : ℝ) ^ n * z ^ (2 * n) := by
      rw [mul_pow, pow_mul (Real.sqrt _), Real.sq_sqrt (by norm_num)]
    rw [hleft, hright]
    dsimp only [f, m]
    ring
  have hf : HasSum f ((9 / 14 : ℝ) * Real.cosh (z / 3) +
      (5 / 14) * Real.cosh (Real.sqrt (11 / 15) * z)) := by
    rw [← hterms]
    exact ((Real.hasSum_cosh (z / 3)).mul_left (9 / 14 : ℝ)).add
      ((Real.hasSum_cosh (Real.sqrt (11 / 15) * z)).mul_left (5 / 14 : ℝ))
  have hg : HasSum g (Real.sinh z / z) := (Real.hasSum_sinh z).div_const z
  have heq (n : ℕ) : g n = (1 / (2 * (n : ℝ) + 1)) *
      (z ^ (2 * n) / ((2 * n).factorial : ℝ)) := by
    dsimp only [g]
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    push_cast
    field_simp [hz.ne'] <;> ring
  have hle (n : ℕ) : f n ≤ g n := by
    rw [heq]
    exact mul_le_mul_of_nonneg_right (hmoment n) (by positivity)
  have hstrict : f 3 < g 3 := by
    rw [heq]
    apply mul_lt_mul_of_pos_right _ (by positivity)
    norm_num [m]
  rw [← hf.tsum_eq, ← hg.tsum_eq]
  exact Summable.tsum_lt_tsum hle hstrict hf.summable hg.summable

open scoped BigOperators

private theorem sum_exp_centered_range (n : ℕ) {x : ℝ} (hx : 0 < x) :
    (∑ j ∈ Finset.range n, Real.exp (((n : ℝ) - 1 - 2 * j) * x)) =
      Real.sinh ((n : ℝ) * x) / Real.sinh x := by
  have hratio : Real.exp (-2 * x) ≠ 1 := by
    rw [← Real.exp_zero]
    exact ne_of_lt (Real.exp_lt_exp.mpr (by linarith))
  have hneg (s : ℝ) : Real.exp (-2 * s) - 1 = -2 * Real.exp (-s) * Real.sinh s := by
    have h₁ : Real.exp (-s) * Real.exp s = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have h₂ : Real.exp (-s) * Real.exp (-s) = Real.exp (-2 * s) := by
      rw [← Real.exp_add, show -s + -s = -2 * s by ring]
    rw [Real.sinh_eq]
    linear_combination h₁ - h₂
  have hcancel : Real.exp (((n : ℝ) - 1) * x) * Real.exp (-((n : ℝ) * x)) =
      Real.exp (-x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = Real.exp (((n : ℝ) - 1) * x) * ∑ j ∈ Finset.range n, Real.exp (-2 * x) ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    _ = _ := by
      rw [geom_sum_eq hratio, ← Real.exp_nat_mul, ← mul_div_assoc,
        show (n : ℝ) * (-2 * x) = -2 * ((n : ℝ) * x) by ring]
      apply (div_eq_div_iff (sub_ne_zero.mpr hratio) (Real.sinh_pos_iff.mpr hx).ne').mpr
      rw [hneg ((n : ℝ) * x), hneg x]
      linear_combination (-2 * Real.sinh ((n : ℝ) * x) * Real.sinh x) * hcancel

theorem compositionMoment_eq_conditioned (p : ℕ) (u v : ℝ) :
    let h := 3 / (p : ℝ)
    1 + compositionMoment p u v =
      (∑ i ∈ Finset.range (p + 1), Real.exp ((h * i - 1) * v) *
        ∑ j ∈ Finset.range (p + 1 - i), Real.exp ((h * (↑(p - i - j) : ℝ) - 1) * u)) /
        ((DimThree.gaps p).length : ℝ) := by
  let f (g : ℕ × ℕ × ℕ) :=
    Real.exp ((3 * (g.2.1 : ℝ) / p - 1) * u + (3 * (g.2.2 : ℝ) / p - 1) * v)
  change 1 + (((DimThree.gaps p).map f).sum / ((DimThree.gaps p).length : ℝ) - 1) = _
  rw [add_comm (1 : ℝ), sub_add_cancel]
  have hcycle := ((DimThree.gaps_cycle_all p).map f).sum_eq
  rw [← hcycle]
  congr 1
  simp only [List.map_map, DimThree.gaps, List.flatMap_def, List.map_flatten,
    List.sum_flatten, Function.comp_def, ← List.sum_toFinset _ List.nodup_range,
    List.toFinset_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Real.exp_add]
  dsimp [f]
  congr 1
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  ring

theorem compositionGap_conditional_sum {p i : ℕ} (hi : i ≤ p) {h a : ℝ}
    (hh : 0 < h) (ha : 0 < a) (hp : h * (p : ℝ) = 3) :
    let n := p + 1 - i
    let y := h * i - 1
    (∑ j ∈ Finset.range n, Real.exp ((h * (↑(p - i - j) : ℝ) - 1) * (2 * a))) =
      (n : ℝ) * Real.exp (-a * y) * (h * a / Real.sinh (h * a)) *
        (Real.sinh ((n : ℝ) * (h * a)) / ((n : ℝ) * (h * a))) := by
  let n := p + 1 - i
  let y := h * (i : ℝ) - 1
  have hn : (n : ℝ) = (p : ℝ) + 1 - i := by
    dsimp [n]
    rw [Nat.cast_sub (by omega)]
    push_cast
    rfl
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by dsimp [n]; omega)
  have hx := mul_pos hh ha
  change (∑ j ∈ Finset.range n, Real.exp ((h * (↑(p - i - j) : ℝ) - 1) * (2 * a))) =
    (n : ℝ) * Real.exp (-a * y) * (h * a / Real.sinh (h * a)) *
      (Real.sinh ((n : ℝ) * (h * a)) / ((n : ℝ) * (h * a)))
  calc
    _ = Real.exp (-a * y) *
        ∑ j ∈ Finset.range n, Real.exp (((n : ℝ) - 1 - 2 * j) * (h * a)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have hk : (↑(p - i - j) : ℝ) = (p : ℝ) - i - j := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub hi]
      rw [hk, ← Real.exp_add, hn]
      congr 1
      dsimp [y]
      linear_combination a * hp
    _ = _ := by
      rw [sum_exp_centered_range n hx]
      field_simp [hx.ne', hnpos.ne', (Real.sinh_pos_iff.mpr hx).ne']

/-- The strict four-point lower bound for the joint composition moment in (29). -/
theorem compositionMoment_fourPoint_lower {p : ℕ} (hp : 0 < p) {u : ℝ} (hu : 0 < u)
    (v : ℝ) :
    let h := 3 / (p : ℝ)
    let a := u / 2
    let t := v - a
    let c := 2 + h
    let r := Real.sqrt (11 / 15)
    let F := fun s ↦ 1 + compositionMoment p 0 s
    (h * a / (2 * Real.sinh (h * a))) *
      ((9 / 14) * (Real.exp (c * (a / 3)) * F (t - a / 3) +
        Real.exp (-(c * (a / 3))) * F (t + a / 3)) +
        (5 / 14) * (Real.exp (c * (r * a)) * F (t - r * a) +
        Real.exp (-(c * (r * a))) * F (t + r * a))) <
      1 + compositionMoment p u v := by
  let h := 3 / (p : ℝ)
  let a := u / 2
  let t := v - a
  let c := 2 + h
  let r := Real.sqrt (11 / 15)
  let F := fun s ↦ 1 + compositionMoment p 0 s
  let N := ((DimThree.gaps p).length : ℝ)
  let n (i : ℕ) := p + 1 - i
  let y (i : ℕ) := h * (i : ℝ) - 1
  let z (i : ℕ) := (n i : ℝ) * (h * a)
  let scale := h * a / Real.sinh (h * a)
  let S := Finset.range (p + 1)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hh : 0 < h := div_pos (by norm_num) hpR
  have ha : 0 < a := half_pos hu
  have hscale : 0 < scale := div_pos (mul_pos hh ha) (Real.sinh_pos_iff.mpr (mul_pos hh ha))
  have htotal : h * (p : ℝ) = 3 := div_mul_cancel₀ _ hpR.ne'
  have hN : 0 < N := by
    have hm : (0, 0, p) ∈ DimThree.gaps p :=
      (DimThree.mem_gaps_iff_total p (0, 0, p)).mpr (by simp)
    dsimp only [N]
    exact_mod_cast List.length_pos_of_mem hm
  have hmarg (s : ℝ) : N * F s = ∑ i ∈ S, (n i : ℝ) * Real.exp (y i * s) := by
    dsimp only [F]
    rw [compositionMoment_eq_conditioned p 0 s, ← mul_div_assoc, mul_div_cancel_left₀ _ hN.ne']
    apply Finset.sum_congr rfl
    intro i _
    simp [n, y, h, mul_comm]
  let pair (d : ℝ) (i : ℕ) := (n i : ℝ) * Real.exp (y i * t) * Real.cosh ((c - y i) * d)
  have hpair (d : ℝ) :
      ∑ i ∈ S, pair d i =
        (Real.exp (c * d) * (N * F (t - d)) + Real.exp (-(c * d)) * (N * F (t + d))) / 2 := by
    rw [hmarg, hmarg, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    have hplus : Real.exp (y i * t) * Real.exp ((c - y i) * d) =
        Real.exp (c * d) * Real.exp (y i * (t - d)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have hminus : Real.exp (y i * t) * Real.exp (-((c - y i) * d)) =
        Real.exp (-(c * d)) * Real.exp (y i * (t + d)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    dsimp only [pair]
    rw [Real.cosh_eq]
    linear_combination (n i : ℝ) / 2 * (hplus + hminus)
  have hsum :
      (∑ i ∈ S, scale * ((9 / 14) * pair (a / 3) i + (5 / 14) * pair (r * a) i)) <
        ∑ i ∈ S, Real.exp (y i * v) *
          ∑ j ∈ Finset.range (n i), Real.exp ((h * (↑(p - i - j) : ℝ) - 1) * u) := by
    apply Finset.sum_lt_sum_of_nonempty (by simp [S])
    intro i hi
    have hip : i ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hnpos : (0 : ℝ) < n i := by exact_mod_cast (show 0 < n i by dsimp [n]; omega)
    have hncast : (n i : ℝ) = (p : ℝ) + 1 - i := by
      dsimp [n]
      rw [Nat.cast_sub (by omega)]
      push_cast
      rfl
    have hz : z i = (c - y i) * a := by
      dsimp only [z, c, y]
      rw [hncast]
      linear_combination a * htotal
    have hquad := fourPoint_cosh_lt_sinh_div (z := z i) (by positivity)
    rw [show z i / 3 = (c - y i) * (a / 3) by rw [hz]; ring,
      show Real.sqrt (11 / 15) * z i = (c - y i) * (r * a) by rw [hz]; dsimp [r]; ring] at hquad
    have hexp : Real.exp (y i * v) * Real.exp (-a * y i) = Real.exp (y i * t) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [t]
      ring
    calc
      _ < scale * ((n i : ℝ) * Real.exp (y i * t) * (Real.sinh (z i) / z i)) := by
        apply mul_lt_mul_of_pos_left _ hscale
        calc
          _ = (n i : ℝ) * Real.exp (y i * t) *
              ((9 / 14) * Real.cosh ((c - y i) * (a / 3)) +
                (5 / 14) * Real.cosh ((c - y i) * (r * a))) := by dsimp only [pair]; ring
          _ < _ := mul_lt_mul_of_pos_left hquad (mul_pos hnpos (Real.exp_pos _))
      _ = _ := by
        rw [show u = 2 * a by dsimp [a]; ring, compositionGap_conditional_sum hip hh ha htotal]
        change _ = Real.exp (y i * v) *
          ((n i : ℝ) * Real.exp (-a * y i) * scale * (Real.sinh (z i) / z i))
        rw [← hexp]
        ring
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hpair] at hsum
  dsimp only
  rw [compositionMoment_eq_conditioned p u v, lt_div_iff₀ hN]
  refine lt_of_eq_of_lt ?_ hsum
  dsimp only [scale, F, N, c, r, t, a, h]
  ring

#print axioms compositionMoment_fourPoint_lower
#print axioms fourPoint_cosh_lt_sinh_div
#print axioms shortGapWeight_pos
#print axioms shortGapNormalization_bounds

noncomputable section

private def gapRate (p : ℕ) : ℝ := 3 / (p : ℝ)

private def gapExponent (p i : ℕ) : ℝ := gapRate p * i - 1

private def geometricMarginal (p : ℕ) (t : ℝ) : ℝ :=
  (∑ i ∈ Finset.range (p + 1), Real.exp (gapExponent p i * t)) /
    ((DimThree.gaps p).length : ℝ)

private theorem gapRate_pos {p : ℕ} (hp : 0 < p) : 0 < gapRate p :=
  div_pos (by norm_num) (by exact_mod_cast hp)

private theorem gapRate_mul {p : ℕ} (hp : 0 < p) : gapRate p * p = 3 :=
  div_mul_cancel₀ _ (by exact_mod_cast hp.ne')

private theorem hasDerivAt_geometricMarginal {p : ℕ} (hp : 0 < p) (t : ℝ) :
    HasDerivAt (geometricMarginal p)
      ((2 + gapRate p) * geometricMarginal p t - gapRate p * (1 + compositionMoment p 0 t)) t := by
  have h := (HasDerivAt.fun_sum (u := Finset.range (p + 1)) (fun i _ ↦
    ((hasDerivAt_id' t).const_mul (gapExponent p i)).exp)).div_const
      ((DimThree.gaps p).length : ℝ)
  refine h.congr_deriv ?_
  rw [compositionMoment_eq_conditioned, geometricMarginal, ← mul_div_assoc, ← mul_div_assoc,
    ← sub_div, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hip : i ≤ p := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  simp only [mul_one, mul_zero, Real.exp_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [Nat.cast_sub (by omega)]
  push_cast
  have he : gapExponent p i = 3 / (p : ℝ) * i - 1 := rfl
  rw [← he]
  unfold gapExponent
  linear_combination Real.exp ((gapRate p * i - 1) * t) * gapRate_mul hp

private theorem compositionMoment_geometric {p : ℕ} (hp : 0 < p) {u : ℝ} (hu : 0 < u)
    (v : ℝ) :
    let h := gapRate p
    1 + compositionMoment p u v =
      (Real.exp u * geometricMarginal p (v-u) -
        Real.exp (-(1+h)*u) * geometricMarginal p v) / (1 - Real.exp (-h*u)) := by
  let h := gapRate p
  let q := Real.exp (-h*u)
  have hq : q < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos (gapRate_pos hp) hu])
  have htotal : h * (p : ℝ) = 3 := gapRate_mul hp
  rw [compositionMoment_eq_conditioned]
  change (∑ i ∈ Finset.range (p+1), Real.exp ((h*i-1)*v) *
      ∑ j ∈ Finset.range (p+1-i), Real.exp ((h * (↑(p-i-j) : ℝ)-1)*u)) / _ = _
  unfold geometricMarginal gapExponent
  rw [← mul_div_assoc, ← mul_div_assoc, ← sub_div, div_div,
    mul_comm ((DimThree.gaps p).length : ℝ), ← div_div]
  congr 1
  apply (eq_div_iff (sub_pos.mpr hq).ne').mpr
  rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hip : i ≤ p := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hn : ((p + 1 - i : ℕ) : ℝ) = (p : ℝ) + 1 - i := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    rfl
  have hjoint :
      ∑ j ∈ Finset.range (p+1-i), Real.exp ((h * (↑(p-i-j) : ℝ)-1)*u) =
        Real.exp ((2-h*i)*u) * ∑ j ∈ Finset.range (p+1-i), q^j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [Nat.cast_sub (by omega), Nat.cast_sub hip, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    linear_combination u * htotal
  rw [hjoint, mul_assoc, mul_assoc, geom_sum_mul_neg q, mul_sub, mul_one, ← Real.exp_nat_mul]
  rw [hn, mul_sub]
  simp only [← Real.exp_add]
  change Real.exp _ - Real.exp _ = Real.exp _ - Real.exp _
  congr 2
  · dsimp only [h]; ring
  · dsimp only [h]; linear_combination -u * gapRate_mul hp

private def gapFactor (p : ℕ) (u : ℝ) : ℝ :=
  gapRate p / (1 - Real.exp (-gapRate p*u))

private theorem hasDerivAt_compositionMoment_geometric_fst {p : ℕ} (hp : 0 < p)
    {u : ℝ} (hu : 0 < u) (v : ℝ) :
    HasDerivAt (fun x ↦ 1 + compositionMoment p x v)
      (-(1 + gapFactor p u) * (1 + compositionMoment p u v) +
        gapFactor p u * Real.exp u * (1 + compositionMoment p 0 (v-u))) u := by
  let h := gapRate p
  let S := geometricMarginal p
  let W := fun x : ℝ ↦ 1 - Real.exp (-h*x)
  let J := fun x : ℝ ↦ Real.exp x * S (v-x) - Real.exp (-(1+h)*x) * S v
  have hW : W u ≠ 0 :=
    (sub_pos.mpr <| Real.exp_lt_one_iff.mpr <| by nlinarith [mul_pos (gapRate_pos hp) hu]).ne'
  have hW' : HasDerivAt W (h * Real.exp (-h*u)) u := by
    convert (hasDerivAt_const u (1 : ℝ)).fun_sub
      (((hasDerivAt_id' u).const_mul (-h)).exp) using 1
    ring
  have hS := (hasDerivAt_geometricMarginal hp (v-u)).comp u
    ((hasDerivAt_const u v).fun_sub (hasDerivAt_id' u))
  have hJ : HasDerivAt J
      (-(1+h) * J u + h * Real.exp u * (1 + compositionMoment p 0 (v-u))) u := by
    have hd := ((Real.hasDerivAt_exp u).mul hS).fun_sub
      ((((hasDerivAt_id' u).const_mul (-(1+h))).exp).mul_const (S v))
    refine hd.congr_deriv ?_
    change Real.exp u * S (v-u) +
      Real.exp u * (((2+h) * S (v-u) - h * (1 + compositionMoment p 0 (v-u))) * (0-1)) -
      Real.exp (-(1+h)*u) * (-(1+h)*1) * S v = _
    unfold J
    ring
  refine ((hJ.div hW' hW).congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [eventually_gt_nhds hu] with x hx
    exact compositionMoment_geometric hp hx v
  · have hj : J u = (1 + compositionMoment p u v) * W u :=
      (eq_div_iff hW).mp (compositionMoment_geometric hp hu v) |>.symm
    rw [hj]
    change _ = -(1 + h / W u) * _ + h / W u * _ * _
    field_simp [hW]
    unfold W
    ring

private theorem hasDerivAt_compositionMoment_geometric_snd {p : ℕ} (hp : 0 < p)
    {u : ℝ} (hu : 0 < u) (v : ℝ) :
    HasDerivAt (fun y ↦ 1 + compositionMoment p u y)
      ((2 + gapRate p) * (1 + compositionMoment p u v) +
        gapFactor p u * Real.exp (-(1+gapRate p)*u) * (1 + compositionMoment p 0 v) -
        gapFactor p u * Real.exp u * (1 + compositionMoment p 0 (v-u))) v := by
  let h := gapRate p
  let W := 1 - Real.exp (-h*u)
  let J := fun y : ℝ ↦ Real.exp u * geometricMarginal p (y-u) -
    Real.exp (-(1+h)*u) * geometricMarginal p y
  have hs := (hasDerivAt_geometricMarginal hp (v-u)).comp v ((hasDerivAt_id' v).sub_const u)
  have hJ : HasDerivAt J
      ((2+h) * J v + h * Real.exp (-(1+h)*u) * (1 + compositionMoment p 0 v) -
        h * Real.exp u * (1 + compositionMoment p 0 (v-u))) v := by
    have hd := (hs.const_mul (Real.exp u)).fun_sub
      ((hasDerivAt_geometricMarginal hp v).const_mul (Real.exp (-(1+h)*u)))
    refine hd.congr_deriv ?_
    dsimp only [J, h]
    ring
  refine ((hJ.div_const W).congr_of_eventuallyEq
    (Eventually.of_forall (compositionMoment_geometric hp hu))).congr_deriv ?_
  have hj : J v / W = 1 + compositionMoment p u v := (compositionMoment_geometric hp hu v).symm
  rw [add_sub_assoc, add_div, sub_div, mul_div_assoc, hj]
  change _ = (2+h) * _ + h / W * _ * _ - h / W * _ * _
  ring

private theorem compositionMoment_marginal_sum (p : ℕ) (t : ℝ) :
    compositionMoment p 0 t = (∑ i ∈ Finset.range (p + 1),
      (↑(p + 1 - i) : ℝ) * Real.exp (gapExponent p i * t)) /
        ((DimThree.gaps p).length : ℝ) - 1 := by
  have h := compositionMoment_eq_conditioned p 0 t
  simp only [mul_zero, Real.exp_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one] at h
  rw [eq_sub_iff_add_eq', h]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

private theorem compositionMoment_marginal_smooth (p : ℕ) :
    ContDiff ℝ 2 (compositionMoment p 0) := by
  change ContDiff ℝ 2 (fun t ↦ compositionMoment p 0 t)
  simp_rw [compositionMoment_marginal_sum]
  exact ((ContDiff.sum fun i _ ↦ by fun_prop).div_const _).sub contDiff_const

private def jointMomentJet (p : ℕ) (u v : ℝ) : MixedJet ℝ :=
  let R := compositionMoment p 0
  let H := 1 + compositionMoment p u v
  let k := gapFactor p u
  let Jv := (2 + gapRate p) * H + k * Real.exp (-(1+gapRate p)*u) * (1 + R v) -
    k * Real.exp u * (1 + R (v-u))
  ⟨compositionMoment p u v, -(1+k)*H + k*Real.exp u*(1 + R (v-u)), Jv,
    -(1+k)*Jv + k*Real.exp u*deriv R (v-u)⟩

private theorem jointMomentJet_isAt {p : ℕ} (hp : 0 < p) {u v : ℝ} (hu : 0 < u) :
    MixedJet.IsAt (jointMomentJet p) u v := by
  have hv := hasDerivAt_compositionMoment_geometric_snd hp hu v
  refine ⟨Eventually.of_forall fun y ↦ ?_, ?_, ?_⟩
  · simpa only [jointMomentJet, add_sub_cancel_left] using
      (hasDerivAt_compositionMoment_geometric_fst hp hu y).sub_const 1
  · simpa only [jointMomentJet, add_sub_cancel_left] using hv.sub_const 1
  · have hd := ((compositionMoment_marginal_smooth p).differentiable (by norm_num)
      (v-u)).hasDerivAt.comp v ((hasDerivAt_id' v).sub_const u)
    have hm := (hv.const_mul (-(1+gapFactor p u))).fun_add
      ((hd.const_add 1).const_mul (gapFactor p u * Real.exp u))
    simpa only [jointMomentJet, Function.comp_apply, mul_one] using hm

/-- The affine expression (30) for the joint exponential moment in the mixed derivative. -/
def compactMixedT (p : ℕ) (u v Z : ℝ) : ℝ :=
  let h := gapRate p
  let R := compositionMoment p 0
  let a := reflectedHalfLogSlope R u
  let b := reflectedHalfLogSlope R v
  let k := gapFactor p u
  let γ := 1 + k + a
  (-γ)*(2+h-b)*Z - γ*k*Real.exp (-(1+h)*u)*(1+R v) +
    k*Real.exp u*((γ-b)*(1+R (v-u)) + deriv R (v-u)) - a*b

/-- The normalized marginal radical contribution (31). -/
def compactMixedQ (p : ℕ) (u v : ℝ) : ℝ :=
  let R := compositionMoment p 0
  let r := marginalLogSlope R
  let a := reflectedHalfLogSlope R u
  let b := reflectedHalfLogSlope R v
  let d := v-u
  Real.sqrt (R v * R d) * (-deriv r d / 2 - (r d + 2*a)*(r v + r d - 2*b)/4)

/-- Exact independent-variable mixed differentiation of the actual log kernel, (32). -/
theorem logKernel_mixed_eq_compactMixed {p : ℕ} (hp : 0 < p) {u v : ℝ}
    (hu : 0 < u) (huv : u < v) :
    Real.sqrt (compositionMoment p 0 (-u) * compositionMoment p 0 (-v)) *
      deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v =
      compactMixedT p u v (1 + compositionMoment p u v) - compactMixedQ p u v := by
  have h := mixed_normalized_marginal_sub (compositionMoment_marginal_smooth p)
    (fun _ ht ↦ compositionMoment_marginal_pos hp ht) hu huv
    (jointMomentJet_isAt (v := v) hp hu)
  change Real.sqrt (compositionMoment p 0 (-u) * compositionMoment p 0 (-v)) *
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v = _ at h
  rw [h]
  dsimp only [compactMixedT, compactMixedQ, jointMomentJet]
  ring

/-- The four marginal evaluations in the strict lower bound (29). -/
def compositionMomentFourPoint (p : ℕ) (u v : ℝ) : ℝ :=
  let h := gapRate p
  let a := u / 2
  let t := v - a
  let c := 2 + h
  let r := Real.sqrt (11 / 15)
  let F := fun s ↦ 1 + compositionMoment p 0 s
  (h * a / (2 * Real.sinh (h * a))) *
    ((9 / 14) * (Real.exp (c * (a / 3)) * F (t - a / 3) +
      Real.exp (-(c * (a / 3))) * F (t + a / 3)) +
      (5 / 14) * (Real.exp (c * (r * a)) * F (t - r * a) +
      Real.exp (-(c * (r * a))) * F (t + r * a)))

private theorem reflectedHalfLogSlope_nonneg {p : ℕ} (hp : 0 < p) {u : ℝ} (hu : 0 < u) :
    0 ≤ reflectedHalfLogSlope (compositionMoment p 0) u := by
  let f (x : ℝ) := compositionMoment p 0 (-x)
  have hN : (0 : ℝ) < (DimThree.gaps p).length := by
    exact_mod_cast (DimThree.word_counts_all p).2.1
  have hsum (s : Finset ℕ) :
      ConvexOn ℝ univ (fun x ↦ ∑ i ∈ s, (↑(p + 1 - i) : ℝ) *
        Real.exp (gapExponent p i * (-x))) := by
    induction s using Finset.induction_on with
    | empty => simpa using convexOn_const (0 : ℝ) (convex_univ : Convex ℝ (univ : Set ℝ))
    | insert i s hi ih =>
      have he := convexOn_exp.comp_linearMap (LinearMap.mul ℝ ℝ (-gapExponent p i))
      rw [preimage_univ, show Real.exp ∘ (LinearMap.mul ℝ ℝ (-gapExponent p i)) =
        (fun x ↦ Real.exp (gapExponent p i * (-x))) from
          funext fun x ↦ congrArg Real.exp ((neg_mul _ _).trans (mul_neg _ _).symm)] at he
      rw [show (fun x : ℝ ↦ ∑ j ∈ insert i s, (↑(p+1-j) : ℝ) *
        Real.exp (gapExponent p j * (-x))) = _ by funext x; rw [Finset.sum_insert hi]]
      exact (he.smul (by positivity : 0 ≤ ((p + 1 - i : ℕ) : ℝ))).add ih
  have hc : ConvexOn ℝ univ f := by
    unfold f
    simp_rw [compositionMoment_marginal_sum, div_eq_inv_mul]
    simp only [sub_eq_add_neg]
    exact ((hsum _).smul (inv_nonneg.mpr hN.le)).add_const (-1)
  have hdiff : DifferentiableAt ℝ f u :=
    ((compositionMoment_marginal_smooth p).differentiable (by norm_num) (-u)).comp u
      differentiableAt_id.neg
  have hsec := hc.slope_le_deriv (mem_univ 0) (mem_univ u) hu hdiff
  have hzero : f 0 = 0 := by
    simp [f, compositionMoment, hN.ne']
  have hfu : 0 < f u := compositionMoment_marginal_pos hp (neg_ne_zero.mpr hu.ne')
  have hder : 0 ≤ deriv f u := by
    rw [slope_def_field, hzero, sub_zero, sub_zero] at hsec
    exact (div_pos hfu hu).le.trans hsec
  exact div_nonneg (div_nonneg hder hfu.le) (by norm_num)

/-- The affine dependence on the joint moment is strictly decreasing for `1 ≤ v`. -/
theorem compactMixedT_strictAnti {p : ℕ} (hp : 0 < p) {u v : ℝ}
    (hu : 0 < u) (hv : 1 ≤ v) : StrictAnti (compactMixedT p u v) := by
  have hvpos : 0 < v := zero_lt_one.trans_le hv
  have hk : 0 < gapFactor p u := div_pos (gapRate_pos hp)
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos (gapRate_pos hp) hu])))
  have ha := reflectedHalfLogSlope_nonneg hp hu
  have hb' : 2 / v ≤ 2 := (div_le_iff₀ hvpos).mpr (by linarith)
  have hb : reflectedHalfLogSlope (compositionMoment p 0) v ≤ 3 / 2 := by
    unfold reflectedHalfLogSlope
    linarith [upperTail_marginal_logDeriv hp hvpos]
  have hγ : 0 < 1 + gapFactor p u + reflectedHalfLogSlope (compositionMoment p 0) u := by
    linarith
  have hc : 0 < 2 + gapRate p - reflectedHalfLogSlope (compositionMoment p 0) v := by
    linarith [gapRate_pos hp]
  intro Z₁ Z₂ hZ
  dsimp only [compactMixedT]
  linarith only [mul_lt_mul_of_neg_left hZ (mul_neg_of_neg_of_pos (neg_neg_of_pos hγ) hc)]

/-- Above unit upper gap, inserting the four-point lower bound gives a strict
upper bound on the actual normalized mixed derivative. -/
theorem logKernel_mixed_lt_fourPoint {p : ℕ} (hp : 0 < p) {u v : ℝ}
    (hu : 0 < u) (huv : u < v) (hv : 1 ≤ v) :
    Real.sqrt (compositionMoment p 0 (-u) * compositionMoment p 0 (-v)) *
      deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v <
      compactMixedT p u v (compositionMomentFourPoint p u v) - compactMixedQ p u v := by
  rw [logKernel_mixed_eq_compactMixed hp hu huv]
  exact sub_lt_sub_right (compactMixedT_strictAnti hp hu hv
    (show compositionMomentFourPoint p u v < 1 + compositionMoment p u v from
      compositionMoment_fourPoint_lower hp hu v)) _

#print axioms logKernel_mixed_eq_compactMixed
#print axioms logKernel_mixed_lt_fourPoint
end

end RefinedBMV.PositiveCenter
