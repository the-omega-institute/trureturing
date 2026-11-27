/- GID: D5/S3/Quantum/Semigroups/WuCubicOneModeEquality
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuCubicOneModeEquality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Equality for positive-definite one-mode observables in Wu's cubic deficit. -/

import D5.S3.Quantum.Semigroups.WuCubicConditionalTensorization
import D5.S3.Quantum.Semigroups.WuCubicHotInnerPartialTrace

/-! The literal Wu cubic deficit on a lifted positive-definite qubit vanishes
exactly at scalar observables. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix Set
open scoped BigOperators ComplexOrder Kronecker MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Semigroups.WuCubicOneModeEquality

open WuCubicOperatorBridge (Mat)
open WuCubicOperatorNormalization (operatorDeficit operatorDeficit_scalar)
open WuCubicHotInnerPartialTrace (Local gibbs lift product_energy rightGenerator)
open WuRepeatedMiddleCubic (alpha oneModeDeficit)
open private h c cutA cutB entropyPair gibbsLow gibbsHigh gibbsOccupation from
  D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private G N Q complete_square G_gibbs G_one hasDerivAt_G continuousOn_G
  slope_lt_gibbs slope_gt_gibbs c_pos cutB_gibbs cutB_factor from
  D5.S3.Quantum.Semigroups.WuOneModeCubic
open private rootScale rootScale_pos rootRatio rootRatio_sq from
  D5.S3.Quantum.Semigroups.WuCubicOperatorBridge
open private root rootValues root_posDef sqrt_rootScale_sq gibbs_trace
  log_difference cubed_base sandwich_lift from
  D5.S3.Quantum.Semigroups.WuCubicHotInnerPartialTrace
open private oneModeOperatorDeficit oneModeEnergy modularJump qubitJump gibbsDensity
  cubicMass cubicEntropy one_mode_operator_nonneg one_mode_scalar_identity
  one_mode_energy_diagonal qubit_diagonal_moments trace_cube_log trace_cube moment from
  D5.S3.Quantum.Semigroups.WuCubicConditionalTensorization

private theorem G_at_minimum {r : ℝ} (hr : 1 ≤ r) : G r r = 0 := by
  rcases hr.eq_or_lt with hr | hr
  · subst r
    exact G_one
  · exact G_gibbs hr

private theorem G_pos_off_minimum {r t : ℝ} (hr : 1 ≤ r) (ht : 1 ≤ t) (hne : t ≠ r) :
    0 < G r t := by
  have hcont {a b : ℝ} (ha : 1 ≤ a) : ContinuousOn (G r) (Icc a b) :=
    (continuousOn_G hr).mono fun _ hx => zero_lt_one.trans_le (ha.trans hx.1)
  rcases lt_or_gt_of_ne hne with htr | hrt
  · have hanti : StrictAntiOn (G r) (Icc t r) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc t r) (hcont ht)
      intro x hx
      rw [interior_Icc] at hx
      have hx1 := ht.trans_lt hx.1
      rw [(hasDerivAt_G hr (zero_lt_one.trans hx1)).deriv]
      exact mul_neg_of_pos_of_neg (by positivity) (slope_lt_gibbs hx1 hx.2)
    simpa only [G_at_minimum hr] using
      hanti ⟨le_rfl, htr.le⟩ ⟨htr.le, le_rfl⟩ htr
  · have hmono : StrictMonoOn (G r) (Icc r t) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc r t) (hcont hr)
      intro x hx
      rw [interior_Icc] at hx
      rw [(hasDerivAt_G hr (zero_lt_one.trans_le (hr.trans hx.1.le))).deriv]
      exact mul_pos (by positivity) (slope_gt_gibbs hr hx.1)
    simpa only [G_at_minimum hr] using
      hmono ⟨le_rfl, hrt.le⟩ ⟨hrt.le, le_rfl⟩ hrt

private theorem cut_center_gibbs {r : ℝ} (hr : 1 < r) :
    N r r / (2 * c r * (r - 1) * (r + 1)) = 1 := by
  have hB := cutB_gibbs hr
  rw [cutB_factor, cutA] at hB
  have hden : 0 < 2 * c r * (r - 1) * (r + 1) := by
    have := c_pos hr.le
    have := sub_pos.mpr hr
    have := zero_lt_one.trans hr
    positivity
  apply (div_eq_iff hden.ne').mpr
  apply mul_left_cancel₀ (sub_ne_zero.mpr hr.ne')
  linear_combination hB

private theorem one_mode_distinct_eq_zero {r v w z : ℝ} (hr : 1 ≤ r)
    (hv : 0 < v) (hvw : v < w) :
    oneModeDeficit r v w z = 0 ↔ w = r * v ∧ z = -1 := by
  let t := w / v
  have ht : 1 < t := (lt_div_iff₀ hv).mpr (by simpa using hvw)
  have hw : w = v * t := by dsimp [t]; field_simp [hv.ne']
  have hmass : 0 < v ^ 3 + (v * t) ^ 3 := by have := zero_lt_one.trans ht; positivity
  have hA : 0 < cutA r 1 t / (2 * (1 + t ^ 3)) := by
    have := c_pos hr
    have := sub_pos.mpr ht
    have := zero_lt_one.trans ht
    unfold cutA
    positivity
  have hratio : w = r * v ↔ t = r := by
    dsimp [t]
    rw [div_eq_iff hv.ne']
  rw [hratio, hw, complete_square hr hv ht]
  simp only [mul_eq_zero, hmass.ne', false_or]
  constructor
  · intro hz
    have htr : t = r := by
      by_contra hne
      linarith only [G_pos_off_minimum hr ht.le hne,
        mul_nonneg hA.le (sq_nonneg (z + N r t / (2 * c r * (t - 1) * (t + 1)))), hz]
    subst r
    rw [G_gibbs ht, cut_center_gibbs ht, zero_add] at hz
    have hsq : (z + 1) ^ 2 = 0 := (mul_eq_zero.mp hz).resolve_left hA.ne'
    have hzero : z + 1 = 0 := by
      by_contra hne
      exact pow_ne_zero _ hne hsq
    exact ⟨rfl, by linarith⟩
  · rintro ⟨rfl, rfl⟩
    rw [G_gibbs ht, cut_center_gibbs ht]
    ring

private theorem one_mode_equal_eq_zero {r v z : ℝ} (hr : 1 ≤ r) (hv : 0 < v) :
    oneModeDeficit r v v z = 0 ↔ r = 1 := by
  have hvalue : oneModeDeficit r v v z = h r * v ^ 3 := by
    rw [oneModeDeficit, entropyPair, cutA, cutB, show (v ^ 3 + v ^ 3) / 2 = v ^ 3 by ring]
    ring
  rw [hvalue, mul_eq_zero, or_iff_left (pow_ne_zero _ hv.ne')]
  constructor
  · intro hh
    by_contra hne
    have hG := G_pos_off_minimum hr le_rfl (Ne.symm hne)
    have hc := c_pos hr
    have hnonneg : 0 ≤ N r 1 ^ 2 / (8 * c r * (1 + 1) * (1 + 1 ^ 3)) := by positivity
    have he : G r 1 = h r / 2 - N r 1 ^ 2 / (8 * c r * (1 + 1) * (1 + 1 ^ 3)) := by
      simp [G, Q, cutA, show ((1 : ℝ) + 1) / 2 = 1 by norm_num]
    linarith only [he, hG, hh, hnonneg]
  · rintro rfl
    norm_num [h, gibbsLow, gibbsHigh]

private theorem sandwich_posDef {r : ℝ} (hr : 1 ≤ r) {P : Local} (hP : P.PosDef) :
    (root r * P * root r).PosDef := by
  have hroot := root_posDef hr
  simpa only [hroot.isHermitian.eq] using
    hP.conjTranspose_mul_mul_same hroot.mulVec_injective

private theorem root_diagonal (r : ℝ) :
    root r = diagonal ![(Real.sqrt (rootScale r) : ℂ),
      (Real.sqrt (rootScale r) : ℂ) * (rootRatio r : ℂ)] := by
  unfold root
  congr 1
  funext i
  fin_cases i <;> simp [rootValues]

private theorem root_second_sq {r : ℝ} (hr : 1 ≤ r) :
    ((Real.sqrt (rootScale r) : ℂ) * (rootRatio r : ℂ)) ^ 2 =
      (Real.sqrt (rootScale r) : ℂ) ^ 2 * (r : ℂ) := by
  have hratio : (rootRatio r : ℂ) ^ 2 = (r : ℂ) := by
    exact_mod_cast rootRatio_sq (zero_le_one.trans hr)
  rw [mul_pow, hratio]

private theorem sandwich_generator {r : ℝ} (hr : 1 ≤ r) (P : Local) :
    root r * rightGenerator r P * root r =
      modularJump r qubitJump (root r * P * root r) := by
  let a : ℂ := Real.sqrt (rootScale r)
  let b : ℂ := a * (rootRatio r : ℂ)
  have hroot : root r = diagonal ![a,b] := root_diagonal r
  have hsq : b * b = a * a * (r : ℂ) := by
    simpa only [pow_two] using root_second_sq hr
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le hr).ne'
  have hinv : (r : ℂ)⁻¹ * (b * b) = a * a := by
    rw [hsq, mul_comm (a * a) (r : ℂ), ← mul_assoc, inv_mul_cancel₀ hr0, one_mul]
  rw [hroot]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rightGenerator, modularJump, qubitJump, Matrix.mul_diagonal,
      Matrix.diagonal_mul, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct]
  · linear_combination (2 * (gibbsHigh r : ℂ) * P 1 1) * hinv
  · ring
  · ring
  · linear_combination -(2 * (gibbsLow r : ℂ) * P 0 0) * hsq

private theorem product_deficit {r : ℝ} (hr : 1 ≤ r) {P : Local} (hP : P.PosDef) :
    operatorDeficit r (lift P) = oneModeOperatorDeficit r (root r * P * root r) := by
  let B := root r * P * root r
  have htrace (L : Local) : ((gibbs r ⊗ₖ (B ^ 3)) * lift L).trace = (B ^ 3 * L).trace := by
    rw [lift, ← mul_kronecker_mul, Matrix.mul_one, trace_kronecker, gibbs_trace hr, one_mul]
  have hmass : (gibbs r ⊗ₖ (B ^ 3)).trace = (B ^ 3).trace := by
    rw [trace_kronecker, gibbs_trace hr, one_mul]
  dsimp only [operatorDeficit]
  rw [product_energy hr, sandwich_generator hr, sandwich_lift hr,
    log_difference hr (sandwich_posDef hr hP)]
  change (9 / 8 : ℝ) * (B ^ 2 * modularJump r qubitJump B).trace.re -
      alpha r * _ = _
  rw [cubed_base hr, show root r * P * root r = B from rfl, htrace, hmass]
  rfl

private theorem one_mode_operator_eq_scalar {r : ℝ} (hr : 1 ≤ r) {C : Local}
    (hC : C.PosDef) :
    let v := hC.isHermitian.eigenvalues 0
    let w := hC.isHermitian.eigenvalues 1
    let U : Local := hC.isHermitian.eigenvectorUnitary
    oneModeOperatorDeficit r C = oneModeDeficit r v w (2 * Complex.normSq (U 0 1) - 1) := by
  let v := hC.isHermitian.eigenvalues 0
  let w := hC.isHermitian.eigenvalues 1
  let U : Local := hC.isHermitian.eigenvectorUnitary
  let p := Complex.normSq (U 0 1)
  obtain ⟨_, _, hm⟩ := qubit_diagonal_moments hC.isHermitian
  change ∀ k : ℕ, (C ^ k) 0 0 = (moment v w p k : ℂ) ∧
    (C ^ k) 1 1 = (moment v w (1 - p) k : ℂ) at hm
  have hρ : cfc Real.log (gibbsDensity r) =
      diagonal (fun i => (Real.log (gibbsOccupation r i) : ℂ)) := by
    simpa only [gibbsDensity, Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using
      Matrix.cfc_diagonal_real (𝕜 := ℂ) (gibbsOccupation r) Real.log
  have hGibbs : (C ^ 3 * cfc Real.log (gibbsDensity r)).trace.re =
      moment v w p 3 * Real.log (gibbsLow r) + moment v w (1 - p) 3 * Real.log (gibbsHigh r) := by
    rw [hρ]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal, Fin.sum_univ_two,
      (hm 3).1, (hm 3).2, ← Complex.ofReal_mul, Complex.add_re, Complex.ofReal_re,
      gibbsOccupation, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hm0 : C 0 0 = (moment v w p 1 : ℂ) := by simpa only [pow_one] using (hm 1).1
  have hm1 : C 1 1 = (moment v w (1 - p) 1 : ℂ) := by simpa only [pow_one] using (hm 1).2
  change oneModeOperatorDeficit r C = oneModeDeficit r v w (2 * p - 1)
  unfold oneModeOperatorDeficit cubicEntropy cubicMass
  rw [one_mode_energy_diagonal hr, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re,
    trace_cube_log hC.isHermitian, trace_cube hC.isHermitian, hGibbs, (hm 3).1, (hm 3).2,
    (hm 2).1, (hm 2).2, hm0, hm1]
  simp only [Fin.sum_univ_two, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [sub_right_comm ((v ^ 3 * Real.log (v ^ 3)) + (w ^ 3 * Real.log (w ^ 3)))]
  simpa only [v, w, mul_assoc] using
    one_mode_scalar_identity hr (hC.eigenvalues_pos 0).le (hC.eigenvalues_pos 1).le p

private theorem one_mode_sorted_data {r : ℝ} (hr : 1 ≤ r) {C : Local} (hC : C.PosDef) :
    ∃ v w p : ℝ, 0 < v ∧ v ≤ w ∧
      oneModeOperatorDeficit r C = oneModeDeficit r v w (2 * p - 1) ∧
      ∀ k : ℕ, (C ^ k) 0 0 = (moment v w p k : ℂ) ∧
        (C ^ k) 1 1 = (moment v w (1 - p) k : ℂ) := by
  let v := hC.isHermitian.eigenvalues 0
  let w := hC.isHermitian.eigenvalues 1
  let U : Local := hC.isHermitian.eigenvectorUnitary
  let p := Complex.normSq (U 0 1)
  have hv : 0 < v := hC.eigenvalues_pos 0
  have hw : 0 < w := hC.eigenvalues_pos 1
  have hd : oneModeOperatorDeficit r C = oneModeDeficit r v w (2 * p - 1) :=
    one_mode_operator_eq_scalar hr hC
  obtain ⟨_, _, hm⟩ := qubit_diagonal_moments hC.isHermitian
  change ∀ k : ℕ, (C ^ k) 0 0 = (moment v w p k : ℂ) ∧
    (C ^ k) 1 1 = (moment v w (1 - p) k : ℂ) at hm
  rcases le_total v w with hvw | hwv
  · exact ⟨v, w, p, hv, hvw, hd, hm⟩
  · -- Swapping columns replaces the upper-level overlap by its complement.
    refine ⟨w, v, 1 - p, hw, hwv, hd.trans ?_, ?_⟩
    · simp only [oneModeDeficit, entropyPair, cutA, cutB, add_comm (w ^ 3) (v ^ 3)]
      ring
    · intro k
      have hswap (q : ℝ) : moment w v (1 - q) k = moment v w q k := by
        unfold moment
        ring
      refine ⟨by rw [hswap, (hm k).1], ?_⟩
      rw [hswap, (hm k).2]

private theorem one_mode_operator_eq_gibbs_levels {r : ℝ} (hr : 1 ≤ r) {C : Local}
    (hC : C.PosDef) (hz : oneModeOperatorDeficit r C = 0) :
    ∃ v : ℝ, 0 < v ∧ C = diagonal ![(v : ℂ), ((r * v : ℝ) : ℂ)] := by
  obtain ⟨v, w, p, hv, hvw, hd, hm⟩ := one_mode_sorted_data hr hC
  have hz' := hd.symm.trans hz
  have hlevels : w = r * v ∧ ∀ k : ℕ, moment v w p k = v ^ k ∧
      moment v w (1 - p) k = w ^ k := by
    rcases hvw.eq_or_lt with heq | hlt
    · subst w
      have hr' := (one_mode_equal_eq_zero hr hv).mp hz'
      subst r
      exact ⟨by simp, fun k => ⟨by unfold moment; ring, by unfold moment; ring⟩⟩
    · obtain ⟨hw, hp⟩ := (one_mode_distinct_eq_zero hr hv hlt).mp hz'
      have hp0 : p = 0 := by linarith
      exact ⟨hw, fun k => by simp [hp0, moment]⟩
  have hdiag0 : C 0 0 = (v : ℂ) := by
    simpa only [pow_one, (hlevels.2 1).1] using (hm 1).1
  have hdiag1 : C 1 1 = (w : ℂ) := by
    simpa only [pow_one, (hlevels.2 1).2] using (hm 1).2
  have hsq : (C ^ 2) 0 0 = (v : ℂ) ^ 2 := by
    simpa only [(hlevels.2 2).1, Complex.ofReal_pow] using (hm 2).1
  have hconj : star (C 0 1) = C 1 0 := congrFun (congrFun hC.isHermitian.eq 1) 0
  have hoff : C 0 1 = 0 := by
    rw [pow_two, Matrix.mul_apply, Fin.sum_univ_two, hdiag0, pow_two] at hsq
    have hprod : C 0 1 * C 1 0 = 0 := by
      exact add_left_cancel (hsq.trans (add_zero _).symm)
    rw [← hconj, Complex.star_def, Complex.mul_conj] at hprod
    exact Complex.normSq_eq_zero.mp (by exact_mod_cast hprod)
  have hoff' : C 1 0 = 0 := by rw [← hconj, hoff, star_zero]
  refine ⟨v, hv, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal_apply, ← hlevels.1, hdiag0, hdiag1, hoff, hoff']

private theorem sandwich_scalar {r v : ℝ} (hr : 1 ≤ r) :
    root r * (((v / rootScale r : ℝ) : ℂ) • (1 : Local)) * root r =
      diagonal ![(v : ℂ), ((r * v : ℝ) : ℂ)] := by
  have hs : (Real.sqrt (rootScale r) : ℂ) ^ 2 = (rootScale r : ℂ) := by
    exact_mod_cast sqrt_rootScale_sq hr
  have hv : v / rootScale r * rootScale r = v :=
    div_mul_cancel₀ _ (rootScale_pos (zero_le_one.trans hr)).ne'
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← pow_two,
    root_diagonal, Matrix.diagonal_pow, Matrix.smul_diagonal]
  congr 1
  funext i
  fin_cases i <;>
    simp only [Pi.smul_apply, Pi.pow_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      smul_eq_mul, root_second_sq hr, hs, ← mul_assoc, ← Complex.ofReal_mul, hv, mul_comm v r]

/-- The literal Wu cubic deficit is nonnegative on a lifted positive-definite qubit. -/
theorem operatorDeficit_lift_nonneg {r : ℝ} (hr : 1 ≤ r) {P : Local} (hP : P.PosDef) :
    0 ≤ operatorDeficit r (lift P) := by
  rw [product_deficit hr hP]
  exact one_mode_operator_nonneg hr (sandwich_posDef hr hP).posSemidef

/-- The literal Wu cubic deficit on a lifted positive-definite qubit is zero
exactly when the original observable is a positive scalar matrix. -/
theorem operatorDeficit_lift_eq_zero_iff {r : ℝ} (hr : 1 ≤ r) {P : Local} (hP : P.PosDef) :
    operatorDeficit r (lift P) = 0 ↔ ∃ a : ℝ, 0 < a ∧ P = (a : ℂ) • (1 : Local) := by
  constructor
  · intro hz
    rw [product_deficit hr hP] at hz
    obtain ⟨v, hv, hB⟩ := one_mode_operator_eq_gibbs_levels hr (sandwich_posDef hr hP) hz
    refine ⟨v / rootScale r, div_pos hv (rootScale_pos (zero_le_one.trans hr)), ?_⟩
    have hu := (root_posDef hr).isUnit
    exact hu.mul_right_injective (hu.mul_left_injective (hB.trans (sandwich_scalar hr).symm))
  · rintro ⟨a, _, rfl⟩
    rw [lift, Matrix.kronecker_smul, Matrix.one_kronecker_one, operatorDeficit_scalar hr]

#print axioms operatorDeficit_lift_nonneg
#print axioms operatorDeficit_lift_eq_zero_iff

end D5.S3.Quantum.Semigroups.WuCubicOneModeEquality
