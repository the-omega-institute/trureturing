/- GID: D5/S3/Quantum/Analysis/RefinedBMVPositiveCenterLeftStripKernel
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cancellation of the exact positive-center numerator on the separated left strip. -/

import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterLeftStripWeightedTail

noncomputable section

namespace RefinedBMV.PositiveCenter

/-- Exact decomposition of the numerator into the geometric profile and
the two small residuals. -/
theorem leftStrip_numerator_decomposition {p : ℕ} (hp : 11 ≤ p) {a v : ℝ}
    (ha : 0 < a) (hgap : 6 ≤ v-a) :
    let h := 3/(p : ℝ)
    compositionMoment p a v -
      Real.sqrt (compositionMoment p 0 v*compositionMoment p 0 (v-a)) =
    leftStripGeometricTerm h a v+leftStripRadicalTerm h a v+leftStripTailTerm p a v := by
  let h := 3/(p : ℝ)
  let s := v-a
  let c := (3+h)*(3+2*h)/2
  let F := upperTailGap h
  let x (t : ℝ) := Real.exp (-t/(p : ℝ))
  let D (r t : ℝ) := c*F r*F t*Real.exp (-(r+t))
  let b (t : ℝ) := Real.sqrt (1-upperTailLambda h t)
  let U := upperTailRepeatCorrection h
  let W := leftStripWeight h a v
  have hp₀ : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp₀
  have hh : 0 < h := by dsimp [h]; positivity
  have hhmax : h ≤ 3/11 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by exact_mod_cast hp)
  have hs : 0 < s := by linarith
  have hsv : s ≤ v := sub_le_self v ha.le
  have hv : 0 < v := hs.trans_le hsv
  have hc : 0 < c := by dsimp [c]; positivity
  have hFs := tail_gap_pos hh hs
  have hFv := tail_gap_pos hh hv
  have hD : 0 < D v s :=
    mul_pos (mul_pos (mul_pos hc hFv) hFs) (Real.exp_pos _)
  have hScale (r t : ℝ) :
      (1-(x r)^3)*(1-(x t)^3)*DimThree.defect p (x r) (x t) 1 =
        D r t*compositionMoment p (r-t) r := by
    have hx₁ (u : ℝ) : (x u)^3 = Real.exp (-(h*u)) := (tail_cube_pow hp₀ u).1
    have hx₂ (u : ℝ) : (x u)^p = Real.exp (-u) := (tail_cube_pow hp₀ u).2
    rw [defect_eq_compositionMoment hp₀ (Real.exp_pos _) (Real.exp_pos _) zero_lt_one,
      DimThree.gaps_length_eq_choose, show logCoordinate p (x r) (x t) = r-t from
        tail_logCoordinate hp₀ r t,
      show logCoordinate p (x r) 1 = r by
        simpa only [zero_sub, neg_zero, zero_div, Real.exp_zero, sub_zero, x] using
          tail_logCoordinate hp₀ r 0,
      hx₁ r, hx₁ t, tail_gap_factor hh, tail_gap_factor hh, mul_one, mul_pow,
      hx₂ r, hx₂ t]
    have he : Real.exp (-r)*Real.exp (-t) = Real.exp (-(r+t)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    dsimp only [D]
    linear_combination (F r*F t*Real.exp (-(r+t))*compositionMoment p (r-t) r)*
      (tail_choose_scale hp₀)
  have hCross : D v s*compositionMoment p a v = 1-leftStripCross p a v-D v s := by
    have h := upperTail_distinct_defect (d := s) hp₀ ha
    dsimp only at h
    rw [show s+a = v by dsimp [s]; ring] at h
    change (1-(x v)^3)*(1-(x s)^3)*DimThree.defect p (x v) (x s) 1 =
      1-upperTailCrossCorrection _ _ _-_ at h
    rw [hScale v s, show v-s = a by dsimp [s]; ring, ← leftStripCross_eq hp₀ ha] at h
    rw [show -(a+2*s) = -(v+s) by dsimp [s]; ring] at h
    exact h
  have hDiag (t : ℝ) : D t t*compositionMoment p 0 t = 1-upperTailLambda h t := by
    have h := upperTail_repeated_defect hp₀ t
    change (1-(x t)^3)^2*DimThree.defect p (x t) (x t) 1 = _ at h
    rw [pow_two, hScale t t, sub_self] at h
    exact h
  have hDiagNonneg (t : ℝ) (ht : 6 ≤ t) : 0 ≤ 1-upperTailLambda h t :=
    (Real.sqrt_pos.mp ((by norm_num : (0 : ℝ) < 999/1000).trans_le
      (separated_radical_lower hh hhmax ht).2)).le
  have hDsq : D v s^2 = D v v*D s s := by
    simp only [D, neg_add, Real.exp_add]
    ring
  have hRoot : D v s*Real.sqrt (compositionMoment p 0 v*compositionMoment p 0 s) =
      b v*b s := calc
    _ = Real.sqrt ((D v s)^2*(compositionMoment p 0 v*compositionMoment p 0 s)) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hD.le]
    _ = Real.sqrt ((D v v*compositionMoment p 0 v)*(D s s*compositionMoment p 0 s)) := by
      rw [hDsq]
      congr 1
      ring
    _ = _ := by rw [hDiag, hDiag, Real.sqrt_mul (hDiagNonneg v (hgap.trans hsv))]
  let L := logReciprocalGap h
  have hDexp {r t : ℝ} (hr : 0 < F r) (ht : 0 < F t) :
      D r t = c*Real.exp (-(L r+L t)) := by
    have he (z : ℝ) (hz : 0 < F z) : Real.exp (-(L z)) = Real.exp (-z)*F z := by
      change Real.exp (-(z-Real.log (F z))) = _
      rw [show -(z-Real.log (F z)) = -z+Real.log (F z) by ring, Real.exp_add, Real.exp_log hz]
    simp only [D, neg_add, Real.exp_add, he r hr, he t ht]
    ring
  have hW : W*D v s = 1 := by
    rw [hDexp hFv hFs]
    change Real.exp (L v+L s)/c*(c*Real.exp (-(L v+L s))) = 1
    field_simp [hc.ne']
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hWdiag : W*((D v v+D s s)/2) = Real.cosh (L v-L s) := by
    rw [hDexp hFv hFv, hDexp hFs hFs, Real.cosh_eq]
    change Real.exp (L v+L s)/c*((c*Real.exp (-(L v+L v))+c*Real.exp (-(L s+L s)))/2) = _
    have he₁ : Real.exp (L v+L s)*Real.exp (-(L v+L v)) = Real.exp (-(L v-L s)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have he₂ : Real.exp (L v+L s)*Real.exp (-(L s+L s)) = Real.exp (L v-L s) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = (Real.exp (L v+L s)*Real.exp (-(L v+L v))+
          Real.exp (L v+L s)*Real.exp (-(L s+L s)))/2 := by
        field_simp [hc.ne'] <;> ring
      _ = _ := by rw [he₁, he₂]; ring
  have hSq (t : ℝ) (ht : 6 ≤ t) : (b t)^2 = 1-U t-D t t := by
    unfold b
    rw [Real.sq_sqrt (hDiagNonneg t ht)]
    unfold U upperTailRepeatCorrection upperTailLambda D
    rw [show -(t+t) = -(2*t) by ring]
    dsimp only [c, F]
    ring
  have hsum : 1-leftStripCross p a v-b v*b s =
      (D v v+D s s)/2+((U v+U s)/2-leftStripCross p a v)+(b v-b s)^2/2 := by
    nlinarith only [hSq v (hgap.trans hsv), hSq s hgap]
  have hN :
      compositionMoment p a v-Real.sqrt (compositionMoment p 0 v*compositionMoment p 0 s) =
        W*(1-leftStripCross p a v-b v*b s)-1 := by
    have hid := congrArg (fun z : ℝ ↦ W*z)
      (show D v s*(compositionMoment p a v-
          Real.sqrt (compositionMoment p 0 v*compositionMoment p 0 s)) =
        1-leftStripCross p a v-D v s-b v*b s by rw [mul_sub, hRoot, hCross])
    rw [← mul_assoc, hW, one_mul] at hid
    nlinarith only [hid, hW]
  change compositionMoment p a v-Real.sqrt (compositionMoment p 0 v*compositionMoment p 0 s) =
    (Real.cosh (L v-L s)-1)+W*(b v-b s)^2/2+
      W*((U v+U s)/2-leftStripCross p a v)
  rw [hN, hsum]
  nlinarith only [hWdiag]

#print axioms leftStrip_numerator_decomposition

end RefinedBMV.PositiveCenter
