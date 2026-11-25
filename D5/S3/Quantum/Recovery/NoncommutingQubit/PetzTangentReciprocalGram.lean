/- GID: D5/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentReciprocalGram
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentReciprocalGram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Paired reciprocal Gram lower bound for the qubit Petz tangent. -/

import D5.S3.Quantum.Divergence.UmegakiRareFlagBKM

/-! The two reciprocal Gram kernels after the change of variables
`t = z⁻² - 1`. Their normalization retains both opposite off-diagonal
responses, including when the two nodes coincide. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open D5.S3.Divergence.LogDerivTrace
open D5.S3.Quantum.Divergence.UmegakiRareFlagBKM
open D5.S3.Quantum.Subentropy.UniformIntegrals

namespace D5.S3.Quantum.Recovery.PetzTangentReciprocalGram

private def pair (a b : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), 1 / ((a+t)*(b+t))

private def triple (a b c : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), 1 / ((a+t)*(b+t)*(c+t))

private lemma pair_self (a : ℝ) (ha : 0 < a) : pair a a = 1/a := by
  rw [pair, pair_kernel_eval a a ha ha, ite_eq_left rfl]

private lemma pair_comm (a b : ℝ) : pair a b = pair b a := by
  simp only [pair, mul_comm]

private lemma triple_rotate (a b c : ℝ) : triple a b c = triple b c a := by
  unfold triple
  congr 1
  ext t
  ring

private lemma triple_integrable (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => 1 / ((a+t)*(b+t)*(c+t))) (Ioi 0) := by
  apply Integrable.mono' ((pairKernel_integrable b c hb hc).const_mul (1/a))
  · apply (continuousOn_const.div ?_ ?_).aestronglyMeasurable measurableSet_Ioi
    · exact ((continuousOn_const.add continuousOn_id).mul
        (continuousOn_const.add continuousOn_id)).mul (continuousOn_const.add continuousOn_id)
    · intro t ht
      exact mul_ne_zero (mul_ne_zero (add_pos ha ht).ne' (add_pos hb ht).ne') (add_pos hc ht).ne'
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have hat := add_pos ha ht
    have hbt := add_pos hb ht
    have hct := add_pos hc ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc
      1 / ((a+t)*(b+t)*(c+t)) = (1/(a+t)) * (1/((b+t)*(c+t))) := by simp only [div_eq_mul_inv, mul_inv_rev]; ring
      _ ≤ (1/a) * (1/((b+t)*(c+t))) :=
        mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le ha (by linarith)) (by positivity)

private lemma pair_scale (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    pair (a^2) (b^2) = 2 * pair a b / (a+b) := by
  by_cases hab : a = b
  · subst b
    rw [pair_self _ (sq_pos_of_pos ha), pair_self _ ha]
    field_simp <;> ring
  · have hab2 : a^2 ≠ b^2 := by
      intro h
      apply hab
      nlinarith [sq_nonneg (a-b)]
    rw [pair, pair_kernel_eval _ _ (sq_pos_of_pos ha) (sq_pos_of_pos hb), ite_eq_right hab2,
      pair, pair_kernel_eval _ _ ha hb, ite_eq_right hab, Real.log_pow, Real.log_pow]
    push_cast
    field_simp [hab, hab2, (add_pos ha hb).ne', sub_ne_zero.mpr hab, sub_ne_zero.mpr hab2]
    <;> ring

private lemma pair_diff (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    pair a b - pair a c = (c-b) * triple a b c := by
  unfold pair triple
  rw [← integral_sub (pairKernel_integrable a b ha hb) (pairKernel_integrable a c ha hc),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change 1 / ((a+t)*(b+t)) - 1 / ((a+t)*(c+t)) = (c-b) * (1 / ((a+t)*(b+t)*(c+t)))
  field_simp [(add_pos ha ht).ne', (add_pos hb ht).ne', (add_pos hc ht).ne']
  <;> ring

private lemma triple_self (a : ℝ) (ha : 0 < a) : triple a a a = 1/(2*a^2) := by
  unfold triple
  have hv := (inverse_power a ha 1).2
  convert hv using 1
  · apply integral_congr_ae
    filter_upwards [] with t
    ring
  · norm_num

/-- The three-node reciprocal identity underlying the odd Gram comparison.
All positive nodes are allowed, including every pair and triple coincidence. -/
private lemma triple_scale (g x y : ℝ) (hg : 0 < g) (hx : 0 < x) (hy : 0 < y) :
    (g+x)*(g+y)/2 * triple (g^2) (x^2) (y^2) =
      triple g x y + pair x y / (x+y) := by
  by_cases hxy : x = y
  · subst y
    by_cases hgx : g = x
    · subst g
      rw [triple_self _ (sq_pos_of_pos hx), triple_self _ hx, pair_self _ hx]
      field_simp
      <;> ring
    · have d := pair_diff x x g hx hx hg
      have d2 := pair_diff (x^2) (x^2) (g^2) (sq_pos_of_pos hx) (sq_pos_of_pos hx) (sq_pos_of_pos hg)
      rw [← triple_rotate g x x] at d
      rw [← triple_rotate (g^2) (x^2) (x^2), pair_scale x x hx hx, pair_scale x g hx hg] at d2
      have hgx' : g-x ≠ 0 := sub_ne_zero.mpr hgx
      have hgx2 : g^2-x^2 ≠ 0 := by
        rw [show g^2-x^2 = (g-x)*(g+x) by ring]
        exact mul_ne_zero hgx' (add_pos hg hx).ne'
      -- Solve the two reciprocal differences for the repeated-node triples.
      have e1 : triple g x x = (pair x x - pair x g)/(g-x) := by
        apply (eq_div_iff hgx').2
        linarith only [d]
      have e2 : triple (g^2) (x^2) (x^2) =
          (2*pair x x/(x+x)-2*pair x g/(x+g))/(g^2-x^2) := by
        apply (eq_div_iff hgx2).2
        linarith only [d2]
      rw [e1, e2]
      field_simp [hgx', hgx2, hx.ne', (add_pos hx hg).ne', (add_pos hg hx).ne']
      <;> ring
  · have hyx : y-x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
    have hyx2 : y^2-x^2 ≠ 0 := by
      rw [show y^2-x^2 = (y-x)*(y+x) by ring]
      exact mul_ne_zero hyx (add_pos hy hx).ne'
    have d := pair_diff g x y hg hx hy
    have d2 := pair_diff (g^2) (x^2) (y^2) (sq_pos_of_pos hg) (sq_pos_of_pos hx) (sq_pos_of_pos hy)
    rw [pair_scale g x hg hx, pair_scale g y hg hy] at d2
    have d3 := pair_diff y x g hy hx hg
    rw [pair_comm y x, pair_comm y g, triple_rotate y x g] at d3
    -- The cyclic identity may be used in either orientation of the triple.
    have hsym : triple x g y = triple g x y := by
      unfold triple
      congr 1
      ext t
      ring
    rw [hsym] at d3
    have e1 : triple g x y = (pair g x - pair g y)/(y-x) := by
      apply (eq_div_iff hyx).2
      linarith only [d]
    have e2 : triple (g^2) (x^2) (y^2) =
        (2*pair g x/(g+x)-2*pair g y/(g+y))/(y^2-x^2) := by
      apply (eq_div_iff hyx2).2
      linarith only [d2]
    rw [e2]
    have he : (g+x)*(g+y)/2 *
        ((2*pair g x/(g+x)-2*pair g y/(g+y))/(y^2-x^2)) =
        ((g+y)*triple g x y + pair g y)/(x+y) := by
      rw [e1]
      field_simp [hyx, hyx2, (add_pos hg hx).ne', (add_pos hg hy).ne', (add_pos hx hy).ne']
      <;> ring
    rw [he]
    apply (div_eq_iff (add_pos hx hy).ne').2
    rw [show (triple g x y + pair x y / (x+y))*(x+y) = triple g x y*(x+y)+pair x y by
      rw [add_mul, div_mul_cancel₀ _ (add_pos hx hy).ne']]
    linarith only [d3]

/-- Normalization by the two odd arcsine functional values
`1 / (x * (x + g))` and `1 / (y * (y + g))`. -/
private def oddGram (g x y : ℝ) : ℝ :=
  x * y * (g+x)*(g+y)/2 * triple (g^2) (x^2) (y^2)

/-- The normalized reciprocal Gram term common to both parity sectors. -/
private def evenLowerGram (x y : ℝ) : ℝ := x*y/2 * pair (x^2) (y^2)

/-- The positive Gram correction with unsquared reciprocal nodes. -/
private def correctionGram (g x y : ℝ) : ℝ := x*y * triple g x y

/-- The paired odd lower Gram splits into the common even lower Gram
and a positive reciprocal Gram with unsquared nodes. -/
private theorem oddGram_eq (g x y : ℝ) (hg : 0 < g) (hx : 0 < x) (hy : 0 < y) :
    oddGram g x y = evenLowerGram x y + correctionGram g x y := by
  unfold oddGram evenLowerGram correctionGram
  rw [show x*y*(g+x)*(g+y)/2 = x*y*((g+x)*(g+y)/2) by ring,
    mul_assoc, triple_scale g x y hg hx hy, pair_scale x y hx hy]
  ring

private lemma even_diag (x : ℝ) (hx : 0 < x) : evenLowerGram x x = 1/2 := by
  rw [evenLowerGram, pair_self _ (sq_pos_of_pos hx)]
  field_simp

private lemma even_cross_le (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    evenLowerGram x y ≤ 1/2 := by
  have hi := (pairKernel_integrable (x^2) (y^2) (sq_pos_of_pos hx) (sq_pos_of_pos hy)).const_mul (2*x*y)
  have hj := ((pairKernel_integrable (x^2) (x^2) (sq_pos_of_pos hx) (sq_pos_of_pos hx)).const_mul (x*x)).add
    ((pairKernel_integrable (y^2) (y^2) (sq_pos_of_pos hy) (sq_pos_of_pos hy)).const_mul (y*y))
  have h := integral_mono_ae hi hj (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change (2*x*y) * (1/((x^2+t)*(y^2+t))) ≤
      (x*x)*(1/((x^2+t)*(x^2+t))) + (y*y)*(1/((y^2+t)*(y^2+t)))
    have he : (x/(x^2+t))^2 + (y/(y^2+t))^2 - 2*(x/(x^2+t))*(y/(y^2+t)) ≥ 0 := by
      nlinarith [sq_nonneg (x/(x^2+t)-y/(y^2+t))]
    calc
      _ = 2*(x/(x^2+t))*(y/(y^2+t)) := by simp only [div_eq_mul_inv, mul_inv_rev]; ring
      _ ≤ (x/(x^2+t))^2 + (y/(y^2+t))^2 := by linarith
      _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring)
  simp only [Pi.add_apply] at h
  rw [integral_add
    ((pairKernel_integrable (x^2) (x^2) (sq_pos_of_pos hx) (sq_pos_of_pos hx)).const_mul (x*x))
    ((pairKernel_integrable (y^2) (y^2) (sq_pos_of_pos hy) (sq_pos_of_pos hy)).const_mul (y*y)),
    integral_const_mul, integral_const_mul, integral_const_mul] at h
  change 2*x*y*pair (x^2) (y^2) ≤ x*x*pair (x^2) (x^2) + y*y*pair (y^2) (y^2) at h
  rw [pair_self _ (sq_pos_of_pos hx), pair_self _ (sq_pos_of_pos hy)] at h
  have hx' : x*x*(1/x^2) = 1 := by field_simp
  have hy' : y*y*(1/y^2) = 1 := by field_simp
  rw [hx', hy'] at h
  unfold evenLowerGram
  linarith only [h]

private lemma correction_nonneg (g x y a b : ℝ) (hg : 0 < g) (hx : 0 < x) (hy : 0 < y) :
    0 ≤ a^2*correctionGram g x x + 2*a*b*correctionGram g x y + b^2*correctionGram g y y := by
  unfold correctionGram triple
  have hi := (triple_integrable g x x hg hx hx).const_mul (a^2*(x*x))
  have hj := (triple_integrable g x y hg hx hy).const_mul (2*a*b*(x*y))
  have hk := (triple_integrable g y y hg hy hy).const_mul (b^2*(y*y))
  have h : 0 ≤ ∫ t in Ioi (0 : ℝ),
      a^2*(x*x)*(1/((g+t)*(x+t)*(x+t))) + 2*a*b*(x*y)*(1/((g+t)*(x+t)*(y+t))) +
        b^2*(y*y)*(1/((g+t)*(y+t)*(y+t))) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hgt := add_pos hg ht
    have hxt := add_pos hx ht
    have hyt := add_pos hy ht
    rw [show a^2*(x*x)*(1/((g+t)*(x+t)*(x+t))) + 2*a*b*(x*y)*(1/((g+t)*(x+t)*(y+t))) +
      b^2*(y*y)*(1/((g+t)*(y+t)*(y+t))) = (a*x/(x+t)+b*y/(y+t))^2/(g+t) by
        simp only [div_eq_mul_inv, mul_inv_rev]; ring]
    positivity
  have he := integral_add (hi.add hj) hk
  simp only [Pi.add_apply] at he
  rw [he, integral_add hi hj, integral_const_mul, integral_const_mul, integral_const_mul] at h
  linarith only [h]

private lemma correction_diag (g x : ℝ) (hg : 0 < g) (hx : 0 < x) (hg1 : g ≤ 1) (hx1 : x ≤ 1) :
    x^2/2 ≤ correctionGram g x x := by
  have hi := (triple_integrable 1 1 1 (by norm_num) (by norm_num) (by norm_num))
  have hj := triple_integrable g x x hg hx hx
  have h : triple 1 1 1 ≤ triple g x x := by
    unfold triple
    apply integral_mono_ae hi hj
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    apply one_div_le_one_div_of_le (by positivity : 0 < (g+t)*(x+t)*(x+t))
    exact mul_le_mul (mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity))
      (by linarith) (by positivity) (by positivity)
  rw [triple_self 1 (by norm_num)] at h
  norm_num at h
  unfold correctionGram
  nlinarith only [mul_le_mul_of_nonneg_left h (sq_nonneg x)]

private lemma odd_entry_nonneg (g x y : ℝ) (hg : 0 < g) (hx : 0 < x) (hy : 0 < y) :
    0 ≤ oddGram g x y := by
  have h : 0 ≤ triple (g^2) (x^2) (y^2) := by
    unfold triple
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    positivity
  unfold oddGram
  positivity

/-- The unweighted odd reciprocal Gram already controls the paired
arcsine functional with the reviewed marginal-dependent coefficient.
The statement includes `δ = 1` and `g = δ` without a rank assumption. -/
private theorem paired_odd_bound (g δ a b : ℝ) (hg : 0 < g) (hg1 : g ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (a+b)^2 ≤ (1+2/(1+δ^2)) *
      (a^2*oddGram g 1 1 + 2*a*b*oddGram g 1 δ + b^2*oddGram g δ δ) := by
  let Q := a^2*oddGram g 1 1 + 2*a*b*oddGram g 1 δ + b^2*oddGram g δ δ
  let C := 1+2/(1+δ^2)
  have h1 : (0:ℝ) < 1 := by norm_num
  have hc : 2 ≤ C := by
    dsimp [C]
    have he : δ^2 ≤ 1 := by nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hδ1)]
    have hf : 1 ≤ 2/(1+δ^2) := (le_div_iff₀ (by positivity)).2 (by linarith)
    linarith
  have hq1 : 1 ≤ oddGram g 1 1 := by
    rw [oddGram_eq _ _ _ hg h1 h1, even_diag _ h1]
    have h := correction_diag g 1 hg h1 hg1 le_rfl
    linarith
  have hqδ : (1+δ^2)/2 ≤ oddGram g δ δ := by
    rw [oddGram_eq _ _ _ hg hδ hδ, even_diag _ hδ]
    linarith only [correction_diag g δ hg hδ hg1 hδ1]
  change (a+b)^2 ≤ C*Q
  rcases le_or_gt (a*b) 0 with hab | hab
  · have hcross := even_cross_le 1 δ h1 hδ
    have hp := correction_nonneg g 1 δ a b hg h1 hδ
    have hq : (a+b)^2/2 ≤ Q := by
      dsimp [Q]
      rw [oddGram_eq _ _ _ hg h1 h1, oddGram_eq _ _ _ hg h1 hδ,
        oddGram_eq _ _ _ hg hδ hδ, even_diag _ h1, even_diag _ hδ]
      nlinarith only [hp, mul_nonneg (sub_nonneg.mpr hcross) (neg_nonneg.mpr hab)]
    have hQ : 0 ≤ Q := le_trans (by positivity) hq
    nlinarith only [hq, mul_le_mul_of_nonneg_right hc hQ]
  · have hcross := odd_entry_nonneg g 1 δ hg h1 hδ
    have hq : a^2 + ((1+δ^2)/2)*b^2 ≤ Q := by
      dsimp [Q]
      nlinarith only [mul_le_mul_of_nonneg_left hq1 (sq_nonneg a),
        mul_le_mul_of_nonneg_left hqδ (sq_nonneg b), mul_nonneg hab.le hcross]
    let d := (1+δ^2)/2
    have hd : 0 < d := by dsimp [d]; positivity
    have hC : C = 1+1/d := by dsimp [C,d]; field_simp
    have hCS : (a+b)^2 ≤ C*(a^2+d*b^2) := by
      rw [hC]
      apply (le_of_sub_nonneg)
      have he : (1+1/d)*(a^2+d*b^2)-(a+b)^2 = (a-d*b)^2/d := by
        field_simp [hd.ne']
        <;> ring
      rw [he]
      positivity
    exact hCS.trans (mul_le_mul_of_nonneg_left hq (by linarith : 0 ≤ C))

private lemma weighted_triple_integrable (g x y : ℝ) (hg : 0 < g) (hg1 : g ≤ 1)
    (hx : 0 < x) (hy : 0 < y) :
    IntegrableOn (fun t : ℝ => Real.sqrt (1+t) * (1/((g^2+t)*(x^2+t)*(y^2+t))))
      (Ioi 0) := by
  apply Integrable.mono' ((pairKernel_integrable (x^2) (y^2)
    (sq_pos_of_pos hx) (sq_pos_of_pos hy)).const_mul (1/g^2))
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    refine (by fun_prop : ContinuousOn (fun t : ℝ => Real.sqrt (1+t)) (Ioi 0)).mul ?_
    apply continuousOn_const.div
    · fun_prop
    · intro t ht
      have ht0 : 0 < t := ht
      positivity
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have hgt : 0 < g^2+t := by positivity
    have hxt : 0 < x^2+t := by positivity
    have hyt : 0 < y^2+t := by positivity
    have hs : Real.sqrt (1+t) ≤ 1+t := by
      have hsq := Real.sq_sqrt (show 0 ≤ 1+t by positivity)
      have h1 : 1 ≤ Real.sqrt (1+t) := by
        simpa using Real.sqrt_le_sqrt (show 1 ≤ 1+t by linarith)
      nlinarith only [hsq, mul_nonneg (sub_nonneg.mpr h1) (Real.sqrt_nonneg (1+t))]
    have hg2 : g^2 ≤ 1 := by nlinarith [mul_nonneg hg.le (sub_nonneg.mpr hg1)]
    have hs' : Real.sqrt (1+t)/(g^2+t) ≤ 1/g^2 := by
      apply (div_le_div_iff₀ hgt (sq_pos_of_pos hg)).2
      nlinarith only [mul_le_mul_of_nonneg_right hs (sq_nonneg g),
        mul_le_mul_of_nonneg_right hg2 ht0.le]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc
      _ = (Real.sqrt (1+t)/(g^2+t)) * (1/((x^2+t)*(y^2+t))) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hs' (by positivity)

/-- The normalized square of the odd rational profile, after removing the
Jacobian factor `sqrt (1+t)`. -/
private def oddEnergy (g δ a b t : ℝ) : ℝ :=
  (a*(g+1)/(1+t) + b*δ*(g+δ)/(δ^2+t))^2 / (2*(g^2+t))

private lemma odd_energy_expansion (g δ a b t : ℝ) :
    oddEnergy g δ a b t =
      (a^2*(g+1)^2/2) * (1/((g^2+t)*(1+t)*(1+t))) +
      (a*b*δ*(g+1)*(g+δ)) * (1/((g^2+t)*(1+t)*(δ^2+t))) +
      (b^2*δ^2*(g+δ)^2/2) * (1/((g^2+t)*(δ^2+t)*(δ^2+t))) := by
  unfold oddEnergy
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private lemma odd_energy_integrable (g δ a b : ℝ) (hg : 0 < g) (hδ : 0 < δ) :
    IntegrableOn (oddEnergy g δ a b) (Ioi 0) := by
  have h1 : (0:ℝ) < 1 := by norm_num
  have hi := (triple_integrable (g^2) 1 1 (sq_pos_of_pos hg) h1 h1).const_mul
    (a^2*(g+1)^2/2)
  have hj := (triple_integrable (g^2) 1 (δ^2) (sq_pos_of_pos hg) h1 (sq_pos_of_pos hδ)).const_mul
    (a*b*δ*(g+1)*(g+δ))
  have hk := (triple_integrable (g^2) (δ^2) (δ^2) (sq_pos_of_pos hg)
    (sq_pos_of_pos hδ) (sq_pos_of_pos hδ)).const_mul (b^2*δ^2*(g+δ)^2/2)
  refine IntegrableOn.congr_fun ((hi.add hj).add hk) ?_ measurableSet_Ioi
  intro t _
  exact (odd_energy_expansion g δ a b t).symm

private lemma weighted_odd_energy_integrable (g δ a b : ℝ) (hg : 0 < g) (hg1 : g ≤ 1)
    (hδ : 0 < δ) :
    IntegrableOn (fun t => Real.sqrt (1+t)*oddEnergy g δ a b t) (Ioi 0) := by
  have h1 : (0:ℝ) < 1 := by norm_num
  have hi := (weighted_triple_integrable g 1 1 hg hg1 h1 h1).const_mul (a^2*(g+1)^2/2)
  have hj := (weighted_triple_integrable g 1 δ hg hg1 h1 hδ).const_mul (a*b*δ*(g+1)*(g+δ))
  have hk := (weighted_triple_integrable g δ δ hg hg1 hδ hδ).const_mul (b^2*δ^2*(g+δ)^2/2)
  refine IntegrableOn.congr_fun ((hi.add hj).add hk) ?_ measurableSet_Ioi
  intro t _
  simp only [Pi.add_apply, one_pow, odd_energy_expansion]
  ring

private lemma odd_energy_integral (g δ a b : ℝ) (hg : 0 < g) (hδ : 0 < δ) :
    (∫ t in Ioi (0:ℝ), oddEnergy g δ a b t) =
      a^2*oddGram g 1 1 + 2*a*b*oddGram g 1 δ + b^2*oddGram g δ δ := by
  have h1 : (0:ℝ) < 1 := by norm_num
  have hi := (triple_integrable (g^2) 1 1 (sq_pos_of_pos hg) h1 h1).const_mul
    (a^2*(g+1)^2/2)
  have hj := (triple_integrable (g^2) 1 (δ^2) (sq_pos_of_pos hg) h1 (sq_pos_of_pos hδ)).const_mul
    (a*b*δ*(g+1)*(g+δ))
  have hk := (triple_integrable (g^2) (δ^2) (δ^2) (sq_pos_of_pos hg)
    (sq_pos_of_pos hδ) (sq_pos_of_pos hδ)).const_mul (b^2*δ^2*(g+δ)^2/2)
  simp_rw [odd_energy_expansion]
  have he := integral_add (hi.add hj) hk
  simp only [Pi.add_apply] at he
  rw [he, integral_add hi hj, integral_const_mul, integral_const_mul, integral_const_mul]
  unfold oddGram triple
  norm_num
  ring

/-- The actual square-root-weighted reciprocal integral in the odd parity
sector. Both signed coefficients occur in the same square before integration. -/
private theorem weighted_odd_bound (g δ a b : ℝ) (hg : 0 < g) (hg1 : g ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (a+b)^2 ≤ (1+2/(1+δ^2)) *
      (∫ t in Ioi (0:ℝ), Real.sqrt (1+t)*oddEnergy g δ a b t) := by
  have hmono : (∫ t in Ioi (0:ℝ), oddEnergy g δ a b t) ≤
      ∫ t in Ioi (0:ℝ), Real.sqrt (1+t)*oddEnergy g δ a b t := by
    apply integral_mono_ae (odd_energy_integrable g δ a b hg hδ)
      (weighted_odd_energy_integrable g δ a b hg hg1 hδ)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have hs : 1 ≤ Real.sqrt (1+t) := by
      simpa using Real.sqrt_le_sqrt (show 1 ≤ 1+t by linarith)
    have he : 0 ≤ oddEnergy g δ a b t := by unfold oddEnergy; positivity
    simpa using mul_le_mul_of_nonneg_right hs he
  rw [odd_energy_integral g δ a b hg hδ] at hmono
  exact (paired_odd_bound g δ a b hg hg1 hδ hδ1).trans
    (mul_le_mul_of_nonneg_left hmono (by positivity))

private lemma root_tail (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => 1/(Real.sqrt (a+t)*(a+t))) (Ioi 0) ∧
      (∫ t in Ioi (0:ℝ), 1/(Real.sqrt (a+t)*(a+t))) = 2/Real.sqrt a := by
  have he (t : ℝ) (ht : 0 < t) :
      (t+a)^(-(3/2):ℝ) = 1/(Real.sqrt (a+t)*(a+t)) := by
    rw [show -(3/2:ℝ) = -(1/2+1) by norm_num, Real.rpow_neg (by positivity),
      Real.rpow_add (by positivity), Real.rpow_one, ← Real.sqrt_eq_rpow, add_comm t a, one_div]
  have hi := integrableOn_add_rpow_Ioi_of_lt (a := -(3/2:ℝ)) (c := 0) (m := a)
    (by norm_num) (by linarith)
  refine ⟨hi.congr_fun (fun t ht => he t ht) measurableSet_Ioi, ?_⟩
  have hshift := (measurePreserving_add_right volume a).setIntegral_preimage_emb
    (MeasurableEquiv.addRight a).measurableEmbedding
    (fun t : ℝ => t ^ (-(3/2):ℝ)) (Ioi a)
  have hpre : (fun t : ℝ => t+a) ⁻¹' Ioi a = Ioi 0 := by ext t; simp
  rw [hpre, integral_Ioi_rpow_of_lt (by norm_num : -(3/2:ℝ) < -1) ha] at hshift
  calc
    _ = ∫ t in Ioi (0:ℝ), (t+a)^(-(3/2):ℝ) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (he t ht).symm
    _ = _ := by
      rw [hshift, show -(3/2:ℝ)+1 = -(1/2) by norm_num, Real.rpow_neg ha.le,
        ← Real.sqrt_eq_rpow]
      ring

private lemma sqrt_div_sq (u : ℝ) (hu : 0 < u) :
    Real.sqrt u / (u*u) = 1/(Real.sqrt u*u) := by
  have hs := Real.sqrt_pos.2 hu
  field_simp [hu.ne', hs.ne']
  nlinarith only [Real.sq_sqrt hu.le]

private lemma weighted_pair_integrable (x y : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (hy : 0 < y) (hy1 : y ≤ 1) :
    IntegrableOn (fun t : ℝ => Real.sqrt (1+t) * (1/((x^2+t)*(y^2+t)))) (Ioi 0) := by
  apply Integrable.mono' ((root_tail 1 (by norm_num)).1.const_mul (1/(x^2*y^2)))
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    refine (by fun_prop : ContinuousOn (fun t : ℝ => Real.sqrt (1+t)) (Ioi 0)).mul ?_
    apply continuousOn_const.div
    · fun_prop
    · intro t ht
      have ht0 : 0 < t := ht
      positivity
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have hx2 : x^2 ≤ 1 := by nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hx1)]
    have hy2 : y^2 ≤ 1 := by nlinarith [mul_nonneg hy.le (sub_nonneg.mpr hy1)]
    have hx' : x^2*(1+t) ≤ x^2+t := by nlinarith only [mul_le_mul_of_nonneg_right hx2 ht0.le]
    have hy' : y^2*(1+t) ≤ y^2+t := by nlinarith only [mul_le_mul_of_nonneg_right hy2 ht0.le]
    have hden : x^2*(1+t)*(y^2*(1+t)) ≤ (x^2+t)*(y^2+t) :=
      mul_le_mul hx' hy' (by positivity) (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc
      _ ≤ Real.sqrt (1+t) * (1/(x^2*(1+t)*(y^2*(1+t)))) :=
        mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by positivity) hden) (by positivity)
      _ = (1/(x^2*y^2)) * (Real.sqrt (1+t)/((1+t)*(1+t))) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ = _ := by rw [sqrt_div_sq _ (by positivity)]

/-- The normalized even Gram with its original change-of-variables weight. -/
private def evenGram (x y : ℝ) : ℝ :=
  x*y/2 * ∫ t in Ioi (0:ℝ), Real.sqrt (1+t) * (1/((x^2+t)*(y^2+t)))

private lemma even_gram_nonneg (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    0 ≤ evenGram x y := by
  have h : 0 ≤ ∫ t in Ioi (0:ℝ), Real.sqrt (1+t) * (1/((x^2+t)*(y^2+t))) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    positivity
  unfold evenGram
  positivity

private lemma sqrt_chord (x t : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) (ht : 0 < t) :
    1-x^2+x*Real.sqrt (x^2+t) ≤ Real.sqrt (1+t) := by
  have hx2 : x^2 ≤ 1 := by nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hx1)]
  have hL : 0 ≤ 1-x^2+x*Real.sqrt (x^2+t) := by positivity
  have he : (Real.sqrt (1+t))^2-(1-x^2+x*Real.sqrt (x^2+t))^2 =
      (1-x^2)*(Real.sqrt (x^2+t)-x)^2 := by
    rw [Real.sq_sqrt (by positivity : 0 ≤ 1+t)]
    have h := Real.sq_sqrt (by positivity : 0 ≤ x^2+t)
    nlinarith only [h, congrArg (fun z : ℝ => x^2*z) h]
  have hsq : (1-x^2+x*Real.sqrt (x^2+t))^2 ≤ (Real.sqrt (1+t))^2 := by
    nlinarith only [he, mul_nonneg (sub_nonneg.mpr hx2) (sq_nonneg (Real.sqrt (x^2+t)-x))]
  exact (sq_le_sq₀ hL (Real.sqrt_nonneg _)).1 hsq

private lemma even_gram_diag (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    (1+x^2)/2 ≤ evenGram x x := by
  let f := fun t : ℝ => (1-x^2)*(1/((x^2+t)*(x^2+t)))
  let k := fun t : ℝ => x*(1/(Real.sqrt (x^2+t)*(x^2+t)))
  have hf : IntegrableOn f (Ioi 0) :=
    (pairKernel_integrable (x^2) (x^2) (sq_pos_of_pos hx) (sq_pos_of_pos hx)).const_mul _
  have hk : IntegrableOn k (Ioi 0) := (root_tail (x^2) (sq_pos_of_pos hx)).1.const_mul _
  have h := integral_mono_ae (hf.add hk) (weighted_pair_integrable x x hx hx1 hx hx1) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have hxt : 0 < x^2+t := by positivity
    change f t + k t ≤ _
    calc
      _ = (1-x^2+x*Real.sqrt (x^2+t))*(1/((x^2+t)*(x^2+t))) := by
        dsimp [f,k]
        rw [← sqrt_div_sq _ hxt]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (sqrt_chord x t hx hx1 ht0) (by positivity))
  simp only [Pi.add_apply] at h
  rw [integral_add hf hk] at h
  dsimp [f,k] at h
  rw [integral_const_mul, integral_const_mul, (root_tail (x^2) (sq_pos_of_pos hx)).2,
    Real.sqrt_sq hx.le] at h
  change (1-x^2)*pair (x^2) (x^2) + x*(2/x) ≤ _ at h
  rw [pair_self _ (sq_pos_of_pos hx)] at h
  have he : (x*x/2)*((1-x^2)*(1/x^2)+x*(2/x)) = (1+x^2)/2 := by field_simp; ring
  unfold evenGram
  rw [← he]
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- The normalized even rational profile in the reciprocal variable. -/
private def evenEnergy (δ a b t : ℝ) : ℝ :=
  (a/(1+t)+b*δ/(δ^2+t))^2/2

private lemma even_energy_eval (w : ℝ → ℝ) (δ a b : ℝ)
    (h11 : IntegrableOn (fun t => w t * (1/((1+t)*(1+t)))) (Ioi 0))
    (h1d : IntegrableOn (fun t => w t * (1/((1+t)*(δ^2+t)))) (Ioi 0))
    (hdd : IntegrableOn (fun t => w t * (1/((δ^2+t)*(δ^2+t)))) (Ioi 0)) :
    IntegrableOn (fun t => w t * evenEnergy δ a b t) (Ioi 0) ∧
      (∫ t in Ioi (0:ℝ), w t * evenEnergy δ a b t) =
      (a^2/2)*(∫ t in Ioi (0:ℝ), w t * (1/((1+t)*(1+t)))) +
      (a*b*δ)*(∫ t in Ioi (0:ℝ), w t * (1/((1+t)*(δ^2+t)))) +
      (b^2*δ^2/2)*(∫ t in Ioi (0:ℝ), w t * (1/((δ^2+t)*(δ^2+t)))) := by
  have hi := h11.const_mul (a^2/2)
  have hj := h1d.const_mul (a*b*δ)
  have hk := hdd.const_mul (b^2*δ^2/2)
  have he (t : ℝ) : w t * evenEnergy δ a b t =
      (a^2/2)*(w t * (1/((1+t)*(1+t)))) +
      (a*b*δ)*(w t * (1/((1+t)*(δ^2+t)))) +
      (b^2*δ^2/2)*(w t * (1/((δ^2+t)*(δ^2+t)))) := by
    unfold evenEnergy
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  refine ⟨IntegrableOn.congr_fun ((hi.add hj).add hk) (fun t _ => (he t).symm) measurableSet_Ioi, ?_⟩
  simp_rw [he]
  have h := integral_add (hi.add hj) hk
  simp only [Pi.add_apply] at h
  rw [h, integral_add hi hj, integral_const_mul, integral_const_mul, integral_const_mul]

/-- The even parity sector has the same coefficient as the odd sector, with
no distinction between equal and distinct marginal eigenvalues. -/
private theorem weighted_even_bound (δ a b : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (a+b)^2 ≤ (1+2/(1+δ^2)) *
      (∫ t in Ioi (0:ℝ), Real.sqrt (1+t)*evenEnergy δ a b t) := by
  have h1 : (0:ℝ) < 1 := by norm_num
  have hd2 := sq_pos_of_pos hδ
  obtain ⟨hi, hE⟩ := even_energy_eval (fun t => Real.sqrt (1+t)) δ a b
    (by simpa using weighted_pair_integrable 1 1 h1 le_rfl h1 le_rfl)
    (by simpa using weighted_pair_integrable 1 δ h1 le_rfl hδ hδ1)
    (weighted_pair_integrable δ δ hδ hδ1 hδ hδ1)
  obtain ⟨hj, hL⟩ := even_energy_eval (fun _ => 1) δ a b
    (by simpa using pairKernel_integrable 1 1 h1 h1)
    (by simpa using pairKernel_integrable 1 (δ^2) h1 hd2)
    (by simpa using pairKernel_integrable (δ^2) (δ^2) hd2 hd2)
  simp only [one_mul] at hj hL
  have hE' : (∫ t in Ioi (0:ℝ), Real.sqrt (1+t)*evenEnergy δ a b t) =
      a^2*evenGram 1 1 + 2*a*b*evenGram 1 δ + b^2*evenGram δ δ := by
    rw [hE]
    simp only [evenGram, one_pow]
    ring
  have hL' : (∫ t in Ioi (0:ℝ), evenEnergy δ a b t) =
      a^2*evenLowerGram 1 1 + 2*a*b*evenLowerGram 1 δ + b^2*evenLowerGram δ δ := by
    rw [hL]
    simp only [evenLowerGram, pair, one_pow]
    ring
  let Q := a^2*evenGram 1 1 + 2*a*b*evenGram 1 δ + b^2*evenGram δ δ
  let C := 1+2/(1+δ^2)
  have hc : 2 ≤ C := by
    dsimp [C]
    have he : δ^2 ≤ 1 := by nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hδ1)]
    have hf : 1 ≤ 2/(1+δ^2) := (le_div_iff₀ (by positivity)).2 (by linarith)
    linarith
  have hq1 : 1 ≤ evenGram 1 1 := by simpa using even_gram_diag 1 h1 le_rfl
  have hqδ := even_gram_diag δ hδ hδ1
  rw [hE']
  change (a+b)^2 ≤ C*Q
  rcases le_or_gt (a*b) 0 with hab | hab
  · have hcross := even_cross_le 1 δ h1 hδ
    have hmono : (∫ t in Ioi (0:ℝ), evenEnergy δ a b t) ≤
        (∫ t in Ioi (0:ℝ), Real.sqrt (1+t)*evenEnergy δ a b t) := by
      apply integral_mono_ae hj hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := ht
      have hs : 1 ≤ Real.sqrt (1+t) := by
        simpa using Real.sqrt_le_sqrt (show 1 ≤ 1+t by linarith)
      have he : 0 ≤ evenEnergy δ a b t := by unfold evenEnergy; positivity
      simpa using mul_le_mul_of_nonneg_right hs he
    rw [hL', hE', even_diag _ h1, even_diag _ hδ] at hmono
    have hq : (a+b)^2/2 ≤ Q := by
      dsimp [Q]
      nlinarith only [hmono, mul_nonneg (sub_nonneg.mpr hcross) (neg_nonneg.mpr hab)]
    have hQ : 0 ≤ Q := le_trans (by positivity) hq
    nlinarith only [hq, mul_le_mul_of_nonneg_right hc hQ]
  · have hcross := even_gram_nonneg 1 δ h1 hδ
    have hq : a^2 + ((1+δ^2)/2)*b^2 ≤ Q := by
      dsimp [Q]
      nlinarith only [mul_le_mul_of_nonneg_left hq1 (sq_nonneg a),
        mul_le_mul_of_nonneg_left hqδ (sq_nonneg b), mul_nonneg hab.le hcross]
    let d := (1+δ^2)/2
    have hd : 0 < d := by dsimp [d]; positivity
    have hC : C = 1+1/d := by dsimp [C,d]; field_simp
    have hCS : (a+b)^2 ≤ C*(a^2+d*b^2) := by
      rw [hC]
      apply le_of_sub_nonneg
      rw [show (1+1/d)*(a^2+d*b^2)-(a+b)^2 = (a-d*b)^2/d by field_simp [hd.ne']; ring]
      positivity
    exact hCS.trans (mul_le_mul_of_nonneg_left hq (by linarith : 0 ≤ C))

private lemma weighted_even_energy_integrable (δ a b : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    IntegrableOn (fun t => Real.sqrt (1+t)*evenEnergy δ a b t) (Ioi 0) := by
  have h1 : (0:ℝ) < 1 := by norm_num
  exact (even_energy_eval (fun t => Real.sqrt (1+t)) δ a b
    (by simpa using weighted_pair_integrable 1 1 h1 le_rfl h1 le_rfl)
    (by simpa using weighted_pair_integrable 1 δ h1 le_rfl hδ hδ1)
    (weighted_pair_integrable δ δ hδ hδ1 hδ hδ1)).1

/-- Complex even energy in the reciprocal variable, retaining the two-node
cross term for arbitrary complex coefficients. -/
def evenComplexEnergy (δ : ℝ) (a b : ℂ) (t : ℝ) : ℝ :=
  Complex.normSq (a * ((1/(1+t) : ℝ) : ℂ) + b * ((δ/(δ^2+t) : ℝ) : ℂ))/2

/-- Complex odd energy in the reciprocal variable. -/
def oddComplexEnergy (g δ : ℝ) (a b : ℂ) (t : ℝ) : ℝ :=
  Complex.normSq (a * (((g+1)/(1+t) : ℝ) : ℂ) +
    b * ((δ*(g+δ)/(δ^2+t) : ℝ) : ℂ))/(2*(g^2+t))

/-- Even dual energy bound for fully complex coefficients. -/
private theorem weighted_even_complex_bound (δ : ℝ) (a b : ℂ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Complex.normSq (a+b) ≤ (1+2/(1+δ^2)) *
      (∫ t in Ioi (0:ℝ), Real.sqrt (1+t)*evenComplexEnergy δ a b t) := by
  have hR := weighted_even_bound δ a.re b.re hδ hδ1
  have hI := weighted_even_bound δ a.im b.im hδ hδ1
  have he (t : ℝ) : Real.sqrt (1+t)*evenComplexEnergy δ a b t =
      Real.sqrt (1+t)*evenEnergy δ a.re b.re t + Real.sqrt (1+t)*evenEnergy δ a.im b.im t := by
    simp only [evenComplexEnergy, evenEnergy, Complex.normSq_apply, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, zero_add]
    ring
  simp_rw [he]
  rw [integral_add (weighted_even_energy_integrable δ _ _ hδ hδ1)
    (weighted_even_energy_integrable δ _ _ hδ hδ1), mul_add]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, ← pow_two]
  exact add_le_add hR hI

/-- Odd dual energy bound for fully complex coefficients. -/
private theorem weighted_odd_complex_bound (g δ : ℝ) (a b : ℂ) (hg : 0 < g) (hg1 : g ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Complex.normSq (a+b) ≤ (1+2/(1+δ^2)) *
      (∫ t in Ioi (0:ℝ), Real.sqrt (1+t)*oddComplexEnergy g δ a b t) := by
  have hR := weighted_odd_bound g δ a.re b.re hg hg1 hδ hδ1
  have hI := weighted_odd_bound g δ a.im b.im hg hg1 hδ hδ1
  have he (t : ℝ) : Real.sqrt (1+t)*oddComplexEnergy g δ a b t =
      Real.sqrt (1+t)*oddEnergy g δ a.re b.re t + Real.sqrt (1+t)*oddEnergy g δ a.im b.im t := by
    simp only [oddComplexEnergy, oddEnergy, Complex.normSq_apply, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, zero_add]
    ring
  simp_rw [he]
  rw [integral_add (weighted_odd_energy_integrable g δ _ _ hg hg1 hδ)
    (weighted_odd_energy_integrable g δ _ _ hg hg1 hδ), mul_add]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, ← pow_two]
  exact add_le_add hR hI

/-- The paired parity estimate, in normalized reciprocal coordinates.
For the arcsine residual, the first two coefficients are scaled by `1/x`
and the last two by `1/(x*(x+g))`, where `x` ranges over `1, δ`. -/
theorem paired_parity_bound (g β δ : ℝ) (a b c d : ℂ)
    (hg : 0 < g) (hg1 : g ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hgb : g^2+β^2 = 1) :
    Complex.normSq ((g : ℂ)*(a+b)+(β : ℂ)*(c+d)) ≤ (1+2/(1+δ^2)) *
      ((∫ t in Ioi (0:ℝ), Real.sqrt (1+t)*evenComplexEnergy δ a b t) +
        (∫ t in Ioi (0:ℝ), Real.sqrt (1+t)*oddComplexEnergy g δ c d t)) := by
  have hE := weighted_even_complex_bound δ a b hδ hδ1
  have hO := weighted_odd_complex_bound g δ c d hg hg1 hδ hδ1
  have hrot (z w : ℂ) : Complex.normSq ((g : ℂ)*z+(β : ℂ)*w) +
      Complex.normSq ((β : ℂ)*z-(g : ℂ)*w) =
      (g^2+β^2)*(Complex.normSq z+Complex.normSq w) := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, add_zero]
    ring
  have h := hrot (a+b) (c+d)
  rw [hgb, one_mul] at h
  have hn := Complex.normSq_nonneg ((β : ℂ)*(a+b)-(g : ℂ)*(c+d))
  calc
    _ ≤ Complex.normSq (a+b) + Complex.normSq (c+d) := by linarith only [h, hn]
    _ ≤ _ := by simpa only [mul_add] using add_le_add hE hO

#print axioms paired_parity_bound

end D5.S3.Quantum.Recovery.PetzTangentReciprocalGram
