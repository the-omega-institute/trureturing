/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CentralMarginalBounds
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict lower slope bound for the reflected marginal in the central BMV certificate. -/

import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterMoments
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterRegularized
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterTailFormula

/-! # Lower bounds on the reflected central BMV marginal slope -/

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace RefinedBMV.PositiveCenter

open DimThree (gaps)
open SmallCorner

noncomputable section

private theorem tilted_mean_integral_le (b m t : ℝ) (ht : 0 ≤ t) :
    let w (s : ℝ) := (1 - s) * Real.exp (-t * (b * s))
    (∫ s in (0 : ℝ)..1, (1 - s) * (b * s) ^ (1 : ℕ) * Real.exp (-t * (b * s))) -
      m * (∫ s in (0 : ℝ)..1, w s) ≤ Real.exp (-t * m) * (b / 6 - m / 2) := by
  dsimp only
  let f (s : ℝ) := (1 - s) * (b * s - m) * Real.exp (-t * (b * s))
  let g (s : ℝ) := (1 - s) * (b * s - m) * Real.exp (-t * m)
  have hf : Continuous f := by unfold f; fun_prop
  have hg : Continuous g := by unfold g; fun_prop
  have h := intervalIntegral.integral_mono_on (μ := volume) zero_le_one
    (hf.intervalIntegrable 0 1) (hg.intervalIntegrable 0 1) (fun s hs ↦ by
      have hw : 0 ≤ 1 - s := sub_nonneg.mpr hs.2
      have he : Antitone (fun x : ℝ ↦ Real.exp (-t * x)) := fun x y hxy ↦
        Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hxy (neg_nonpos.mpr ht))
      dsimp only [f, g]
      -- The signed difference reverses the comparison below the untilted mean.
      rcases le_total m (b * s) with hms | hsm
      · exact mul_le_mul_of_nonneg_left (he hms) (mul_nonneg hw (sub_nonneg.mpr hms))
      · exact mul_le_mul_of_nonpos_left (he hsm)
          (mul_nonpos_of_nonneg_of_nonpos hw (sub_nonpos.mpr hsm)))
  have integral_split (e : ℝ → ℝ) (he : Continuous e) :
      (∫ s in (0 : ℝ)..1, (1 - s) * (b * s - m) * e s) =
        (∫ s in (0 : ℝ)..1, (1 - s) * (b * s) * e s) -
          m * (∫ s in (0 : ℝ)..1, (1 - s) * e s) := by
    simp_rw [show ∀ s : ℝ, (1 - s) * (b * s - m) * e s =
      (1 - s) * (b * s) * e s - m * ((1 - s) * e s) from fun s ↦ by ring]
    rw [intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) 0 1)
      (Continuous.intervalIntegrable (by fun_prop) 0 1), intervalIntegral.integral_const_mul]
  dsimp only [f, g] at h
  rw [integral_split _ (by fun_prop), integral_split _ continuous_const] at h
  simp_rw [show ∀ s : ℝ, (1 - s) * (b * s) * Real.exp (-t * m) =
    (b * Real.exp (-t * m)) * ((1 - s) * s ^ (1 : ℕ)) from fun s ↦ by ring,
    show ∀ s : ℝ, (1 - s) * Real.exp (-t * m) =
    Real.exp (-t * m) * ((1 - s) * s ^ (0 : ℕ)) from fun s ↦ by ring,
    intervalIntegral.integral_const_mul, unit_weight_moment] at h
  simp only [pow_one, neg_mul]
  norm_num at h
  linarith only [h]

/-- The normalized reflected marginal has a logarithmic slope bounded below
by its quadratic contribution and the cubic correction at zero. -/
theorem centralMarginal_halfLogDeriv_ge_quadratic {p : ℕ} (hp : 0 < p)
    {t : ℝ} (ht : 0 < t) :
    1 / t - (2 + 3 / (p : ℝ)) / 30 ≤
      deriv (fun s ↦ compositionMoment p 0 (-s)) t / (2 * compositionMoment p 0 (-t)) := by
  let m : ℝ := (2 + 3 / (p : ℝ)) / 15
  let y (g : ℕ × ℕ × ℕ) : ℝ := 3 * (g.2.2 : ℝ) / p - 1
  let N : ℝ := (gaps p).length
  have hN : 0 < N := by
    dsimp only [N]
    exact_mod_cast (DimThree.word_counts_all p).2.1
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hsq : ((gaps p).map fun g ↦ y g ^ 2).sum = N * ((p : ℝ) + 3) / (2 * p) :=
    (centered_marginal_sums hp).2
  have hcube : ((gaps p).map fun g ↦ y g ^ 3).sum =
      N * ((p : ℝ) + 3) * (2 * (p : ℝ) + 3) / (10 * (p : ℝ) ^ 2) :=
    centered_marginal_cubic_sum hp
  have hm : ((gaps p).map fun g ↦ y g ^ 3).sum / 6 =
      m * (((gaps p).map fun g ↦ y g ^ 2).sum / 2) := by
    rw [hsq, hcube]
    dsimp only [m]
    field_simp [hpR.ne']
    ring
  let I (k : ℕ) (g : ℕ × ℕ × ℕ) : ℝ :=
    y g ^ 2 * ∫ s in (0 : ℝ)..1, (1 - s) * (y g * s) ^ k * Real.exp (-t * (y g * s))
  have hpoint (g : ℕ × ℕ × ℕ) :
      I 1 g - m * I 0 g ≤
        Real.exp (-t * m) * (y g ^ 3 / 6 - m * (y g ^ 2 / 2)) := by
    have h := mul_le_mul_of_nonneg_left (tilted_mean_integral_le (y g) m t ht.le)
      (sq_nonneg (y g))
    dsimp only [I]
    simp only [pow_zero, mul_one] at h ⊢
    nlinarith only [h]
  have hsum (l : List (ℕ × ℕ × ℕ)) :
      (l.map (I 1)).sum - m * (l.map (I 0)).sum ≤
        Real.exp (-t * m) * ((l.map fun g ↦ y g ^ 3).sum / 6 -
          m * ((l.map fun g ↦ y g ^ 2).sum / 2)) := by
    induction l with
    | nil => simp
    | cons g l ih =>
      simp only [List.map_cons, List.sum_cons]
      linarith only [show _ ≤ _ from add_le_add (hpoint g) ih]
  have hmean := hsum (gaps p)
  rw [hm, sub_self, mul_zero, sub_nonpos] at hmean
  have hG₀ := iteratedDeriv_G_eq_integral (p := p) hp (c := 1)
    one_ne_zero (neg_ne_zero.mpr ht.ne') 0
  have hG₁ := iteratedDeriv_G_eq_integral (p := p) hp (c := 1)
    one_ne_zero (neg_ne_zero.mpr ht.ne') 1
  rw [iteratedDeriv_zero] at hG₀
  rw [iteratedDeriv_one] at hG₁
  change G p 1 (-t) = ((gaps p).map (I 0)).sum / (N * 1) at hG₀
  change deriv (G p 1) (-t) = ((gaps p).map (I 1)).sum / (N * 1) at hG₁
  have hGmean : deriv (G p 1) (-t) ≤ m * G p 1 (-t) := by
    rw [hG₀, hG₁, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right hmean (by positivity)
  have hG' : HasDerivAt (fun s : ℝ ↦ G p 1 (-s)) (-deriv (G p 1) (-t)) t := by
    have h := hasDerivAt_G p (c := 1) one_ne_zero (neg_ne_zero.mpr ht.ne')
    simpa only [h.deriv, Function.comp_def, id_eq, mul_neg, mul_one] using
      (h.comp t (hasDerivAt_id' t).neg)
  have hEq (s : ℝ) (hs : 0 < s) : s ^ 2 * G p 1 (-s) = compositionMoment p 0 (-s) := by
    simp only [G, one_mul, neg_sq]
    exact mul_div_cancel₀ _ (pow_ne_zero _ hs.ne')
  have hD : HasDerivAt (fun s ↦ compositionMoment p 0 (-s))
      (2 * t * G p 1 (-t) + t ^ 2 * (-deriv (G p 1) (-t))) t := by
    have hProd : HasDerivAt (fun s : ℝ ↦ s ^ 2 * G p 1 (-s))
        (2 * t * G p 1 (-t) + t ^ 2 * (-deriv (G p 1) (-t))) t := by
      simpa using (hasDerivAt_pow 2 t).fun_mul hG'
    apply hProd.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds ht] with s hs using (hEq s hs).symm
  rw [show (2 + 3 / (p : ℝ)) / 30 = m / 2 by dsimp only [m]; ring]
  rw [hD.deriv, le_div_iff₀ (mul_pos (by norm_num)
    (compositionMoment_marginal_pos hp (neg_ne_zero.mpr ht.ne'))), ← hEq t ht]
  calc
    _ = 2 * t * G p 1 (-t) - t ^ 2 * (m * G p 1 (-t)) := by
      field_simp [ht.ne']
    _ ≤ _ := by
      linarith only [mul_le_mul_of_nonneg_left hGmean (sq_nonneg t)]

#print axioms centralMarginal_halfLogDeriv_ge_quadratic

private theorem central_exp_window {t : ℝ} (ht₂ : 2 ≤ t) (ht₆ : t ≤ 6) :
    Real.exp t * (6 - t) / t ^ 2 < 15 / 2 := by
  let f (x : ℝ) := Real.exp x * (6 - x) / x ^ 2
  have hderiv {x : ℝ} (hx : 0 < x) : HasDerivAt f
      (-(Real.exp x * ((x - 3) * (x - 4))) / x ^ 3) x := by
    apply (((Real.hasDerivAt_exp x).fun_mul ((hasDerivAt_id' x).const_sub 6)).fun_div
      (hasDerivAt_pow 2 x) (pow_ne_zero 2 hx.ne')).congr_deriv
    field_simp [hx.ne']
    ring
  have hdiff {a b : ℝ} (ha : 0 < a) : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x :=
    fun _ hx ↦ (hderiv (ha.trans_le hx.1)).differentiableAt
  have hanti {a b : ℝ} (ha : 0 < a)
      (hsign : ∀ x ∈ Icc a b, 0 ≤ (x - 3) * (x - 4)) : AntitoneOn f (Icc a b) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (fun x hx ↦ (hdiff ha x hx).continuousAt.continuousWithinAt)
      (fun x hx ↦ (hdiff ha x (interior_subset hx)).differentiableWithinAt) ?_
    intro x hx
    have hmem := interior_subset hx
    have hx₀ := ha.trans_le hmem.1
    rw [(hderiv hx₀).deriv]
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (mul_nonneg (Real.exp_pos _).le (hsign x hmem))) (by positivity)
  have hleft : AntitoneOn f (Icc 2 3) :=
    hanti (by norm_num) fun x hx ↦ mul_nonneg_of_nonpos_of_nonpos
      (sub_nonpos.mpr hx.2) (sub_nonpos.mpr (hx.2.trans (by norm_num)))
  have hright : AntitoneOn f (Icc 4 6) :=
    hanti (by norm_num) fun _ hx ↦
      mul_nonneg (sub_nonneg.mpr ((by norm_num : (3 : ℝ) ≤ 4).trans hx.1)) (sub_nonneg.mpr hx.1)
  have hmiddle : MonotoneOn f (Icc 3 4) := by
    have ha : (0 : ℝ) < 3 := by norm_num
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun x hx ↦ (hdiff ha x hx).continuousAt.continuousWithinAt)
      (fun x hx ↦ (hdiff ha x (interior_subset hx)).differentiableWithinAt) ?_
    intro x hx
    have hmem : x ∈ Icc (3 : ℝ) 4 := interior_subset hx
    have hx₀ := ha.trans_le hmem.1
    rw [(hderiv hx₀).deriv]
    exact div_nonneg
      (neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
        (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hmem.1) (sub_nonpos.mpr hmem.2))))
      (by positivity)
  have he : Real.exp 1 < 87 / 32 := Real.exp_one_lt_d9.trans (by norm_num)
  have hexp (n : ℕ) : Real.exp (n : ℝ) = Real.exp 1 ^ n := by
    simpa only [mul_one] using Real.exp_nat_mul 1 n
  have hf₂ : f 2 < 15 / 2 := by
    have h := pow_lt_pow_left₀ he (Real.exp_pos _).le (by decide : 2 ≠ 0)
    have he₂ : Real.exp (2 : ℝ) = Real.exp 1 ^ 2 := by exact_mod_cast hexp 2
    dsimp only [f]
    rw [he₂]
    norm_num at h ⊢
    linarith only [h]
  have hf₄ : f 4 < 15 / 2 := by
    have h := pow_lt_pow_left₀ he (Real.exp_pos _).le (by decide : 4 ≠ 0)
    have he₄ : Real.exp (4 : ℝ) = Real.exp 1 ^ 4 := by exact_mod_cast hexp 4
    dsimp only [f]
    rw [he₄]
    norm_num at h ⊢
    linarith only [h]
  change f t < _
  by_cases h₃ : t ≤ 3
  · exact (hleft (by norm_num) ⟨ht₂, h₃⟩ ht₂).trans_lt hf₂
  by_cases h₄ : t ≤ 4
  · exact (hmiddle ⟨le_of_not_ge h₃, h₄⟩ (by norm_num) h₄).trans_lt hf₄
  · exact (hright (by norm_num) ⟨le_of_not_ge h₄, ht₆⟩ (le_of_not_ge h₄)).trans_lt hf₄

private theorem reflected_marginal_geometric {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) :
    let h : ℝ := 3 / (p : ℝ)
    let M (s : ℝ) := compositionMoment p 0 (-s)
    (1 - upperTailSlope h t) * (M t + 1) < deriv M t ∧
      M t + 1 ≤ 2 * Real.exp t * (h + upperTailSlope h t) / (3 + 2 * h) := by
  dsimp only
  let h : ℝ := 3 / (p : ℝ)
  let n : ℝ := (p + 2).choose 2
  let M (s : ℝ) := compositionMoment p 0 (-s)
  let E (s : ℝ) := upperTailGap h s * Real.exp (-s)
  let r (i : ℕ) : ℝ := -((i : ℝ) + 1) * h
  let S (s : ℝ) := (p + 1 : ℝ) - ∑ i ∈ Finset.range (p + 1), Real.exp (r i * s)
  change (1 - upperTailSlope h t) * (M t + 1) < deriv M t ∧ _
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h]; positivity
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (Nat.choose_pos (show 2 ≤ p + 2 by omega))
  have hId (s : ℝ) (hs : 0 < s) : S s = (n * h) * E s * (M s + 1) := by
    have hLow := upperTail_lower_weight hp s 0
    dsimp only at hLow
    simp only [zero_add, mul_zero, neg_zero, zero_div, Real.exp_zero] at hLow
    have hUp := upperTail_upper_weight hp hs
    dsimp only at hUp
    rw [(tail_cube_pow hp s).1, hLow] at hUp
    have hNorm : (p + 1 : ℝ) * upperTailNormalizer (p + 1) h (n / (p + 1)) s =
        S s - (1 - Real.exp (-(h * s))) * n * Real.exp (-s) := by
      have hp1 : (p + 1 : ℝ) ≠ 0 := by positivity
      unfold upperTailNormalizer
      push_cast
      change (p + 1 : ℝ) * (1 - (∑ i ∈ Finset.range (p + 1), Real.exp (r i * s)) / (p + 1) -
        (n / (p + 1)) * ((1 - Real.exp (-(h * s))) * Real.exp (-s))) = _
      dsimp only [S]
      generalize (∑ i ∈ Finset.range (p + 1), Real.exp (r i * s)) = A
      field_simp [hp1]
    change (1 - Real.exp (-(h * s))) * (n * Real.exp (-s) * M s) =
      (p + 1 : ℝ) * upperTailNormalizer (p + 1) h (n / (p + 1)) s at hUp
    rw [hNorm, tail_gap_factor hh] at hUp
    change S s = n * h * (upperTailGap h s * Real.exp (-s)) * (M s + 1)
    linear_combination -hUp
  have hScale (s : ℝ) (hs : 0 < s) : 0 < (n * h) * E s :=
    mul_pos (mul_pos hn hh) (mul_pos (tail_gap_pos hh hs) (Real.exp_pos _))
  constructor
  · have hdE : HasDerivAt E ((upperTailSlope h t - 1) * E t) t := by
      have hgap := hasDerivAt_upperTailGap (t := t) hh
      have hL := (div_eq_iff (tail_gap_pos hh ht).ne').mp (upperTailGap_logDeriv hh ht)
      rw [hgap.deriv] at hL
      have hneg : HasDerivAt (fun s : ℝ ↦ -s) (-1) t := (hasDerivAt_id' t).neg
      apply (hgap.fun_mul hneg.exp).congr_deriv
      dsimp only [E]
      rw [hL]
      ring
    have hterm (i : ℕ) : HasDerivAt (fun s : ℝ ↦ Real.exp (r i * s))
        (r i * Real.exp (r i * t)) t := by
      have hlin : HasDerivAt (fun s : ℝ ↦ r i * s) (r i) t := by
        simpa only [mul_one] using (hasDerivAt_id' t).const_mul (r i)
      simpa only [mul_comm] using hlin.exp
    have hsum := HasDerivAt.fun_sum (u := Finset.range (p + 1)) (fun i _ ↦ hterm i)
    have hdS := hsum.const_sub (p + 1 : ℝ)
    change HasDerivAt S _ t at hdS
    have hS : 0 < deriv S t := by
      rw [hdS.deriv, neg_pos]
      apply Finset.sum_neg'
      · intro i _
        exact (mul_neg_of_neg_of_pos
          (mul_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) hh) (Real.exp_pos _)).le
      · refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
        dsimp only [r]
        exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos
          (neg_neg_of_pos (by positivity)) hh) (Real.exp_pos _)
    have hNear : S =ᶠ[𝓝 t] fun s ↦ (n * h) * E s * (M s + 1) := by
      filter_upwards [eventually_gt_nhds ht] with s hs using hId s hs
    have hNearDiv : (fun s ↦ S s / ((n * h) * E s) - 1) =ᶠ[𝓝 t] M := by
      filter_upwards [eventually_gt_nhds ht] with s hs
      rw [hId s hs]
      rw [mul_comm _ (M s + 1), mul_div_cancel_right₀ _ (hScale s hs).ne', add_sub_cancel_right]
    have hM : DifferentiableAt ℝ M t := by
      have hQuot := (hdS.div (hdE.const_mul (n * h)) (hScale t ht).ne').sub_const 1
      exact hQuot.differentiableAt.congr_of_eventuallyEq hNearDiv.symm
    have hProd := (hdE.const_mul (n * h)).fun_mul (hM.hasDerivAt.add_const 1)
    rw [hNear.deriv_eq, hProd.deriv] at hS
    apply (mul_lt_mul_iff_of_pos_left (hScale t ht)).mp
    linarith only [hS, show n * h * ((upperTailSlope h t - 1) * E t) * (M t + 1) =
      -(n * h * E t * ((1 - upperTailSlope h t) * (M t + 1))) by ring]
  · change M t + 1 ≤ 2 * Real.exp t * (h + upperTailSlope h t) / (3 + 2 * h)
    have hsum : S t ≤ (p + 1 : ℝ) :=
      sub_le_self _ (Finset.sum_nonneg fun _ _ ↦ (Real.exp_pos _).le)
    rw [hId t ht] at hsum
    have hnh : n * h = (p + 1 : ℝ) * (3 + 2 * h) / 2 := by
      dsimp only [n, h]
      rw [Nat.cast_choose_two]
      push_cast
      field_simp [hpR.ne']
      <;> ring
    have hF := tail_gap_pos hh ht
    have hLF : (h + upperTailSlope h t) * upperTailGap h t = 1 := by
      have hL := (div_eq_iff hF.ne').mp (upperTailGap_logDeriv hh ht)
      rw [(hasDerivAt_upperTailGap hh).deriv] at hL
      have hgap := tail_gap_factor (t := t) hh
      linarith only [hL, hgap, add_mul h (upperTailSlope h t) (upperTailGap h t)]
    apply (mul_le_mul_iff_of_pos_left (hScale t ht)).mp
    refine hsum.trans_eq ?_
    have hden : 0 < 3 + 2 * h := by positivity
    dsimp only [E]
    rw [hnh]
    field_simp [hden.ne']
    calc
      1 = ((h + upperTailSlope h t) * upperTailGap h t) * (Real.exp (-t) * Real.exp t) := by
        rw [hLF, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
      _ = _ := by ring

private theorem centralMarginal_halfLogDeriv_gt_of_two_le {p : ℕ} (hp : 0 < p)
    {t : ℝ} (ht₂ : 2 ≤ t) :
    5 / 12 < deriv (fun s ↦ compositionMoment p 0 (-s)) t /
      (2 * compositionMoment p 0 (-t)) := by
  let h : ℝ := 3 / (p : ℝ)
  let L := upperTailSlope h t
  let M (s : ℝ) := compositionMoment p 0 (-s)
  have ht : 0 < t := by linarith
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h]; positivity
  have hM : 0 < M t := compositionMoment_marginal_pos hp (neg_ne_zero.mpr ht.ne')
  obtain ⟨hD, hB⟩ := reflected_marginal_geometric hp ht
  change (1 - L) * (M t + 1) < deriv M t at hD
  change M t + 1 ≤ 2 * Real.exp t * (h + L) / (3 + 2 * h) at hB
  change 5 / 12 < deriv M t / (2 * M t)
  apply (lt_div_iff₀ (mul_pos (by norm_num) hM)).2
  suffices hbudget : (6 * L - 1) * (M t + 1) < 5 by linarith only [hbudget, hD]
  by_cases hL₆ : L ≤ 1 / 6
  · have hsgn : 6 * L - 1 ≤ 0 := by linarith
    have hproduct := mul_nonpos_of_nonpos_of_nonneg hsgn (add_nonneg hM.le zero_le_one)
    exact hproduct.trans_lt (by norm_num)
  have hsgn : 0 ≤ 6 * L - 1 := by linarith
  obtain ⟨_, hL, _, hprod, _, _⟩ := upperTailSlope_bounds hh ht
  rw [(hasDerivAt_upperTailSlope hh ht).deriv, neg_neg] at hprod
  change L * (h + L) ≤ 1 / t ^ 2 at hprod
  have ht₆ : t ≤ 6 := by
    have hLt : L ≤ 1 / t := hL
    have hi : (1 : ℝ) / 6 ≤ 1 / t := (le_of_not_ge hL₆).trans hLt
    have hcross := (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 6) ht).mp hi
    linarith only [hcross]
  have hF := tail_gap_pos hh ht
  have hsum : 1 / t ≤ h + L := by
    have hDerivative := (div_eq_iff hF.ne').mp (upperTailGap_logDeriv hh ht)
    rw [(hasDerivAt_upperTailGap hh).deriv] at hDerivative
    change Real.exp (-(h * t)) = L * upperTailGap h t at hDerivative
    have hg := tail_gap_factor (t := t) hh
    have hidentity : h + L = 1 / upperTailGap h t := (eq_div_iff hF.ne').2 (by
      rw [add_mul, ← hDerivative, ← hg]
      ring)
    rw [hidentity]
    exact one_div_le_one_div_of_le hF (upperTailGap_le hh)
  have hpoly : (6 * L - 1) * (h + L) ≤ (6 - t) / t ^ 2 := by
    have hrewrite : (6 - t) / t ^ 2 = 6 * (1 / t ^ 2) - 1 / t := by
      field_simp [ht.ne']
    rw [hrewrite]
    linarith only [hprod, hsum, show (6 * L - 1) * (h + L) =
      6 * (L * (h + L)) - (h + L) by ring]
  have hden : 0 < 3 + 2 * h := by positivity
  have hnonneg : 0 ≤ 2 * (Real.exp t * (6 - t) / t ^ 2) :=
    mul_nonneg (by norm_num) (div_nonneg (mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr ht₆))
      (sq_nonneg _))
  calc
    _ ≤ (6 * L - 1) * (2 * Real.exp t * (h + L) / (3 + 2 * h)) :=
      mul_le_mul_of_nonneg_left hB hsgn
    _ = (2 * Real.exp t * ((6 * L - 1) * (h + L))) / (3 + 2 * h) := by ring
    _ ≤ (2 * Real.exp t * ((6 - t) / t ^ 2)) / (3 + 2 * h) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly (by positivity)) hden.le
    _ = (2 * (Real.exp t * (6 - t) / t ^ 2)) / (3 + 2 * h) := by ring
    _ ≤ (2 * (Real.exp t * (6 - t) / t ^ 2)) / 3 :=
      div_le_div_of_nonneg_left hnonneg (by norm_num) (by linarith)
    _ < 5 := by linarith only [central_exp_window ht₂ ht₆]

/-- The reflected marginal in the normalized central BMV certificate has
strict logarithmic half-slope greater than five twelfths at every positive gap. -/
theorem centralMarginal_halfLogDeriv_gt_five_twelfths {p : ℕ} (hp : 11 ≤ p)
    {t : ℝ} (ht : 0 < t) :
    5 / 12 < deriv (fun s ↦ compositionMoment p 0 (-s)) t /
      (2 * compositionMoment p 0 (-t)) := by
  have hp₀ : 0 < p := by omega
  by_cases ht₂ : 2 ≤ t
  · exact centralMarginal_halfLogDeriv_gt_of_two_le hp₀ ht₂
  · have hpR : (11 : ℝ) ≤ p := by exact_mod_cast hp
    have hh : 3 / (p : ℝ) ≤ 3 / 11 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpR
    have htinv := one_div_le_one_div_of_le ht (le_of_not_ge ht₂)
    exact (show (5 : ℝ) / 12 < 1 / t - (2 + 3 / (p : ℝ)) / 30 by
      linarith only [hh, htinv]).trans_le (centralMarginal_halfLogDeriv_ge_quadratic hp₀ ht)

#print axioms centralMarginal_halfLogDeriv_gt_five_twelfths

end

end RefinedBMV.PositiveCenter
