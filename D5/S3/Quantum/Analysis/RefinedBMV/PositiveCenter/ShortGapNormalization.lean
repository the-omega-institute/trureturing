/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/ShortGapNormalization
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Logarithmic derivative bounds for the short-gap normalization. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortGapMoments

/-! Affine mixed derivative formula for the short-gap kernel. -/

open Filter Set
open scoped Topology BigOperators

namespace RefinedBMV.PositiveCenter

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

/-- The joint coefficient is strictly negative when the reflected slope is below `2 + 3/p`. -/
theorem compactMixedT_strictAnti_of_slope {p : ℕ} (hp : 0 < p) {u v : ℝ}
    (hu : 0 < u) (hb : reflectedHalfLogSlope (compositionMoment p 0) v < 2 + 3 / (p : ℝ)) :
    StrictAnti (compactMixedT p u v) := by
  have hk : 0 < gapFactor p u := div_pos (gapRate_pos hp)
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos (gapRate_pos hp) hu])))
  have ha := reflectedHalfLogSlope_nonneg hp hu
  have hγ : 0 < 1 + gapFactor p u + reflectedHalfLogSlope (compositionMoment p 0) u := by
    linarith
  have hc : 0 < 2 + gapRate p - reflectedHalfLogSlope (compositionMoment p 0) v :=
    sub_pos.mpr hb
  intro Z₁ Z₂ hZ
  dsimp only [compactMixedT]
  linarith only [mul_lt_mul_of_neg_left hZ (mul_neg_of_neg_of_pos (neg_neg_of_pos hγ) hc)]

/-- The affine dependence on the joint moment is strictly decreasing for `1 ≤ v`. -/
theorem compactMixedT_strictAnti {p : ℕ} (hp : 0 < p) {u v : ℝ}
    (hu : 0 < u) (hv : 1 ≤ v) : StrictAnti (compactMixedT p u v) := by
  have hvpos : 0 < v := zero_lt_one.trans_le hv
  have hb' : 2 / v ≤ 2 := (div_le_iff₀ hvpos).mpr (by linarith)
  have hb : reflectedHalfLogSlope (compositionMoment p 0) v ≤ 3 / 2 := by
    unfold reflectedHalfLogSlope
    linarith [upperTail_marginal_logDeriv hp hvpos]
  exact compactMixedT_strictAnti_of_slope hp hu (by
    have hh : (0 : ℝ) < 3 / (p : ℝ) := gapRate_pos hp
    linarith)

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
