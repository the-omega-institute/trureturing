/- GID: D5/S3/Quantum/Analysis/RefinedBMVPositiveCenterLeftStripKernel
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cancellation of the exact positive-center numerator on the separated left strip. -/

import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterLeftStripWeightedTail

open Filter
open scoped Topology

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

private theorem contDiffAt_partialLeft {f : ℝ → ℝ → ℝ} {x y : ℝ} {n m : WithTop ℕ∞}
    (hf : ContDiffAt ℝ n (Function.uncurry f) (x,y)) (hn : n ≠ 0)
    (hfin : n ≠ (↑(⊤ : ℕ∞) : WithTop ℕ∞)) (hm : m+1 ≤ n) :
    ContDiffAt ℝ m (Function.uncurry (fun a v ↦ deriv (f · v) a)) (x,y) := by
  have hd := (hf.fderiv_right hm).clm_apply
    (contDiffAt_const : ContDiffAt ℝ m (fun _ : ℝ × ℝ ↦ ((1,0) : ℝ × ℝ)) (x,y))
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [hf.eventually hfin] with z hz
  rcases z with ⟨a,v⟩
  have hline : HasDerivAt (fun t : ℝ ↦ (t,v)) (1,0) a := by
    simpa only [id_eq] using (hasDerivAt_id a).prodMk (hasDerivAt_const a v)
  exact ((hz.differentiableAt hn).hasFDerivAt.comp_hasDerivAt a hline).deriv

private def weightedThird (f : ℝ → ℝ → ℝ) (a v γ : ℝ) : ℝ :=
  deriv (fun y ↦ deriv (deriv (f · y)) a) v - γ*deriv (deriv (f · v)) a

private theorem weightedThird_add {f g : ℝ → ℝ → ℝ} {a v γ : ℝ}
    (hf : ContDiffAt ℝ 3 (Function.uncurry f) (a,v))
    (hg : ContDiffAt ℝ 3 (Function.uncurry g) (a,v)) :
    weightedThird (fun x y ↦ f x y+g x y) a v γ =
      weightedThird f a v γ+weightedThird g a v γ := by
  have hl {j : ℝ → ℝ → ℝ} {y : ℝ} (h : ContDiffAt ℝ 3 (Function.uncurry j) (a,y)) :
      ContDiffAt ℝ 3 (j · y) a :=
    h.comp a (contDiffAt_id.prodMk contDiffAt_const)
  have hsecond {y : ℝ} (hf' : ContDiffAt ℝ 3 (Function.uncurry f) (a,y))
      (hg' : ContDiffAt ℝ 3 (Function.uncurry g) (a,y)) :
      deriv (deriv (fun x ↦ f x y+g x y)) a =
        deriv (deriv (f · y)) a+deriv (deriv (g · y)) a := by
    have h₁ : deriv (fun x ↦ f x y+g x y) =ᶠ[𝓝 a] fun x ↦ deriv (f · y) x+deriv (g · y) x := by
      filter_upwards [(hl hf').eventually (by norm_num), (hl hg').eventually (by norm_num)] with x hx hy
      exact deriv_fun_add (hx.differentiableAt (by decide)) (hy.differentiableAt (by decide))
    have hLf : ContDiffAt ℝ 2 (deriv (f · y)) a := (hl hf').derivWithin (by norm_num)
    have hLg : ContDiffAt ℝ 2 (deriv (g · y)) a := (hl hg').derivWithin (by norm_num)
    exact h₁.deriv_eq.trans
      (deriv_fun_add (hLf.differentiableAt (by decide)) (hLg.differentiableAt (by decide)))
  have heq : (fun y ↦ deriv (deriv (fun x ↦ f x y+g x y)) a) =ᶠ[𝓝 v]
      fun y ↦ deriv (deriv (f · y)) a+deriv (deriv (g · y)) a := by
    have hline : ContinuousAt (fun y : ℝ ↦ (a,y)) v := by fun_prop
    filter_upwards [hline.tendsto.eventually (hf.eventually (by norm_num)),
        hline.tendsto.eventually (hg.eventually (by norm_num))] with y hy hz
    exact hsecond hy hz
  have hr {j : ℝ → ℝ → ℝ} (h : ContDiffAt ℝ 3 (Function.uncurry j) (a,v)) :
      DifferentiableAt ℝ (fun y ↦ deriv (deriv (j · y)) a) v := by
    have h₁ := contDiffAt_partialLeft h (by decide) (by decide)
      (show (2 : WithTop ℕ∞)+1 ≤ 3 by decide)
    have h₂ := contDiffAt_partialLeft h₁ (by decide) (by decide)
      (show (1 : WithTop ℕ∞)+1 ≤ 2 by decide)
    exact (h₂.comp v (contDiffAt_const.prodMk contDiffAt_id :
      ContDiffAt ℝ 1 (fun y : ℝ ↦ (a,y)) v)).differentiableAt (by decide)
  rw [weightedThird, heq.deriv_eq, deriv_fun_add (hr hf) (hr hg), hsecond hf hg]
  unfold weightedThird
  ring

/-- The weighted third derivative of the exact numerator is negative on
the separated left strip. Only the two logarithmic slope bounds enter. -/
theorem leftStrip_numerator_weighted_mixed_lt {p : ℕ} (hp : 11 ≤ p)
    {a v γ : ℝ} (ha : 0 < a) (hamax : a ≤ 1/2) (hgap : 6 < v-a)
    (hγ : 5/12 ≤ γ) (hγmax : γ ≤ 1) :
    let N (x y : ℝ) := compositionMoment p x y -
      Real.sqrt (compositionMoment p 0 y*compositionMoment p 0 (y-x))
    deriv (fun y ↦ deriv (deriv (N · y)) a) v -
      γ*deriv (deriv (N · v)) a < -7/450 := by
  let h := 3/(p : ℝ)
  let G := leftStripGeometricTerm h
  let B := leftStripRadicalTerm h
  let T := leftStripTailTerm p
  let N (x y : ℝ) := compositionMoment p x y -
    Real.sqrt (compositionMoment p 0 y*compositionMoment p 0 (y-x))
  let s := v-a
  let F := upperTailGap h
  let L := logReciprocalGap h
  let w := leftStripWeight h
  let X (t : ℝ) := 1-upperTailLambda h t
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hh : 0 < h := by dsimp [h]; positivity
  have hhmax : h ≤ 3/11 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by exact_mod_cast hp)
  have hs : 0 < s := by linarith
  have hsv : s ≤ v := sub_le_self v ha.le
  have hv : 0 < v := hs.trans_le hsv
  have hf₁ : ContDiffAt ℝ 3 (fun z : ℝ × ℝ ↦ F z.2) (a,v) := by
    unfold F upperTailGap
    fun_prop
  have hf₂ : ContDiffAt ℝ 3 (fun z : ℝ × ℝ ↦ F (z.2-z.1)) (a,v) := by
    unfold F upperTailGap
    fun_prop
  have hL₁ : ContDiffAt ℝ 3 (fun z : ℝ × ℝ ↦ L z.2) (a,v) :=
    contDiffAt_snd.sub (hf₁.log (tail_gap_pos hh hv).ne')
  have hL₂ : ContDiffAt ℝ 3 (fun z : ℝ × ℝ ↦ L (z.2-z.1)) (a,v) :=
    (contDiffAt_snd.sub contDiffAt_fst).sub (hf₂.log (tail_gap_pos hh hs).ne')
  have hG : ContDiffAt ℝ 3 (Function.uncurry G) (a,v) :=
    ((hL₁.sub hL₂).cosh).sub contDiffAt_const
  have hw : ContDiffAt ℝ 3 (Function.uncurry w) (a,v) :=
    ((hL₁.add hL₂).exp).div_const ((3+h)*(3+2*h)/2)
  have hXs (t : ℝ) (ht : 6 ≤ t) : 0 < X t :=
    Real.sqrt_pos.mp ((by norm_num : (0 : ℝ) < 999/1000).trans_le
      (separated_radical_lower hh hhmax ht).2)
  have hx₁ : ContDiffAt ℝ 3 (fun z : ℝ × ℝ ↦ X z.2) (a,v) := by
    unfold X upperTailLambda upperTailGap
    fun_prop
  have hx₂ : ContDiffAt ℝ 3 (fun z : ℝ × ℝ ↦ X (z.2-z.1)) (a,v) := by
    unfold X upperTailLambda upperTailGap
    fun_prop
  have hb₁ := hx₁.sqrt (hXs v (hgap.le.trans hsv)).ne'
  have hb₂ := hx₂.sqrt (hXs s hgap.le).ne'
  have hB : ContDiffAt ℝ 3 (Function.uncurry B) (a,v) :=
    (hw.mul ((hb₁.sub hb₂).pow 2)).div_const 2
  have hT : ContDiffAt ℝ 3 (Function.uncurry T) (a,v) :=
    hw.mul (leftStripTailResidual_smooth p).contDiffAt
  have hleft : ∀ᶠ z : ℝ × ℝ in 𝓝 (a,v), 0 < z.1 :=
    continuousAt_fst.eventually (eventually_gt_nhds ha)
  have hsep : ∀ᶠ z : ℝ × ℝ in 𝓝 (a,v), 6 < z.2-z.1 :=
    (continuousAt_snd.sub continuousAt_fst).eventually (eventually_gt_nhds hgap)
  have hLocal : ∀ᶠ z : ℝ × ℝ in (𝓝 a) ×ˢ (𝓝 v),
      N z.1 z.2 = G z.1 z.2+B z.1 z.2+T z.1 z.2 := by
    rw [← nhds_prod_eq]
    filter_upwards [hleft,hsep] with z hz hd
    exact leftStrip_numerator_decomposition hp hz hd.le
  obtain ⟨P,hP,Q,hQ,hPQ⟩ := eventually_prod_iff.mp hLocal
  have hsec : (fun y ↦ deriv (deriv (N · y)) a) =ᶠ[𝓝 v]
      fun y ↦ deriv (deriv (fun x ↦ G x y+B x y+T x y)) a := by
    filter_upwards [hQ] with y hy
    have heq : (N · y) =ᶠ[𝓝 a] fun x ↦ G x y+B x y+T x y :=
      hP.mono fun _ hx ↦ hPQ hx hy
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using heq.iteratedDeriv_eq 2
  have heq :
      weightedThird N a v γ = weightedThird (fun x y ↦ G x y+B x y+T x y) a v γ := by
    unfold weightedThird
    rw [hsec.deriv_eq,hsec.eq_of_nhds]
  have hmain : weightedThird G a v γ < -1/5 :=
    leftStrip_geometric_mixed_lt hh hhmax ha.le hamax hgap.le hγ hγmax
  have hrad : |weightedThird B a v γ| < 47/450 :=
    leftStrip_radical_mixed_lt hh hhmax ha.le hamax hgap.le (by linarith) hγmax
  have htail : |weightedThird T a v γ| < 2/25 :=
    leftStrip_tail_mixed_lt hp ha.le hamax hgap.le (by linarith) hγmax
  have hGB : ContDiffAt ℝ 3 (Function.uncurry (fun x y ↦ G x y+B x y)) (a,v) :=
    hG.add hB
  change weightedThird N a v γ < _
  rw [heq, weightedThird_add hGB hT, weightedThird_add hG hB]
  linarith only [hmain, (abs_lt.mp hrad).2, (abs_lt.mp htail).2]

#print axioms leftStrip_numerator_decomposition
#print axioms leftStrip_numerator_weighted_mixed_lt

end RefinedBMV.PositiveCenter
