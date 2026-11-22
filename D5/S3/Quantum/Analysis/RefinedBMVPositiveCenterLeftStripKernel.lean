/- GID: D5/S3/Quantum/Analysis/RefinedBMVPositiveCenterLeftStripKernel
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cancellation of the exact positive-center numerator on the separated left strip. -/

import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterLeftStripWeightedTail
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterLeftStripMarginal

/-! # The mixed kernel sign on the separated left strip -/

open Filter Set
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

private theorem compositionMoment_smooth (p : ℕ) :
    ContDiff ℝ 3 (Function.uncurry (compositionMoment p)) := by
  have hsum (l : List (ℕ × ℕ × ℕ)) (c d : (ℕ × ℕ × ℕ) → ℝ) :
      ContDiff ℝ 3 (fun z : ℝ × ℝ ↦
        (l.map fun g ↦ Real.exp (c g*z.1+d g*z.2)).sum) := by
    induction l with
    | nil => simpa using (contDiff_const : ContDiff ℝ 3 (fun _ : ℝ × ℝ ↦ (0 : ℝ)))
    | cons j l ih =>
      have he : ContDiff ℝ 3 (fun z : ℝ × ℝ ↦ Real.exp (c j*z.1+d j*z.2)) := by fun_prop
      simpa only [List.map_cons, List.sum_cons] using he.add ih
  change ContDiff ℝ 3 (fun z : ℝ × ℝ ↦ compositionMoment p z.1 z.2)
  unfold compositionMoment
  exact ((hsum _ _ _).div_const _).sub contDiff_const

private theorem ratio_derivative_neg {f D : ℝ → ℝ} {u k : ℝ}
    (hu : 0 < u) (hD : 0 < D u) (hk : 0 < k)
    (hf : ∀ x ∈ Icc 0 u, DifferentiableAt ℝ f x)
    (hf' : ContinuousOn (deriv f) (Icc 0 u))
    (hf'' : ∀ x ∈ Ioo 0 u, deriv (deriv f) x < 0)
    (hf₀ : f 0 = 0) (hf₁ : deriv f 0 = 0)
    (hD' : DifferentiableAt ℝ D u) (hslope : u*deriv D u ≤ D u) :
    deriv (fun x ↦ f x/(D x*k)) u < 0 := by
  have hAnti : StrictAntiOn (deriv f) (Icc 0 u) :=
    strictAntiOn_of_deriv_neg (convex_Icc _ _) hf' (by
      rw [interior_Icc]
      exact hf'')
  obtain ⟨t,ht,hm⟩ := exists_hasDerivAt_eq_slope f (deriv f) hu
    (fun x hx ↦ (hf x hx).continuousAt.continuousWithinAt)
    (fun x hx ↦ (hf x ⟨hx.1.le,hx.2.le⟩).hasDerivAt)
  have ht' : t ∈ Icc 0 u := ⟨ht.1.le,ht.2.le⟩
  have h₀ := hAnti (left_mem_Icc.mpr hu.le) ht' ht.1
  have h₁ := hAnti ht' (right_mem_Icc.mpr hu.le) ht.2
  rw [hf₁] at h₀
  rw [hf₀, sub_zero, sub_zero] at hm
  have hEq := (eq_div_iff hu.ne').mp hm
  have hfu : f u ≤ 0 := by nlinarith only [hEq, mul_nonpos_of_nonpos_of_nonneg h₀.le hu.le]
  have hsec : deriv f u*u < f u := (mul_lt_mul_of_pos_right h₁ hu).trans_eq hEq
  have hsec' := mul_lt_mul_of_pos_right hsec hD
  have hslope' := mul_le_mul_of_nonpos_left hslope hfu
  have hnum : deriv f u*D u-f u*deriv D u < 0 := by
    by_contra! hn
    have hm := mul_nonneg hu.le hn
    nlinarith only [hsec',hslope',hm]
  have hd := (hf u (right_mem_Icc.mpr hu.le)).hasDerivAt.fun_div
    (hD'.hasDerivAt.mul_const k) (mul_pos hD hk).ne'
  rw [hd.deriv]
  apply div_neg_of_neg_of_pos _ (sq_pos_of_pos (mul_pos hD hk))
  nlinarith only [mul_neg_of_neg_of_pos hnum hk]

/-- A strictly negative weighted numerator on the whole integration interval
transfers to the mixed derivative of the original kernel. -/
private theorem leftStrip_logKernel_mixed_lt_of_weighted {p : ℕ} (hp : 0 < p) {u v : ℝ}
    (hu : 0 < u) (huv : u < v)
    (hsmall : u*deriv (fun t ↦ Real.sqrt (compositionMoment p 0 (-t))) u ≤
      Real.sqrt (compositionMoment p 0 (-u)))
    (hweighted :
      let D (t : ℝ) := Real.sqrt (compositionMoment p 0 (-t))
      let N (x y : ℝ) := compositionMoment p x y -
        Real.sqrt (compositionMoment p 0 y*compositionMoment p 0 (y-x))
      ∀ a ∈ Ioo 0 u, weightedThird N a v (deriv D v/D v) < 0) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  let C := compositionMoment p
  let D (t : ℝ) := Real.sqrt (C 0 (-t))
  let N (x y : ℝ) := C x y-Real.sqrt (C 0 y*C 0 (y-x))
  let P (x y : ℝ) := deriv (N · y) x
  let R (x y : ℝ) := deriv (N x) y
  let γ := deriv D v/D v
  let f (x : ℝ) := R x v-γ*N x v
  have hp₀ := hp
  have hv : 0 < v := hu.trans huv
  have hC : ContDiff ℝ 3 (Function.uncurry C) := compositionMoment_smooth p
  have hPos (t : ℝ) (ht : 0 < t) : 0 < D t :=
    Real.sqrt_pos.mpr (compositionMoment_marginal_pos hp₀ (neg_ne_zero.mpr ht.ne'))
  have hD (t : ℝ) (ht : 0 < t) : ContDiffAt ℝ 3 D t := by
    have hM := hC.comp (contDiff_const.prodMk contDiff_id.neg :
      ContDiff ℝ 3 (fun y : ℝ ↦ ((0 : ℝ),-y)))
    exact hM.contDiffAt.sqrt
      (compositionMoment_marginal_pos hp₀ (neg_ne_zero.mpr ht.ne')).ne'
  have hN {x y : ℝ} (hy : 0 < y) (hxy : x < y) :
      ContDiffAt ℝ 3 (Function.uncurry N) (x,y) := by
    have hM₁ := hC.comp (contDiff_const.prodMk contDiff_snd :
      ContDiff ℝ 3 (fun z : ℝ × ℝ ↦ ((0 : ℝ),z.2)))
    have hM₂ := hC.comp (contDiff_const.prodMk (contDiff_snd.sub contDiff_fst) :
      ContDiff ℝ 3 (fun z : ℝ × ℝ ↦ ((0 : ℝ),z.2-z.1)))
    exact hC.contDiffAt.sub ((hM₁.mul hM₂).contDiffAt.sqrt
      (mul_ne_zero (compositionMoment_marginal_pos hp₀ hy.ne').ne'
        (compositionMoment_marginal_pos hp₀ (sub_pos.mpr hxy).ne').ne'))
  have hN₂ {x y : ℝ} (hy : 0 < y) (hxy : x < y) :
      ContDiffAt ℝ 2 (Function.uncurry N) (x,y) := (hN hy hxy).of_le (by decide)
  have hP {x y : ℝ} (hy : 0 < y) (hxy : x < y) :
      ContDiffAt ℝ 2 (Function.uncurry P) (x,y) :=
    contDiffAt_partialLeft (hN hy hxy) (by decide) (by decide) (by norm_num)
  have hLeft {j : ℝ → ℝ → ℝ} {n : WithTop ℕ∞} {x y : ℝ}
      (hj : ContDiffAt ℝ n (Function.uncurry j) (x,y)) (hn : n ≠ 0) :
      HasDerivAt (j · y) (deriv (j · y) x) x := by
    have hline : ContDiffAt ℝ n (fun t : ℝ ↦ (t,y)) x := contDiffAt_id.prodMk contDiffAt_const
    exact ((hj.comp x hline).differentiableAt hn).hasDerivAt
  have hRight {j : ℝ → ℝ → ℝ} {n : WithTop ℕ∞} {x y : ℝ}
      (hj : ContDiffAt ℝ n (Function.uncurry j) (x,y)) (hn : n ≠ 0) :
      HasDerivAt (j x) (deriv (j x) y) y := by
    have hline : ContDiffAt ℝ n (fun t : ℝ ↦ (x,t)) y := contDiffAt_const.prodMk contDiffAt_id
    exact ((hj.comp y hline).differentiableAt hn).hasDerivAt
  have hf (x : ℝ) (hx : x < v) : HasDerivAt f (deriv (P x) v-γ*P x v) x := by
    have hm := Extreme.hasDerivAt_deriv_second (hN₂ hv hx)
    have hm' := hm.congr_deriv (hm.deriv.symm.trans (mixed_partial_eq (hN₂ hv hx)))
    exact hm'.sub ((hLeft (hN hv hx) (by decide)).const_mul γ)
  have hf' (x : ℝ) (hx : x < v) : HasDerivAt (deriv f) (weightedThird N x v γ) x := by
    have heq : deriv f =ᶠ[𝓝 x] fun t ↦ deriv (P t) v-γ*P t v := by
      filter_upwards [eventually_lt_nhds hx] with t ht using (hf t ht).deriv
    have hm := Extreme.hasDerivAt_deriv_second (hP hv hx)
    have hm' := hm.congr_deriv (hm.deriv.symm.trans (mixed_partial_eq (hP hv hx)))
    exact (hm'.sub ((hLeft (hP hv hx) (by decide)).const_mul γ)).congr_of_eventuallyEq heq
  have hN₀ : N 0 =ᶠ[𝓝 v] fun _ ↦ 0 := by
    filter_upwards [eventually_gt_nhds hv] with y hy
    simpa only [N,C,sub_zero] using logKernel_numerator_zero hp₀ hy
  have hP₀ : P 0 =ᶠ[𝓝 v] fun _ ↦ 0 := by
    filter_upwards [eventually_gt_nhds hv] with y hy
    exact (hasDerivAt_logKernel_numerator_zero hp₀ hy).deriv
  have hf₀ : f 0 = 0 := by
    change deriv (N 0) v-γ*N 0 v = 0
    rw [hN₀.deriv_eq,hN₀.eq_of_nhds,deriv_const,mul_zero,sub_zero]
  have hf₁ : deriv f 0 = 0 := by
    rw [(hf 0 hv).deriv,hP₀.deriv_eq,hP₀.eq_of_nhds,deriv_const,mul_zero,sub_zero]
  have hf'' (x : ℝ) (hx : x ∈ Ioo 0 u) : deriv (deriv f) x < 0 := by
    rw [(hf' x (hx.2.trans huv)).deriv]
    exact hweighted x hx
  have hRatio := ratio_derivative_neg hu (hPos u hu) (hPos v hv)
    (fun x hx ↦ (hf x (hx.2.trans_lt huv)).differentiableAt)
    (fun x hx ↦ (hf' x (hx.2.trans_lt huv)).continuousAt.continuousWithinAt)
    hf'' hf₀ hf₁ ((hD u hu).differentiableAt (by decide)) hsmall
  have hK (x y : ℝ) (hx : 0 < x) : logKernel p x y = N x y/(D x*D y) := by
    unfold logKernel
    rw [Real.sqrt_mul (compositionMoment_marginal_pos hp₀ (neg_ne_zero.mpr hx.ne')).le]
  have hKv (x : ℝ) (hx : 0 < x) (hxv : x < v) :
      deriv (logKernel p x) v = f x/(D x*D v) := by
    rw [show logKernel p x = fun y ↦ N x y/(D x*D y) from funext fun y ↦ hK x y hx]
    have hd := (hRight (hN hv hxv) (by decide)).fun_div
      (((hD v hv).differentiableAt (by decide)).hasDerivAt.const_mul (D x))
      (mul_pos (hPos x hx) (hPos v hv)).ne'
    rw [hd.deriv]
    change _ = (deriv (N x) v-(deriv D v/D v)*N x v)/(D x*D v)
    field_simp [(hPos x hx).ne', (hPos v hv).ne'] <;> ring
  have hnear : (fun x ↦ deriv (logKernel p x) v) =ᶠ[𝓝 u] fun x ↦ f x/(D x*D v) := by
    filter_upwards [eventually_gt_nhds hu,eventually_lt_nhds huv] with x hx hxv using hKv x hx hxv
  have hK₂ : ContDiffAt ℝ 2 (Function.uncurry (logKernel p)) (u,v) := by
    have hDu := (hD u hu).comp (u,v) contDiffAt_fst
    have hDv := (hD v hv).comp (u,v) contDiffAt_snd
    have hs := (hN hv huv).div (hDu.mul hDv) (mul_pos (hPos u hu) (hPos v hv)).ne'
    apply (hs.of_le (show (2 : WithTop ℕ∞) ≤ 3 by decide)).congr_of_eventuallyEq
    filter_upwards [continuousAt_fst.eventually (eventually_gt_nhds hu)] with z hz
    exact hK z.1 z.2 hz
  rw [← mixed_partial_eq hK₂, hnear.deriv_eq]
  exact hRatio

/-- The separated-strip slope estimates supply the weighted numerator hypothesis. -/
theorem leftStrip_logKernel_mixed_lt_of_slopes {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu : 0 < u) (humax : u ≤ 1/2) (hgap : 6 < v-u)
    (hsmall : u*deriv (fun t ↦ Real.sqrt (compositionMoment p 0 (-t))) u ≤
      Real.sqrt (compositionMoment p 0 (-u)))
    (hγ : 5/12 ≤ deriv (fun t ↦ Real.sqrt (compositionMoment p 0 (-t))) v /
      Real.sqrt (compositionMoment p 0 (-v)))
    (hγmax : deriv (fun t ↦ Real.sqrt (compositionMoment p 0 (-t))) v /
      Real.sqrt (compositionMoment p 0 (-v)) ≤ 1) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  refine leftStrip_logKernel_mixed_lt_of_weighted (by omega) hu (by linarith) hsmall ?_
  dsimp only
  intro a ha
  exact (leftStrip_numerator_weighted_mixed_lt hp ha.1 (ha.2.le.trans humax)
    (hgap.trans_le (sub_le_sub_left ha.2.le _)) hγ hγmax).trans (by norm_num)

private theorem leftStrip_small_slope {p : ℕ} (hp : 11 ≤ p) {u : ℝ}
    (hu : 0 < u) (humax : u ≤ 1/2) :
    u * deriv (fun t ↦ Real.sqrt (compositionMoment p 0 (-t))) u ≤
      Real.sqrt (compositionMoment p 0 (-u)) := by
  let M (t : ℝ) := compositionMoment p 0 (-t)
  let D (t : ℝ) := Real.sqrt (M t)
  have hp₀ : 0 < p := by omega
  have hMpos (t : ℝ) (ht : 0 < t) : 0 < M t :=
    compositionMoment_marginal_pos hp₀ (neg_ne_zero.mpr ht.ne')
  have hMs : ContDiff ℝ 3 M :=
    (compositionMoment_smooth p).comp (contDiff_const.prodMk contDiff_id.neg :
      ContDiff ℝ 3 (fun t : ℝ ↦ ((0 : ℝ),-t)))
  have hM (t : ℝ) : HasDerivAt M (deriv M t) t := (hMs.differentiable (by decide) t).hasDerivAt
  have hD (t : ℝ) (ht : 0 < t) : HasDerivAt D (deriv M t/(2*D t)) t :=
    (hM t).sqrt (hMpos t ht).ne'
  have hDpos (t : ℝ) (ht : 0 < t) : 0 < D t := Real.sqrt_pos.mpr (hMpos t ht)
  have hDsq (t : ℝ) (ht : 0 < t) : D t^2 = M t := Real.sq_sqrt (hMpos t ht).le
  have hreg := (SmallCorner.hasDerivAt_G p (c := 1) one_ne_zero
    (neg_ne_zero.mpr hu.ne')).comp u (hasDerivAt_id' u).neg
  change HasDerivAt (fun t ↦ compositionMoment p 0 (-t)/(1*(-t)^2))
    (SmallCorner.GPrime p 1 (-u)*(-1)) u at hreg
  have hreg' : HasDerivAt (fun t ↦ M t/t^2) (-SmallCorner.GPrime p 1 (-u)) u := by
    simpa only [M, one_mul, neg_sq, mul_neg, mul_one] using hreg
  have hd := (hM u).fun_div (hasDerivAt_pow 2 u) (pow_ne_zero 2 hu.ne')
  have hcmp := hd.deriv.symm.trans hreg'.deriv
  have hnonpos : (deriv M u*u^2-M u*(↑(2 : ℕ)*u^(2-1)))/(u^2)^2 ≤ 0 := by
    rw [hcmp]
    exact neg_nonpos.mpr (leftStrip_GPrime_nonneg hp hu humax)
  have hcross := (div_le_iff₀ (sq_pos_of_ne_zero (pow_ne_zero 2 hu.ne'))).mp hnonpos
  norm_num at hcross
  have hbound : u*deriv M u ≤ 2*M u := by
    by_contra! hbad
    have hm := mul_pos hu (sub_pos.mpr hbad)
    nlinarith only [hcross,hm]
  rw [(hD u hu).deriv, ← mul_div_assoc,
    div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) (hDpos u hu))]
  nlinarith only [hbound,hDsq u hu]

/-- The original refined BMV kernel has strictly negative mixed derivative
throughout the separated left strip for every degree at least eleven. -/
theorem leftStrip_logKernel_mixed_lt {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu : 0 < u) (humax : u ≤ 1/2) (hgap : 6 < v-u) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  let M (t : ℝ) := compositionMoment p 0 (-t)
  let D (t : ℝ) := Real.sqrt (M t)
  have hp₀ : 0 < p := by omega
  have hv : 6 ≤ v := by linarith
  have hv₀ : 0 < v := by linarith
  have hMpos (t : ℝ) (ht : 0 < t) : 0 < M t :=
    compositionMoment_marginal_pos hp₀ (neg_ne_zero.mpr ht.ne')
  have hMs : ContDiff ℝ 3 M :=
    (compositionMoment_smooth p).comp (contDiff_const.prodMk contDiff_id.neg :
      ContDiff ℝ 3 (fun t : ℝ ↦ ((0 : ℝ),-t)))
  have hM (t : ℝ) : HasDerivAt M (deriv M t) t := (hMs.differentiable (by decide) t).hasDerivAt
  have hD (t : ℝ) (ht : 0 < t) : HasDerivAt D (deriv M t/(2*D t)) t :=
    (hM t).sqrt (hMpos t ht).ne'
  have hDpos (t : ℝ) (ht : 0 < t) : 0 < D t := Real.sqrt_pos.mpr (hMpos t ht)
  have hDsq (t : ℝ) (ht : 0 < t) : D t^2 = M t := Real.sq_sqrt (hMpos t ht).le
  have hγ : deriv D v/D v = (deriv M v/M v)/2 := by
    rw [(hD v hv₀).deriv, div_div, div_div]
    congr 1
    nlinarith only [hDsq v hv₀]
  have hlo := negativeMarginal_logDeriv_ge hp₀ hv
  have hhi := negativeMarginal_logDeriv_le hp₀ (by linarith : 2 ≤ v)
  change 5/6 ≤ deriv M v/M v at hlo
  change deriv M v/M v ≤ 2 at hhi
  exact leftStrip_logKernel_mixed_lt_of_slopes hp hu humax hgap
    (leftStrip_small_slope hp hu humax)
    (by rw [hγ]; linarith only [hlo]) (by rw [hγ]; linarith only [hhi])

private abbrev leftStripS (p : ℕ) (t : ℝ) := Real.sqrt (compositionMoment p 0 t)

private abbrev leftStripGap := ℕ × ℕ × ℕ

private def leftStripX (p : ℕ) (g : leftStripGap) : ℝ := 3 * (g.2.1 : ℝ) / p - 1

private def leftStripY (p : ℕ) (g : leftStripGap) : ℝ := 3 * (g.2.2 : ℝ) / p - 1

/-- The tilted joint moment with polynomial weight `X^i Y^j` under the
uniform law on the degree-`p` compositions. -/
def leftStripExpMoment (p i j : ℕ) (a v : ℝ) : ℝ :=
  ((DimThree.gaps p).map fun g ↦ leftStripX p g ^ i * leftStripY p g ^ j *
    Real.exp (leftStripX p g * a + leftStripY p g * v)).sum / (DimThree.gaps p).length

private theorem leftStrip_hasDerivAt_exp_sum (l : List leftStripGap) (w A B : leftStripGap → ℝ)
    (t : ℝ) :
    HasDerivAt (fun x ↦ (l.map fun g ↦ w g * Real.exp (A g * x + B g)).sum)
      (l.map fun g ↦ (w g * A g) * Real.exp (A g * t + B g)).sum t := by
  induction l with
  | nil => simpa using hasDerivAt_const t (0 : ℝ)
  | cons g l ih =>
    have hg : HasDerivAt (fun x ↦ w g * Real.exp (A g * x + B g))
        ((w g * A g) * Real.exp (A g * t + B g)) t := by
      convert (((hasDerivAt_const_mul (A g)).add_const (B g)).exp.const_mul (w g)) using 1
      ring
    exact hg.add ih

private theorem leftStrip_hasDerivAt_expMoment_left (p i j : ℕ) (a v : ℝ) :
    HasDerivAt (leftStripExpMoment p i j · v) (leftStripExpMoment p (i+1) j a v) a := by
  have h := (leftStrip_hasDerivAt_exp_sum (DimThree.gaps p)
    (fun g ↦ leftStripX p g ^ i * leftStripY p g ^ j) (leftStripX p)
    (fun g ↦ leftStripY p g * v) a).div_const ((DimThree.gaps p).length : ℝ)
  simpa only [leftStripExpMoment, pow_succ, mul_right_comm] using h

private theorem leftStrip_hasDerivAt_expMoment_right (p i j : ℕ) (a v : ℝ) :
    HasDerivAt (leftStripExpMoment p i j a) (leftStripExpMoment p i (j+1) a v) v := by
  have h := (leftStrip_hasDerivAt_exp_sum (DimThree.gaps p)
    (fun g ↦ leftStripX p g ^ i * leftStripY p g ^ j) (leftStripY p)
    (fun g ↦ leftStripX p g * a) v).div_const ((DimThree.gaps p).length : ℝ)
  unfold leftStripExpMoment
  simpa only [pow_succ, mul_assoc, add_comm] using h

private theorem leftStrip_hasDerivAt_moment_left (p : ℕ) (a v : ℝ) :
    HasDerivAt (compositionMoment p · v) (leftStripExpMoment p 1 0 a v) a := by
  have h : ∀ t : ℝ, compositionMoment p t v = leftStripExpMoment p 0 0 t v - 1 := by
    intro t
    simp only [compositionMoment, leftStripExpMoment, pow_zero, mul_one, one_mul]
    rfl
  exact ((leftStrip_hasDerivAt_expMoment_left p 0 0 a v).sub_const 1).congr_of_eventuallyEq
    (Eventually.of_forall h)

/-- The second partial of the exact kernel numerator in its first coordinate. -/
def leftStripE (p : ℕ) (a v : ℝ) : ℝ :=
  leftStripExpMoment p 2 0 a v - leftStripS p v * deriv (deriv (leftStripS p)) (v-a)

private theorem leftStrip_contDiffAt_S {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : t ≠ 0) :
    ContDiffAt ℝ 3 (leftStripS p) t := by
  have h := (compositionMoment_smooth p).comp
    (contDiff_const.prodMk contDiff_id : ContDiff ℝ 3 (fun t : ℝ ↦ ((0 : ℝ), t)))
  exact h.contDiffAt.sqrt (compositionMoment_marginal_pos hp ht).ne'

private theorem leftStrip_numerator_second_eq_E {p : ℕ} (hp : 0 < p) {a v : ℝ}
    (hv : 0 < v) (hav : a < v) :
    let N (x y : ℝ) := compositionMoment p x y -
      Real.sqrt (compositionMoment p 0 y * compositionMoment p 0 (y-x))
    deriv (deriv (N · v)) a = leftStripE p a v := by
  let S := leftStripS p
  have hN : ∀ x : ℝ, compositionMoment p x v -
      Real.sqrt (compositionMoment p 0 v * compositionMoment p 0 (v-x)) =
      compositionMoment p x v - S v * S (v-x) := by
    intro x
    rw [Real.sqrt_mul (compositionMoment_marginal_pos hp hv.ne').le]
  have hgap (x : ℝ) : HasDerivAt (fun t : ℝ ↦ v-t) (-1) x :=
    (hasDerivAt_id' x).const_sub v
  have hfirst : (fun x ↦ deriv (fun t ↦ compositionMoment p t v -
      Real.sqrt (compositionMoment p 0 v * compositionMoment p 0 (v-t))) x)
      =ᶠ[𝓝 a] fun x ↦ leftStripExpMoment p 1 0 x v + S v * deriv S (v-x) := by
    filter_upwards [eventually_lt_nhds hav] with x hx
    have hs := ((leftStrip_contDiffAt_S hp (sub_pos.mpr hx).ne').differentiableAt
      (by decide)).hasDerivAt
    have hd := (leftStrip_hasDerivAt_moment_left p x v).sub
      ((hs.comp x (hgap x)).const_mul (S v))
    have he := (hd.congr_of_eventuallyEq (Eventually.of_forall hN)).deriv
    simpa only [mul_neg, mul_one, sub_neg_eq_add] using he
  change deriv (fun x ↦ deriv (fun t ↦ compositionMoment p t v -
    Real.sqrt (compositionMoment p 0 v * compositionMoment p 0 (v-t))) x) a = _
  rw [hfirst.deriv_eq]
  have hs := ((leftStrip_contDiffAt_S hp (sub_pos.mpr hav).ne').derivWithin
    (show (2 : WithTop ℕ∞)+1 ≤ 3 by decide)).differentiableAt (by decide)
  have hd := (leftStrip_hasDerivAt_expMoment_left p 1 0 a v).add
    ((hs.hasDerivAt.comp a (hgap a)).const_mul (S v))
  simpa only [leftStripE, Pi.add_def, Function.comp_apply, mul_neg, mul_one, sub_eq_add_neg]
    using hd.deriv

/-- The weighted third derivative uses the ordinary second-coordinate derivative of `E`
with `a` fixed. The weight `γ` is a scalar at the evaluation point. -/
theorem leftStrip_weightedThird_eq {p : ℕ} (hp : 0 < p) {a v γ : ℝ}
    (hv : 0 < v) (hav : a < v) :
    let N (x y : ℝ) := compositionMoment p x y -
      Real.sqrt (compositionMoment p 0 y * compositionMoment p 0 (y-x))
    deriv (fun y ↦ deriv (deriv (N · y)) a) v - γ * deriv (deriv (N · v)) a =
      deriv (leftStripE p a) v - γ * leftStripE p a v := by
  let N (x y : ℝ) := compositionMoment p x y -
    Real.sqrt (compositionMoment p 0 y * compositionMoment p 0 (y-x))
  have he : (fun y ↦ deriv (deriv (N · y)) a) =ᶠ[𝓝 v] leftStripE p a := by
    filter_upwards [eventually_gt_nhds hv, eventually_gt_nhds hav] with y hy hay
    exact leftStrip_numerator_second_eq_E hp hy hay
  change weightedThird N a v γ = _
  rw [weightedThird, he.deriv_eq, he.eq_of_nhds]

/-- The explicit derivative of `E` in its second coordinate. -/
theorem leftStrip_hasDerivAt_E_right {p : ℕ} (hp : 0 < p) {a v : ℝ}
    (hv : 0 < v) (hav : a < v) :
    let S (t : ℝ) := Real.sqrt (compositionMoment p 0 t)
    HasDerivAt (leftStripE p a)
      (leftStripExpMoment p 2 1 a v -
        (deriv S v * deriv (deriv S) (v-a) + S v * deriv (deriv (deriv S)) (v-a))) v := by
  let S := leftStripS p
  have hS := ((leftStrip_contDiffAt_S hp hv.ne').differentiableAt (by decide)).hasDerivAt
  have hS'' := ((leftStrip_contDiffAt_S hp (sub_pos.mpr hav).ne').derivWithin
    (show (2 : WithTop ℕ∞)+1 ≤ 3 by decide)).derivWithin
    (show (1 : WithTop ℕ∞)+1 ≤ 2 by decide)
  have hd := (hS''.differentiableAt (by decide)).hasDerivAt.comp v
    ((hasDerivAt_id' v).sub_const a)
  have hm := (leftStrip_hasDerivAt_expMoment_right p 2 0 a v).sub (hS.mul hd)
  change HasDerivAt (fun t ↦ leftStripExpMoment p 2 0 a t - S t * deriv (deriv S) (t-a)) _ v
  simpa only [Pi.sub_def, Pi.mul_def, Function.comp_apply, mul_one, add_comm] using hm

/-- The negative marginal's half-log slope, with the reflection included. -/
def leftStripReflectedSlope (p : ℕ) (v : ℝ) : ℝ :=
  deriv (fun t ↦ leftStripS p (-t)) v / leftStripS p (-v)

/-- The rescaled sign of the differentiated numerator used at the origin. -/
def leftStripScaledIntegrand (p : ℕ) (a v : ℝ) : ℝ :=
  v * (leftStripReflectedSlope p v * leftStripE p a v - deriv (leftStripE p a) v)

private abbrev leftStripVarianceHalf (p : ℕ) := compositionMarginalVariance p / 2

private abbrev leftStripZ (p k : ℕ) :=
  SmallCorner.integralMarginalDerivative p (leftStripVarianceHalf p) k

private theorem leftStrip_hasDerivAt_Z (p k : ℕ) (t : ℝ) :
    HasDerivAt (leftStripZ p k) (leftStripZ p (k + 1) t) t := by
  simpa only [SmallCorner.affineMarginalJet, zero_mul, zero_add, one_mul] using
    (SmallCorner.continuedMarginalJet_isAt p k 0 1 0 t).2.1

private theorem leftStrip_Z_eq_G {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : t ≠ 0) :
    leftStripZ p 0 t = SmallCorner.G p (leftStripVarianceHalf p) t := by
  simpa only [iteratedDeriv_zero] using
    (SmallCorner.iteratedDeriv_G_eq_integral hp
      (half_pos (compositionMarginalVariance_pos p)).ne' ht 0).symm

private theorem leftStrip_Z_pos {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : t ≠ 0) :
    0 < leftStripZ p 0 t := by
  rw [leftStrip_Z_eq_G hp ht]
  exact SmallCorner.G_pos hp (half_pos (compositionMarginalVariance_pos p)) ht

private def leftStripRoot (p : ℕ) (t : ℝ) : ℝ := Real.sqrt (leftStripZ p 0 t)

private def leftStripRootOne (p : ℕ) (t : ℝ) : ℝ :=
  leftStripZ p 1 t / (2 * leftStripRoot p t)

private def leftStripRootTwo (p : ℕ) (t : ℝ) : ℝ :=
  (leftStripZ p 2 t - 2 * leftStripRootOne p t ^ 2) / (2 * leftStripRoot p t)

private def leftStripRootThree (p : ℕ) (t : ℝ) : ℝ :=
  (leftStripZ p 3 t - 6 * leftStripRootOne p t * leftStripRootTwo p t) /
    (2 * leftStripRoot p t)

private theorem leftStrip_root_derivatives {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (leftStripRoot p) (leftStripRootOne p t) t ∧
    HasDerivAt (leftStripRootOne p) (leftStripRootTwo p t) t ∧
    HasDerivAt (leftStripRootTwo p) (leftStripRootThree p t) t := by
  have hr : 0 < leftStripRoot p t := Real.sqrt_pos.mpr (leftStrip_Z_pos hp ht)
  have hden := (mul_pos (by norm_num : (0 : ℝ) < 2) hr).ne'
  have h₁ : HasDerivAt (leftStripRoot p) (leftStripRootOne p t) t :=
    (leftStrip_hasDerivAt_Z p 0 t).sqrt (leftStrip_Z_pos hp ht).ne'
  have hn₁ := (div_mul_cancel₀ (leftStripZ p 1 t) hden).symm
  have h₂ : HasDerivAt (leftStripRootOne p) (leftStripRootTwo p t) t := by
    apply ((leftStrip_hasDerivAt_Z p 1 t).fun_div (h₁.const_mul 2) hden).congr_deriv
    change _ = (leftStripZ p 2 t - 2 * leftStripRootOne p t ^ 2) / (2 * leftStripRoot p t)
    rw [show leftStripZ p 1 t = leftStripRootOne p t * (2 * leftStripRoot p t) from hn₁]
    field_simp [hr.ne']
    <;> ring
  have hn₂ := (div_mul_cancel₀ (leftStripZ p 2 t - 2 * leftStripRootOne p t ^ 2) hden).symm
  refine ⟨h₁, h₂, ?_⟩
  apply (((leftStrip_hasDerivAt_Z p 2 t).sub ((h₂.pow 2).const_mul 2)).fun_div
    (h₁.const_mul 2) hden).congr_deriv
  change _ = (leftStripZ p 3 t - 6 * leftStripRootOne p t * leftStripRootTwo p t) /
    (2 * leftStripRoot p t)
  simp only [Pi.sub_apply, Pi.pow_apply]
  rw [show leftStripZ p 2 t - 2 * leftStripRootOne p t ^ 2 =
    leftStripRootTwo p t * (2 * leftStripRoot p t) from hn₂]
  field_simp [hr.ne']
  <;> ring

private theorem leftStrip_S_eq_root {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : t ≠ 0) :
    leftStripS p t = Real.sqrt (leftStripVarianceHalf p) * |t| * leftStripRoot p t := by
  have hc := half_pos (compositionMarginalVariance_pos p)
  have hm : compositionMoment p 0 t = leftStripVarianceHalf p * t ^ 2 * leftStripZ p 0 t := by
    rw [leftStrip_Z_eq_G hp ht, SmallCorner.G,
      mul_div_cancel₀ _ (mul_ne_zero hc.ne' (pow_ne_zero 2 ht))]
  change Real.sqrt (compositionMoment p 0 t) = _
  rw [hm, Real.sqrt_mul (mul_nonneg hc.le (sq_nonneg _)), Real.sqrt_mul hc.le,
    Real.sqrt_sq_eq_abs]
  rfl

private theorem leftStrip_S_derivatives {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) :
    let k := Real.sqrt (leftStripVarianceHalf p)
    deriv (leftStripS p) t = k * (leftStripRoot p t + t * leftStripRootOne p t) ∧
    deriv (deriv (leftStripS p)) t = k * (2 * leftStripRootOne p t + t * leftStripRootTwo p t) ∧
    deriv (deriv (deriv (leftStripS p))) t =
      k * (3 * leftStripRootTwo p t + t * leftStripRootThree p t) := by
  let k := Real.sqrt (leftStripVarianceHalf p)
  have h₁ {x : ℝ} (hx : 0 < x) :
      deriv (leftStripS p) x = k * (leftStripRoot p x + x * leftStripRootOne p x) := by
    have hd := ((hasDerivAt_id' x).mul (leftStrip_root_derivatives hp hx.ne').1).const_mul k
    have he : leftStripS p =ᶠ[𝓝 x] fun y ↦ k * (y * leftStripRoot p y) := by
      filter_upwards [eventually_gt_nhds hx] with y hy
      simpa only [abs_of_pos hy, mul_assoc] using leftStrip_S_eq_root hp hy.ne'
    simpa only [id_eq, mul_one, one_mul, add_comm] using (hd.congr_of_eventuallyEq he).deriv
  have h₂ {x : ℝ} (hx : 0 < x) :
      deriv (deriv (leftStripS p)) x =
        k * (2 * leftStripRootOne p x + x * leftStripRootTwo p x) := by
    have h := leftStrip_root_derivatives hp hx.ne'
    have hd := (h.1.add ((hasDerivAt_id' x).mul h.2.1)).const_mul k
    have he : deriv (leftStripS p) =ᶠ[𝓝 x]
        fun y ↦ k * (leftStripRoot p y + y * leftStripRootOne p y) := by
      filter_upwards [eventually_gt_nhds hx] with y hy using h₁ hy
    convert (hd.congr_of_eventuallyEq he).deriv using 1
    ring
  refine ⟨h₁ ht, h₂ ht, ?_⟩
  have h := leftStrip_root_derivatives hp ht.ne'
  have hd := ((h.2.1.const_mul 2).add ((hasDerivAt_id' t).mul h.2.2)).const_mul k
  have he : deriv (deriv (leftStripS p)) =ᶠ[𝓝 t]
      fun y ↦ k * (2 * leftStripRootOne p y + y * leftStripRootTwo p y) := by
    filter_upwards [eventually_gt_nhds ht] with y hy using h₂ hy
  convert (hd.congr_of_eventuallyEq he).deriv using 1
  ring

private theorem leftStrip_S_reflected_slope {p : ℕ} (hp : 0 < p) {v : ℝ} (hv : 0 < v) :
    leftStripReflectedSlope p v = 1 / v - leftStripRootOne p (-v) / leftStripRoot p (-v) := by
  let k := Real.sqrt (leftStripVarianceHalf p)
  have hk : 0 < k := Real.sqrt_pos.mpr (half_pos (compositionMarginalVariance_pos p))
  have hr : 0 < leftStripRoot p (-v) :=
    Real.sqrt_pos.mpr (leftStrip_Z_pos hp (neg_ne_zero.mpr hv.ne'))
  have he : (fun t ↦ leftStripS p (-t)) =ᶠ[𝓝 v] fun t ↦ k * (t * leftStripRoot p (-t)) := by
    filter_upwards [eventually_gt_nhds hv] with t ht
    simpa only [abs_neg, abs_of_pos ht, mul_assoc] using
      leftStrip_S_eq_root hp (neg_ne_zero.mpr ht.ne')
  have h := ((leftStrip_root_derivatives hp (neg_ne_zero.mpr hv.ne')).1.comp v
    (hasDerivAt_id' v).neg)
  have hd := ((hasDerivAt_id' v).mul h).const_mul k
  rw [leftStripReflectedSlope, (hd.congr_of_eventuallyEq he).deriv, he.eq_of_nhds]
  simp only [id_eq, Function.comp_apply, mul_neg, mul_one, one_mul]
  field_simp [hk.ne', hr.ne', hv.ne']
  <;> ring

private theorem leftStrip_S_mul_second {p : ℕ} (hp : 0 < p) {v d : ℝ}
    (hv : 0 < v) (hd : 0 < d) :
    leftStripS p v * deriv (deriv (leftStripS p)) d =
      leftStripVarianceHalf p * v * leftStripRoot p v *
        (2 * leftStripRootOne p d + d * leftStripRootTwo p d) := by
  have hk : Real.sqrt (leftStripVarianceHalf p) ^ 2 = leftStripVarianceHalf p :=
    Real.sq_sqrt (half_pos (compositionMarginalVariance_pos p)).le
  rw [leftStrip_S_eq_root hp hv.ne', abs_of_pos hv, (leftStrip_S_derivatives hp hd).2.1]
  calc
    _ = Real.sqrt (leftStripVarianceHalf p) ^ 2 * v * leftStripRoot p v *
        (2 * leftStripRootOne p d + d * leftStripRootTwo p d) := by ring
    _ = _ := by rw [hk]

/-- The normalized radical in `E` uses the existing continued marginal jet. -/
theorem leftStrip_E_eq_regularized {p : ℕ} (hp : 0 < p) {a v : ℝ}
    (hv : 0 < v) (hav : a < v) :
    leftStripE p a v = leftStripExpMoment p 2 0 a v -
      leftStripVarianceHalf p * v * leftStripRoot p v *
        (2 * leftStripRootOne p (v-a) + (v-a) * leftStripRootTwo p (v-a)) := by
  rw [leftStripE, leftStrip_S_mul_second hp hv (sub_pos.mpr hav)]

private def leftStripRegularizedSlope (p : ℕ) (t : ℝ) : ℝ :=
  leftStripZ p 1 t / (2 * leftStripZ p 0 t)

private theorem leftStrip_root_log_slope {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : t ≠ 0) :
    leftStripRootOne p t / leftStripRoot p t = leftStripRegularizedSlope p t := by
  rw [leftStripRootOne, leftStripRegularizedSlope, div_div, mul_assoc, ← sq,
    show leftStripRoot p t ^ 2 = leftStripZ p 0 t from Real.sq_sqrt (leftStrip_Z_pos hp ht).le]

/-- The expression bounded by the origin replay, in terms of the tilted moments
and the regularized marginal jet. -/
def leftStripRegularizedIntegrand (p : ℕ) (a v : ℝ) : ℝ :=
  let d := v-a
  let b := leftStripRegularizedSlope p (-v)
  let radical := ((1 + 3 / (p : ℝ)) / 4) * v * leftStripRoot p v *
    (3 * leftStripRootTwo p d + d * leftStripRootThree p d +
      (leftStripRegularizedSlope p v + b) *
        (2 * leftStripRootOne p d + d * leftStripRootTwo p d))
  v * (radical - leftStripExpMoment p 2 1 a v) + (1 - v * b) * leftStripExpMoment p 2 0 a v

/-- The regularized expression equals `v * (γ * E - E_v)` for the exact reflected slope. -/
theorem leftStrip_scaled_integrand_eq_regularized {p : ℕ} (hp : 0 < p) {a v : ℝ}
    (hv : 0 < v) (hav : a < v) :
    leftStripScaledIntegrand p a v = leftStripRegularizedIntegrand p a v := by
  let d := v-a
  let k := Real.sqrt (leftStripVarianceHalf p)
  let r := leftStripRoot p v
  let r₁ := leftStripRootOne p v
  let b := leftStripRegularizedSlope p (-v)
  let A := 2 * leftStripRootOne p d + d * leftStripRootTwo p d
  let B := 3 * leftStripRootTwo p d + d * leftStripRootThree p d
  have hd : 0 < d := sub_pos.mpr hav
  have hk : k ^ 2 = leftStripVarianceHalf p :=
    Real.sq_sqrt (half_pos (compositionMarginalVariance_pos p)).le
  have hr : 0 < r := Real.sqrt_pos.mpr (leftStrip_Z_pos hp hv.ne')
  have hs : leftStripS p v = k * v * r := by rw [leftStrip_S_eq_root hp hv.ne', abs_of_pos hv]
  have hγ : leftStripReflectedSlope p v = 1 / v - b := by
    rw [leftStrip_S_reflected_slope hp hv, leftStrip_root_log_slope hp (neg_ne_zero.mpr hv.ne')]
  have hSlope : leftStripRegularizedSlope p v = r₁ / r :=
    (leftStrip_root_log_slope hp hv.ne').symm
  unfold leftStripScaledIntegrand leftStripRegularizedIntegrand
  rw [hγ, (leftStrip_hasDerivAt_E_right hp hv hav).deriv, leftStrip_E_eq_regularized hp hv hav]
  change v * ((1 / v - b) * (leftStripExpMoment p 2 0 a v - leftStripVarianceHalf p * v * r * A) -
      (leftStripExpMoment p 2 1 a v - (deriv (leftStripS p) v * deriv (deriv (leftStripS p)) d +
        leftStripS p v * deriv (deriv (deriv (leftStripS p))) d))) =
    v * (((1 + 3 / (p : ℝ)) / 4) * v * r * (B + (leftStripRegularizedSlope p v + b) * A) -
      leftStripExpMoment p 2 1 a v) + (1 - v * b) * leftStripExpMoment p 2 0 a v
  rw [hs, (leftStrip_S_derivatives hp hv).1, (leftStrip_S_derivatives hp hd).2.1,
    (leftStrip_S_derivatives hp hd).2.2, hSlope, ← SmallCorner.joint_normalization_eq hp]
  change v * ((1 / v - b) * (leftStripExpMoment p 2 0 a v - leftStripVarianceHalf p * v * r * A) -
      (leftStripExpMoment p 2 1 a v - (k * (r + v * r₁) * (k * A) + k * v * r * (k * B)))) =
    v * (leftStripVarianceHalf p * v * r * (B + (r₁ / r + b) * A) -
      leftStripExpMoment p 2 1 a v) +
      (1 - v * b) * leftStripExpMoment p 2 0 a v
  generalize k = K at hk ⊢
  generalize leftStripVarianceHalf p = c at hk ⊢
  rw [← hk]
  field_simp [hv.ne', hr.ne']
  <;> ring

/-- For an endpoint with gap at most `1/2`, the integration interval lies in
the union of the origin and adjacent ranges. The adjacent input uses the
unscaled inequality. -/
theorem leftStrip_logKernel_mixed_lt_of_low_integrand {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu : 0 < u) (humax : u ≤ 1 / 2) (huv : u < v) (hgap : v - u ≤ 1 / 2)
    (horigin : ∀ a y : ℝ, 0 ≤ a → a ≤ 1 / 2 → 0 < y - a → y - a ≤ 1 / 2 →
      0 < leftStripRegularizedIntegrand p a y)
    (hadjacent : ∀ a y : ℝ, 0 ≤ a → a ≤ 1 / 2 → 1 / 2 ≤ y - a → y - a ≤ 1 →
      0 < leftStripRegularizedIntegrand p a y / y) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  have hp₀ : 0 < p := by omega
  have hv := hu.trans huv
  refine leftStrip_logKernel_mixed_lt_of_weighted hp₀ hu huv
    (leftStrip_small_slope hp hu humax) ?_
  dsimp only
  intro a ha
  have hav := ha.2.trans huv
  have ha₂ := ha.2.le.trans humax
  have hsign : 0 < leftStripScaledIntegrand p a v := by
    rw [leftStrip_scaled_integrand_eq_regularized hp₀ hv hav]
    by_cases hd : v - a ≤ 1 / 2
    · exact horigin a v ha.1.le ha₂ (sub_pos.mpr hav) hd
    · exact (div_pos_iff_of_pos_right hv).mp (hadjacent a v ha.1.le ha₂ (le_of_not_ge hd)
        (by linarith only [hgap, humax, ha.1]))
  have he := leftStrip_weightedThird_eq (γ := leftStripReflectedSlope p v) hp₀ hv hav
  exact he.trans_lt (sub_neg.mpr (lt_of_sub_pos ((mul_pos_iff_of_pos_left hv).mp hsign)))

private theorem logKernel_mixed_continuousAt {p : ℕ} (hp : 0 < p) {u v : ℝ}
    (hu : 0 < u) (huv : u < v) :
    ContinuousAt (fun y ↦ deriv (fun t ↦ deriv (fun x ↦ logKernel p x t) u) y) v := by
  let C := compositionMoment p
  have hC : ContDiff ℝ 3 (Function.uncurry C) := compositionMoment_smooth p
  have hMv : ContDiff ℝ 3 (fun z : ℝ × ℝ ↦ C 0 z.2) :=
    hC.comp (contDiff_const.prodMk contDiff_snd)
  have hMd : ContDiff ℝ 3 (fun z : ℝ × ℝ ↦ C 0 (z.2 - z.1)) :=
    hC.comp (contDiff_const.prodMk (contDiff_snd.sub contDiff_fst))
  have hMu' : ContDiff ℝ 3 (fun z : ℝ × ℝ ↦ C 0 (-z.1)) :=
    hC.comp (contDiff_const.prodMk contDiff_fst.neg)
  have hMv' : ContDiff ℝ 3 (fun z : ℝ × ℝ ↦ C 0 (-z.2)) :=
    hC.comp (contDiff_const.prodMk contDiff_snd.neg)
  have hpos (t : ℝ) (ht : t ≠ 0) : 0 < C 0 t := compositionMoment_marginal_pos hp ht
  have hv := hu.trans huv
  have hd := sub_pos.mpr huv
  have h₁ := mul_pos (hpos v hv.ne') (hpos (v - u) hd.ne')
  have h₂ := mul_pos (hpos (-u) (neg_ne_zero.mpr hu.ne')) (hpos (-v) (neg_ne_zero.mpr hv.ne'))
  have hN : ContDiffAt ℝ 3
      (fun z : ℝ × ℝ ↦ Real.sqrt (C 0 z.2 * C 0 (z.2 - z.1))) (u, v) :=
    (hMv.mul hMd).contDiffAt.sqrt h₁.ne'
  have hD : ContDiffAt ℝ 3
      (fun z : ℝ × ℝ ↦ Real.sqrt (C 0 (-z.1) * C 0 (-z.2))) (u, v) :=
    (hMu'.mul hMv').contDiffAt.sqrt h₂.ne'
  have hK : ContDiffAt ℝ 3 (Function.uncurry (logKernel p)) (u, v) :=
    (hC.contDiffAt.sub hN).div hD (Real.sqrt_pos.mpr h₂).ne'
  have hKleft := contDiffAt_partialLeft hK (by decide) (by decide)
    (show (2 : WithTop ℕ∞) + 1 ≤ 3 by decide)
  have hline : ContDiffAt ℝ 2 (fun t : ℝ ↦ (u, t)) v := contDiffAt_const.prodMk contDiffAt_id
  exact ((hKleft.comp v hline).derivWithin
    (show (1 : WithTop ℕ∞) + 1 ≤ 2 by decide)).continuousAt

/-- The separated left strip includes its finite cutoff for the
nonpositive sign required by the finite-sample reduction. -/
theorem leftStrip_logKernel_mixed_nonpos {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu : 0 < u) (humax : u ≤ 1 / 2) (hgap : 6 ≤ v - u) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v ≤ 0 := by
  have hc := logKernel_mixed_continuousAt (show 0 < p by omega) hu (show u < v by linarith)
  refine le_of_tendsto (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi v))) ?_
  filter_upwards [self_mem_nhdsWithin (s := Ioi v)] with y hy
  exact (leftStrip_logKernel_mixed_lt hp hu humax
    (hgap.trans_lt (sub_lt_sub_right (mem_Ioi.mp hy) u))).le

#print axioms leftStrip_numerator_decomposition
#print axioms leftStrip_numerator_weighted_mixed_lt
#print axioms leftStrip_logKernel_mixed_lt_of_slopes
#print axioms leftStrip_logKernel_mixed_lt
#print axioms leftStrip_logKernel_mixed_nonpos
#print axioms leftStrip_weightedThird_eq
#print axioms leftStrip_hasDerivAt_E_right
#print axioms leftStrip_E_eq_regularized
#print axioms leftStrip_scaled_integrand_eq_regularized
#print axioms leftStrip_logKernel_mixed_lt_of_low_integrand

end RefinedBMV.PositiveCenter
