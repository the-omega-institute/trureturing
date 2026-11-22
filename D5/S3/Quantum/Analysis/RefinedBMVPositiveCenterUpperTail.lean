/- GID: D5/S3/Quantum/Analysis/RefinedBMVPositiveCenterUpperTail
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Mixed derivative bounds for the positive-center upper tail. -/

import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterMixedJet
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Upper-tail derivative estimates for the refined BMV kernel -/

open Filter
open scoped Topology

namespace RefinedBMV.PositiveCenter

/-- Logarithmic slope of `(1-exp (-h*t))/h` at a positive gap. -/
noncomputable def upperTailSlope (h t : ℝ) : ℝ := h / (Real.exp (h*t) - 1)

private theorem exp_gap_pos {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    0 < Real.exp (h*t)-1 := by
  have hh' := Real.exp_lt_exp.mpr (mul_pos hh ht)
  rw [Real.exp_zero] at hh'
  linarith

theorem hasDerivAt_upperTailSlope {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    HasDerivAt (upperTailSlope h)
      (-(upperTailSlope h t * (h + upperTailSlope h t))) t := by
  have hmul : HasDerivAt (fun s : ℝ ↦ h*s) h t := by
    simpa using (hasDerivAt_id' t).const_mul h
  have he := hmul.exp.sub_const 1
  have hd := (hasDerivAt_const t h).div he (exp_gap_pos hh ht).ne'
  convert hd using 1
  · funext s
    rfl
  · unfold upperTailSlope
    field_simp [(exp_gap_pos hh ht).ne']
    ring

private theorem deriv_deriv_upperTailSlope {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    let L := upperTailSlope h t
    deriv (deriv (upperTailSlope h)) t = L*(h+L)*(h+2*L) := by
  dsimp only
  have hfirst := hasDerivAt_upperTailSlope hh ht
  have heq : deriv (upperTailSlope h) =ᶠ[𝓝 t]
      (fun s ↦ -(upperTailSlope h s*(h+upperTailSlope h s))) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact (hasDerivAt_upperTailSlope hh hs).deriv
  have hsecond := HasDerivAt.neg (hfirst.mul (hfirst.const_add h))
  change HasDerivAt (fun s ↦ -(upperTailSlope h s*(h+upperTailSlope h s))) _ t at hsecond
  rw [heq.deriv_eq, hsecond.deriv]
  ring

/-- Derivatives of the logarithmic slope, uniformly as the spacing parameter
approaches zero. -/
theorem upperTailSlope_bounds {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    0 < upperTailSlope h t ∧ upperTailSlope h t ≤ 1/t ∧
    0 ≤ -deriv (upperTailSlope h) t ∧ -deriv (upperTailSlope h) t ≤ 1/t^2 ∧
    0 ≤ deriv (deriv (upperTailSlope h)) t ∧
      deriv (deriv (upperTailSlope h)) t ≤ (h+2/t)/t^2 := by
  let L := upperTailSlope h t
  have hpos : 0 < L := div_pos hh (exp_gap_pos hh ht)
  have hL : L ≤ 1/t := by
    have he := Real.add_one_le_exp (h*t)
    change h/(Real.exp (h*t)-1) ≤ 1/t
    exact (div_le_div_iff₀ (exp_gap_pos hh ht) ht).2 (by linarith)
  have hz := mul_pos hh ht
  let e := Real.exp (h*t/2)
  let s := 2*Real.sinh (h*t/2)
  have he : 0 < e := Real.exp_pos _
  have hsh := Real.self_le_sinh_iff.mpr (by positivity : 0 ≤ h*t/2)
  have hs₁ : h*t ≤ s := by dsimp [s]; linarith
  have hs : 0 < s := hz.trans_le hs₁
  have hexp : Real.exp (h*t) = e^2 := by
    dsimp [e]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hgap : Real.exp (h*t)-1 = e*s := by
    rw [hexp]
    dsimp [e, s]
    rw [Real.sinh_eq, Real.exp_neg]
    field_simp [(Real.exp_pos (h*t/2)).ne']
  have hm : L*(h+L) = h^2/(s^2) := calc
    _ = h^2*Real.exp (h*t)/(Real.exp (h*t)-1)^2 := by
      dsimp [L, upperTailSlope]
      field_simp [(exp_gap_pos hh ht).ne']
      ring
    _ = _ := by
      rw [hgap, hexp]
      field_simp [he.ne', hs.ne']
  have hd₀ : 0 ≤ L*(h+L) := by positivity
  have hd₁ : L*(h+L) ≤ 1/t^2 := calc
    _ = h^2/s^2 := hm
    _ ≤ h^2/(h*t)^2 := div_le_div_of_nonneg_left (sq_nonneg h) (sq_pos_of_pos hz)
      (pow_le_pow_left₀ hz.le hs₁ 2)
    _ = _ := by field_simp [hh.ne', ht.ne']
  have hd₂ : 0 ≤ L*(h+L)*(h+2*L) := by positivity
  have hL₂ : h+2*L ≤ h+2/t := by
    rw [show 2/t = 2*(1/t) by ring]
    linarith only [hL]
  have hd₃ : L*(h+L)*(h+2*L) ≤ (h+2/t)/t^2 := calc
    _ ≤ (1/t^2)*(h+2/t) := mul_le_mul hd₁ hL₂ (by positivity) (by positivity)
    _ = _ := by ring
  rw [(hasDerivAt_upperTailSlope hh ht).deriv, deriv_deriv_upperTailSlope hh ht, neg_neg]
  exact ⟨hpos, hL, hd₀, hd₁, hd₂, hd₃⟩

/-- The regularized geometric sum used in the upper-tail formula. -/
noncomputable def upperTailGap (h t : ℝ) : ℝ := (1 - Real.exp (-(h * t))) / h

theorem hasDerivAt_upperTailGap {h t : ℝ} (hh : 0 < h) :
    HasDerivAt (upperTailGap h) (Real.exp (-(h * t))) t := by
  have hmul : HasDerivAt (fun s : ℝ ↦ h * s) h t := by
    simpa using (hasDerivAt_id' t).const_mul h
  have hneg : HasDerivAt (fun s : ℝ ↦ -(h * s)) (-h) t := HasDerivAt.neg hmul
  have hd := ((hasDerivAt_const t (1 : ℝ)).sub hneg.exp).div_const h
  change HasDerivAt (upperTailGap h) _ t at hd
  convert hd using 1
  field_simp [hh.ne']
  <;> ring

theorem upperTailGap_le {h t : ℝ} (hh : 0 < h) : upperTailGap h t ≤ t := by
  exact (div_le_iff₀ hh).2 (by linarith [Real.add_one_le_exp (-(h * t))])

theorem upperTailGap_logDeriv {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    deriv (upperTailGap h) t / upperTailGap h t = upperTailSlope h t := by
  rw [(hasDerivAt_upperTailGap hh).deriv]
  unfold upperTailGap upperTailSlope
  rw [Real.exp_neg]
  have he := (Real.exp_pos (h * t)).ne'
  have hsub := (exp_gap_pos hh ht).ne'
  have hden : 1 - (Real.exp (h * t))⁻¹ ≠ 0 := by
    intro heq
    apply hsub
    field_simp [he] at heq
    linarith
  field_simp [hh.ne', he, hsub, hden] <;> ring

/-- Lower bound for the denominator of the exponentially small remainder.
The order-two Taylor polynomial already suffices at the cutoff eleven. -/
theorem upperTailGap_ge_three {h d : ℝ} (hh : 0 < h) (hhmax : h ≤ 3 / 11)
    (hd : 11 ≤ d) : 3 ≤ upperTailGap h d := by
  have hd₀ : 0 ≤ d := by linarith
  have hz : 0 ≤ 11 * h := by positivity
  have hTaylor := Real.sum_le_exp_of_nonneg hz 3
  norm_num [Finset.sum_range_succ, Nat.factorial] at hTaylor
  have hnd : 11 * h ≤ h * d := by nlinarith only [mul_nonneg hh.le (sub_nonneg.mpr hd)]
  have hexp := hTaylor.trans (Real.exp_le_exp.mpr hnd)
  let W := 1 + 11 * h + (11 * h)^2 / 2
  have hW : 0 < W := by dsimp [W]; positivity
  have he : W ≤ Real.exp (h * d) := by
    dsimp only [W]
    linarith only [hexp]
  have hbound : (3 * h) * W ≤ W - 1 := by
    have hcubic := mul_le_mul_of_nonneg_left hhmax (sq_nonneg h)
    have hquad := mul_le_mul_of_nonneg_left hhmax hh.le
    dsimp [W]
    nlinarith only [hcubic, hquad, hh.le]
  have hinv : (Real.exp (h * d))⁻¹ ≤ W⁻¹ := inv_anti₀ hW he
  have hlin : 3 * h ≤ 1 - W⁻¹ := by
    have hdiv : 3 * h ≤ (W - 1) / W := (le_div_iff₀ hW).2 hbound
    rw [show (W - 1) / W = 1 - W⁻¹ by field_simp [hW.ne']] at hdiv
    exact hdiv
  unfold upperTailGap
  rw [Real.exp_neg]
  exact (le_div_iff₀ hh).mpr (hlin.trans (sub_le_sub_left hinv 1))

/-- The ratio that enters the leading square in the upper-tail formula. -/
noncomputable def upperTailRatio (h u : ℝ) : ℝ :=
  upperTailGap h u / (Real.exp u - 1)

theorem upperTailRatio_bounds {h u : ℝ} (hh : 0 < h) (hu : 0 < u) :
    0 < upperTailRatio h u ∧ upperTailRatio h u ≤ 1 ∧
      deriv (upperTailRatio h) u ≤ 0 := by
  let a : ℝ → ℝ := upperTailGap h
  have hz := mul_pos hh hu
  have hd : 0 < Real.exp u - 1 := by simpa using exp_gap_pos (h := 1) (by norm_num) hu
  have hneg : Real.exp (-(h*u)) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (neg_neg_of_pos hz)
  have ha₀ : 0 < a u := div_pos (sub_pos.mpr hneg) hh
  have ha₁ : a u ≤ u := upperTailGap_le hh
  have huE : u ≤ Real.exp u - 1 := by linarith [Real.add_one_le_exp u]
  refine ⟨div_pos ha₀ hd, (div_le_one hd).2 (ha₁.trans huE), ?_⟩
  have ha' : HasDerivAt a (Real.exp (-(h*u))) u := hasDerivAt_upperTailGap hh
  have huu : Real.exp u - 1 ≤ u*Real.exp u := by
    have hn : 1 - Real.exp (-u) ≤ u := by linarith [Real.add_one_le_exp (-u)]
    have hm := mul_le_mul_of_nonneg_right hn (Real.exp_pos u).le
    rw [sub_mul, one_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero] at hm
    exact hm
  have hla : u*Real.exp (-(h*u)) ≤ a u := by
    have he : h*u ≤ Real.exp (h*u) - 1 := by
      linarith [Real.add_one_le_exp (h*u)]
    have hm := mul_le_mul_of_nonneg_right he (Real.exp_pos (-(h*u))).le
    rw [sub_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at hm
    apply (le_div_iff₀ hh).2
    linarith only [hm]
  have hn : Real.exp (-(h*u)) * (Real.exp u-1) ≤ a u * Real.exp u := calc
    _ ≤ Real.exp (-(h*u)) * (u*Real.exp u) :=
      mul_le_mul_of_nonneg_left huu (Real.exp_pos _).le
    _ = (u*Real.exp (-(h*u))) * Real.exp u := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hla (Real.exp_pos u).le
  have hqd := ha'.div ((Real.hasDerivAt_exp u).sub_const 1) hd.ne'
  change HasDerivAt (upperTailRatio h) _ u at hqd
  rw [hqd.deriv]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith only [hn]) (sq_nonneg _)

/-- Quantitative error budget for the two upper-tail remainders. -/
theorem upperTail_remainder_budget {a d : ℝ} (hd : 11 ≤ d) (ha₀ : 0 ≤ a)
    (ha₁ : a ≤ d) :
    200*Real.exp (-d) + 10000*(a^2*Real.exp (-2*d)) < 1/200 := by
  have hexp : (50000 : ℝ) ≤ Real.exp 11 := calc
    _ ≤ ∑ i ∈ Finset.range 15, (11 : ℝ)^i / (i.factorial : ℝ) := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    _ ≤ _ := Real.sum_le_exp_of_nonneg (by norm_num) 15
  have he : Real.exp (-11 : ℝ) ≤ 1/50000 := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) hexp
  have hed : Real.exp (-d) ≤ 1/50000 :=
    (Real.exp_le_exp.mpr (by linarith : -d ≤ -11)).trans he
  have hprod : a*Real.exp (-d) ≤ 11/50000 := calc
    _ ≤ d*Real.exp (-d) := mul_le_mul_of_nonneg_right ha₁ (Real.exp_pos _).le
    _ ≤ 11*Real.exp (d-11)*Real.exp (-d) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      linarith [Real.add_one_le_exp (d-11)]
    _ = 11*Real.exp (-11) := by
      rw [mul_assoc, ← Real.exp_add, show d-11 + -d = -11 by ring]
    _ ≤ _ := by linarith
  have hs : a^2*Real.exp (-2*d) ≤ (11/50000 : ℝ)^2 := calc
    _ = (a*Real.exp (-d))^2 := by
      rw [mul_pow, pow_two (Real.exp (-d)), ← Real.exp_add, show -d + -d = -2*d by ring]
    _ ≤ _ := pow_le_pow_left₀ (mul_nonneg ha₀ (Real.exp_pos _).le) hprod 2
  linarith only [hed, hs]

/-- The variance-normalized logarithmic derivative is bounded below when
the logarithmic derivative of the marginal defect is at most `1 + 2/u`. -/
theorem upperTail_baseline_scale {u logDerivative : ℝ} (hu : 0 < u)
    (hlog : logDerivative ≤ 1 + 2/u) :
    (1/4 : ℝ) ≤ 1 + 2/(Real.exp u - 1) - logDerivative/2 := by
  let F : ℝ → ℝ := fun x ↦ (4-x)*Real.exp x - 4 - 7*x
  have hF (x : ℝ) : HasDerivAt F ((3-x)*Real.exp x - 7) x := by
    have h := (((hasDerivAt_const x (4 : ℝ)).sub (hasDerivAt_id' x)).mul
      (Real.hasDerivAt_exp x)).sub_const 4
    have h' := HasDerivAt.sub h ((hasDerivAt_id' x).const_mul 7)
    change HasDerivAt F _ x at h'
    convert h' using 1
    simp only [Pi.sub_apply]
    ring
  have hd : Differentiable ℝ F := fun x ↦ (hF x).differentiableAt
  have hexp₁ := Real.exp_one_lt_three
  have hexp₂ : Real.exp 2 < 8 := by
    rw [show (2 : ℝ) = 1+1 by norm_num, Real.exp_add]
    have he : Real.exp 1 ≤ 14/5 := by linarith [Real.exp_one_lt_d9]
    nlinarith [mul_nonneg (Real.exp_pos 1).le (sub_nonneg.mpr he)]
  have hlower : AntitoneOn F (Set.Iic 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Iic _) hd.continuous.continuousOn
      hd.differentiableOn
    intro x hx
    have hx₁ : x ≤ 1 := Set.mem_Iic.mp (interior_subset hx)
    rw [(hF x).deriv]
    have hs : 3-x ≤ 2*Real.exp (1-x) := by linarith [Real.add_one_le_exp (1-x)]
    have hm := mul_le_mul_of_nonneg_right hs (Real.exp_pos x).le
    rw [mul_assoc, ← Real.exp_add, sub_add_cancel] at hm
    linarith
  let G : ℝ → ℝ := fun x ↦ F x-x
  have hG (x : ℝ) : HasDerivAt G ((3-x)*Real.exp x - 8) x := by
    have h := HasDerivAt.sub (hF x) (hasDerivAt_id' x)
    change HasDerivAt G _ x at h
    convert h using 1
    ring
  have hmid : Antitone G := by
    apply antitone_of_deriv_nonpos (fun x ↦ (hG x).differentiableAt)
    intro x
    rw [(hG x).deriv]
    have hs : 3-x ≤ Real.exp (2-x) := by linarith [Real.add_one_le_exp (2-x)]
    have hm := mul_le_mul_of_nonneg_right hs (Real.exp_pos x).le
    rw [← Real.exp_add, sub_add_cancel] at hm
    linarith
  have hhigh : AntitoneOn F (Set.Ici 3) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _) hd.continuous.continuousOn
      hd.differentiableOn
    intro x hx
    have hx₃ : 3 ≤ x := Set.mem_Ici.mp (interior_subset hx)
    rw [(hF x).deriv]
    have hm := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx₃) (Real.exp_pos x).le
    linarith only [hm]
  have hFmid {x : ℝ} (hx₁ : 1 ≤ x) (hx₃ : x ≤ 3) : F x ≤ 0 := by
    have hx := hmid hx₁
    dsimp [G] at hx
    have h₁ : F 1 = 3*Real.exp 1 - 11 := by dsimp [F]; ring
    linarith only [hx, hx₃, h₁, hexp₁]
  have hFu : F u ≤ 0 := by
    rcases le_total u 1 with hu₁ | hu₁
    · have h₀ : F 0 = 0 := by norm_num [F]
      exact (hlower (by norm_num) (Set.mem_Iic.mpr hu₁) hu.le).trans_eq h₀
    rcases le_total u 3 with hu₃ | hu₃
    · exact hFmid hu₁ hu₃
    · exact (hhigh Set.self_mem_Ici (Set.mem_Ici.mpr hu₃) hu₃).trans
        (hFmid (by norm_num) le_rfl)
  have hden : 0 < Real.exp u-1 := by simpa using exp_gap_pos (h := 1) (by norm_num) hu
  have hsplit : 0 ≤ (1/4 : ℝ) + 2/(Real.exp u-1) - 1/u := by
    have heq : ((1/4 : ℝ) + 2/(Real.exp u-1) - 1/u)*(4*u*(Real.exp u-1)) = -F u := by
      dsimp [F]
      field_simp [hden.ne', hu.ne']
      <;> ring
    by_contra! hneg
    have hm := mul_neg_of_neg_of_pos hneg (by positivity : 0 < 4*u*(Real.exp u-1))
    rw [heq] at hm
    linarith only [hm, hFu]
  rw [show 2/u = 2*(1/u) by ring] at hlog
  linarith only [hlog, hsplit]

/-- Convert the bounds on the logarithmic slopes into the three normalized
derivative bounds used in the upper-tail product. -/
theorem upperTail_baseline {b ld lv ldNegDeriv : ℝ}
    (hb : 1/4 ≤ b) (hv : 0 ≤ lv) (hvd : lv ≤ ld) (hd : ld ≤ 1/11)
    (hderiv₀ : 0 ≤ ldNegDeriv) (hderiv₁ : ldNegDeriv ≤ 1/121) :
    let w := -1/2 + ld - lv/2
    let l := b - ld
    let k := w*l + ldNegDeriv;
    (-1/2 : ℝ) ≤ w ∧ w ≤ -9/22 ∧ 7*b/11 ≤ l ∧
      -b/2 ≤ k ∧ k ≤ -5*b/22 ∧ 0 ≤ l-w ∧ l-w ≤ 3*b := by
  dsimp only
  have hd₀ : 0 ≤ ld := hv.trans hvd
  have hb₀ : 0 ≤ b := by linarith
  let w : ℝ := -1/2 + ld - lv/2
  let l : ℝ := b - ld
  change (-1/2 : ℝ) ≤ w ∧ w ≤ -9/22 ∧ 7*b/11 ≤ l ∧
    -b/2 ≤ w*l + ldNegDeriv ∧ w*l + ldNegDeriv ≤ -5*b/22 ∧
    0 ≤ l-w ∧ l-w ≤ 3*b
  have hw₀ : -1/2 ≤ w := by dsimp [w]; linarith
  have hw₁ : w ≤ -9/22 := by dsimp [w]; linarith
  have hl₀ : 7*b/11 ≤ l := by dsimp [l]; linarith
  have hl₁ : l ≤ b := by dsimp [l]; linarith
  have hl : 0 ≤ l := (by positivity : 0 ≤ 7*b/11).trans hl₀
  have hk₀ : -(1/2 : ℝ)*b ≤ w*l := calc
    -(1/2 : ℝ)*b ≤ -(1/2 : ℝ)*l := mul_le_mul_of_nonpos_left hl₁ (by norm_num)
    _ ≤ w*l := mul_le_mul_of_nonneg_right (by linarith only [hw₀]) hl
  have hk₁ : w*l ≤ -(9/22 : ℝ)*(7*b/11) := calc
    w*l ≤ -(9/22 : ℝ)*l := mul_le_mul_of_nonneg_right (by linarith only [hw₁]) hl
    _ ≤ -(9/22 : ℝ)*(7*b/11) := mul_le_mul_of_nonpos_left hl₀ (by norm_num)
  exact ⟨hw₀, hw₁, hl₀, by linarith, by linarith, by linarith, by linarith⟩

/-- The exact product rule in `(u,v)`, expressed with the derivatives of
the factors in `(u,d)` where `d=v-u`. The baseline jet is normalized by its
positive value. -/
private theorem upperTail_product_components
    (w l k r ru rd rud rdd e eu ed eud edd : ℝ) :
    let t : MixedJet ℝ := ⟨1, l, w, k⟩
    let R : MixedJet ℝ := ⟨r, ru-rd, rd, rud-rdd⟩
    let E : MixedJet ℝ := ⟨e, eu-ed, ed, eud-edd⟩
    let z := t.mul ((R.mul R).add E)
    z.du = l*(r^2+e)+2*r*(ru-rd)+(eu-ed) ∧
    z.duv = k*r^2 + 2*r*rd*(l-w) + 2*ru*(r*w+rd) +
      2*r*(rud-rdd) - 2*rd^2 + (k*e + (l-w)*ed + w*eu + eud - edd) := by
  dsimp only [MixedJet.mul, MixedJet.add]
  constructor <;> ring

/-- On the upper tail the normalized product is increasing in the lower
logarithmic coordinate at fixed upper coordinate and has negative mixed
derivative. The hypotheses are the explicit scalar bounds from the
positive-center tail estimates for `d ≥ 11`. -/
theorem upperTail_product_sign
    {b w l k r ru rd rud rdd e eu ed eud edd : ℝ}
    (hb : 1/4 ≤ b) (hw₀ : -1/2 ≤ w) (hw₁ : w ≤ -9/22)
    (hl : 7*b/11 ≤ l) (hk₀ : -b/2 ≤ k) (hk₁ : k ≤ -5*b/22)
    (hs₀ : 0 ≤ l-w) (hs₁ : l-w ≤ 3*b)
    (hr₀ : 10/11 ≤ r) (hr₁ : r ≤ 1) (hru : 0 ≤ ru)
    (hrd₀ : 0 ≤ rd) (hrd₁ : rd ≤ 1/121) (hrud : rud ≤ 0) (hrdd : -1/220 ≤ rdd)
    (he : |e| ≤ 1/200) (heu : |eu| ≤ 1/200) (hed : |ed| ≤ 1/200)
    (heud : |eud| ≤ 1/200) (hedd : |edd| ≤ 1/200) :
    let t : MixedJet ℝ := ⟨1, l, w, k⟩
    let R : MixedJet ℝ := ⟨r, ru-rd, rd, rud-rdd⟩
    let E : MixedJet ℝ := ⟨e, eu-ed, ed, eud-edd⟩
    let z := t.mul ((R.mul R).add E)
    0 < z.du ∧ z.duv < 0 := by
  dsimp only
  rw [(upperTail_product_components w l k r ru rd rud rdd e eu ed eud edd).1,
    (upperTail_product_components w l k r ru rd rud rdd e eu ed eud edd).2]
  have hb₀ : 0 ≤ b := by linarith
  have hr : 0 ≤ r := by linarith
  have hl₀ : 0 ≤ l := (by positivity : 0 ≤ 7*b/11).trans hl
  have hr2 : (10/11 : ℝ)^2 ≤ r^2 := by nlinarith
  have hrRd : r*rd ≤ 1/121 :=
    (mul_le_mul_of_nonneg_right hr₁ hrd₀).trans (by simpa using hrd₁)
  have he₀ := (abs_le.mp he).1
  have heu₀ := (abs_le.mp heu).1
  have hed₁ := (abs_le.mp hed).2
  have hconst : (0 : ℝ) ≤ (10/11)^2-1/200 := by norm_num
  have hmain : 7*b/11*((10/11)^2-1/200) ≤ l*(r^2+e) := calc
    _ ≤ l*((10/11)^2-1/200) := mul_le_mul_of_nonneg_right hl hconst
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hl₀
  have hru₀ := mul_nonneg hr hru
  have hrw : r*w + rd ≤ 0 := by
    have h₁ := mul_le_mul_of_nonneg_left hw₁ hr
    have h₂ := mul_le_mul_of_nonpos_right hr₀ (show -(9/22 : ℝ) ≤ 0 by norm_num)
    linarith
  have hkr : k*r^2 ≤ -(5*b/22)*(10/11)^2 := calc
    _ ≤ -(5*b/22)*r^2 := mul_le_mul_of_nonneg_right (by linarith only [hk₁]) (sq_nonneg r)
    _ ≤ _ := mul_le_mul_of_nonpos_left hr2 (by linarith)
  have hsrd : r*rd*(l-w) ≤ 3*b/121 := calc
    _ ≤ (1/121)*(l-w) := mul_le_mul_of_nonneg_right hrRd hs₀
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hs₁ (show (0 : ℝ) ≤ 1/121 by norm_num)
      linarith
  have hruw := mul_nonpos_of_nonneg_of_nonpos hru hrw
  have hrd2 : r*(rud-rdd) ≤ 1/220 := calc
    _ ≤ r*(1/220) := mul_le_mul_of_nonneg_left (by linarith) hr
    _ ≤ _ := by
      simpa using mul_le_mul_of_nonneg_right hr₁ (show (0 : ℝ) ≤ 1/220 by norm_num)
  have hbase : k*r^2 + 2*r*rd*(l-w) + 2*ru*(r*w+rd) + 2*r*(rud-rdd) - 2*rd^2
      ≤ -b/10 := by nlinarith [sq_nonneg rd]
  have hkabs : |k| ≤ b/2 := abs_le.mpr ⟨by linarith only [hk₀], by linarith⟩
  have hwabs : |w| ≤ 1/2 := abs_le.mpr ⟨by linarith only [hw₀], by linarith⟩
  have hsabs : |l-w| ≤ 3*b := by simpa [abs_of_nonneg hs₀] using hs₁
  have hke : k*e ≤ (b/2)*(1/200) := calc
    _ ≤ |k*e| := le_abs_self _
    _ = |k| * |e| := abs_mul _ _
    _ ≤ _ := mul_le_mul hkabs he (abs_nonneg _) (by positivity)
  have hsed : (l-w)*ed ≤ (3*b)*(1/200) := calc
    _ ≤ |(l-w)*ed| := le_abs_self _
    _ = |l-w| * |ed| := abs_mul _ _
    _ ≤ _ := mul_le_mul hsabs hed (abs_nonneg _) (by positivity)
  have hweu : w*eu ≤ (1/2)*(1/200) := calc
    _ ≤ |w*eu| := le_abs_self _
    _ = |w| * |eu| := abs_mul _ _
    _ ≤ _ := mul_le_mul hwabs heu (abs_nonneg _) (by norm_num)
  constructor
  · nlinarith
  · linarith [(abs_le.mp heud).2, (abs_le.mp hedd).1]

/-- Apply the product estimate to the actual leading correction and
logarithmic slopes, leaving the error bounds and baseline scale explicit. -/
theorem upperTail_normalized_sign {h u d b e eu ed eud edd : ℝ}
    (hh : 0 < h) (hhmax : h ≤ 3/11) (hu : 0 < u) (hd : 11 ≤ d) (hb : 1/4 ≤ b)
    (he : |e| ≤ 1/200) (heu : |eu| ≤ 1/200) (hed : |ed| ≤ 1/200)
    (heud : |eud| ≤ 1/200) (hedd : |edd| ≤ 1/200) :
    let L := upperTailSlope h d
    let L₁ := deriv (upperTailSlope h) d
    let L₂ := deriv (deriv (upperTailSlope h)) d
    let w := -1/2+L-upperTailSlope h (u+d)/2
    let l := b-L
    let t : MixedJet ℝ := ⟨1, l, w, w*l-L₁⟩
    let f := upperTailRatio h u
    let f₁ := deriv (upperTailRatio h) u
    let R : MixedJet ℝ := ⟨1-L*f, -L*f₁+L₁*f, -L₁*f, -L₁*f₁+L₂*f⟩
    let E : MixedJet ℝ := ⟨e, eu-ed, ed, eud-edd⟩
    let z := t.mul ((R.mul R).add E)
    0 < z.du ∧ z.duv < 0 := by
  let L := upperTailSlope h d
  let L₁ := deriv (upperTailSlope h) d
  let L₂ := deriv (deriv (upperTailSlope h)) d
  let f := upperTailRatio h u
  let f₁ := deriv (upperTailRatio h) u
  have hd₀ : 0 < d := by linarith
  have hv : 0 < u+d := by positivity
  obtain ⟨hL₀, hL₁, hderiv₀, hderiv₁, hcurv₀, hcurv₁⟩ := upperTailSlope_bounds hh hd₀
  obtain ⟨hf₀, hf₁, hf'⟩ := upperTailRatio_bounds hh hu
  have hf : 0 ≤ f := hf₀.le
  have hL : 0 ≤ L := hL₀.le
  have hinv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 11) hd
  have hinv₂ : 1/d^2 ≤ 1/121 := by
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 121)
    have hs : (11 : ℝ)^2 ≤ d^2 := pow_le_pow_left₀ (by norm_num) hd 2
    norm_num at hs
    exact hs
  have hLmax : L ≤ 1/11 := hL₁.trans hinv
  have hL₁max : -L₁ ≤ 1/121 := hderiv₁.trans hinv₂
  have hL₂max : L₂ ≤ 1/220 := calc
    _ ≤ (h+2/d)/d^2 := hcurv₁
    _ = (h+2*(1/d))*(1/d^2) := by ring
    _ ≤ ((3/11 : ℝ)+2*(1/11))*(1/121) :=
      mul_le_mul (by linarith only [hhmax, hinv]) hinv₂ (by positivity) (by norm_num)
    _ ≤ _ := by norm_num
  have hlv : upperTailSlope h (u+d) ≤ L := by
    unfold upperTailSlope L
    refine div_le_div_of_nonneg_left hh.le (exp_gap_pos hh hd₀) ?_
    exact sub_le_sub_right (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hh.le hu.le])) _
  have hlv₀ : 0 ≤ upperTailSlope h (u+d) := (upperTailSlope_bounds hh hv).1.le
  obtain ⟨hw₀, hw₁, htl, hk₀, hk₁, hs₀, hs₁⟩ :=
    upperTail_baseline hb hlv₀ hlv hLmax hderiv₀ hL₁max
  have hr₀ : 10/11 ≤ 1-L*f := by
    have hm := mul_le_mul_of_nonneg_left hf₁ hL
    linarith only [hm, hLmax]
  have hr₁ : 1-L*f ≤ 1 := by linarith [mul_nonneg hL hf]
  have hrd₁ : (-L₁)*f ≤ 1/121 := by
    have hm := mul_le_mul_of_nonneg_left hf₁ hderiv₀
    linarith only [hm, hL₁max]
  have hrdd : -1/220 ≤ -(L₂*f) := by
    have hm := mul_le_mul_of_nonneg_left hf₁ hcurv₀
    linarith only [hm, hL₂max]
  have hsign := upperTail_product_sign hb hw₀ hw₁ htl hk₀ hk₁ hs₀ hs₁ hr₀ hr₁
    (neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hL hf')) (mul_nonneg hderiv₀ hf)
    hrd₁ (mul_nonpos_of_nonneg_of_nonpos hderiv₀ hf') hrdd he heu hed heud hedd
  simpa only [L, L₁, L₂, f, f₁, sub_eq_add_neg, neg_mul, neg_neg] using hsign

private theorem isAt_upperFactor {S : ℝ → ℝ} {v s' : ℝ}
    (hS : HasDerivAt S s' v) (u : ℝ) :
    MixedJet.IsAt (fun _ y ↦ ⟨S y, 0, s', 0⟩) u v := by
  refine ⟨Filter.Eventually.of_forall fun y ↦ hasDerivAt_const u (S y), hS, ?_⟩
  exact hasDerivAt_const v (0 : ℝ)

/-- The upper-gap normalizing factor before taking the inverse square root. -/
noncomputable def upperTailNormalizer (n : ℕ) (h c v : ℝ) : ℝ :=
  1 - (∑ i ∈ Finset.range n, Real.exp (-((i + 1 : ℕ) : ℝ) * h * v)) / n -
    c * ((1 - Real.exp (-(h * v))) * Real.exp (-v))

/-- The upper-gap factor contributes a nonpositive derivative. Positivity
of the normalizer comes from the underlying marginal defect. -/
theorem upperTail_normalizer_invSqrt {n : ℕ} {h c v : ℝ}
    (hh : 0 < h) (hc : 0 ≤ c) (hv : 1 ≤ v) (hA : 0 < upperTailNormalizer n h c v) :
    ∃ s' ≤ 0, HasDerivAt (fun x ↦ 1 / Real.sqrt (upperTailNormalizer n h c x)) s' v := by
  let r (i : ℕ) : ℝ := -((i + 1 : ℕ) : ℝ) * h
  have hr (i : ℕ) : r i ≤ 0 := by
    dsimp [r]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hh.le
  have hexp (k : ℝ) : HasDerivAt (fun x ↦ Real.exp (k * x))
      (k * Real.exp (k * v)) v := by
    have hx : HasDerivAt (fun x : ℝ ↦ k * x) k v := by
      simpa using (hasDerivAt_id' v).const_mul k
    simpa only [mul_comm] using hx.exp
  have hsum : HasDerivAt
      (fun x ↦ ∑ i ∈ Finset.range n, Real.exp (r i * x))
      (∑ i ∈ Finset.range n, r i * Real.exp (r i * v)) v :=
    HasDerivAt.fun_sum fun i _ ↦ hexp (r i)
  let D := ∑ i ∈ Finset.range n, r i * Real.exp (r i * v)
  have hD : D ≤ 0 := Finset.sum_nonpos fun i _ ↦
    mul_nonpos_of_nonpos_of_nonneg (hr i) (Real.exp_pos _).le
  let f : ℝ → ℝ := fun x ↦ (1 - Real.exp (-(h * x))) * Real.exp (-x)
  let f' := ((h + 1) * Real.exp (-(h * v)) - 1) * Real.exp (-v)
  have hf : HasDerivAt f f' v := by
    have hexp₁ : HasDerivAt (fun x ↦ Real.exp (-(h * x)))
        (-h * Real.exp (-(h * v))) v := by simpa only [neg_mul] using hexp (-h)
    have hexp₂ : HasDerivAt (fun x ↦ Real.exp (-x)) (-Real.exp (-v)) v := by
      simpa only [neg_mul, one_mul, neg_smul] using hexp (-1)
    have h := (HasDerivAt.sub (hasDerivAt_const v (1 : ℝ)) hexp₁).mul hexp₂
    change HasDerivAt f _ v at h
    convert h using 1
    dsimp [f']
    ring
  have hf' : f' ≤ 0 := by
    have hExp := Real.add_one_le_exp (h * v)
    have hbase : h + 1 ≤ Real.exp (h * v) := by
      nlinarith [mul_nonneg hh.le (sub_nonneg.mpr hv)]
    have hp := mul_le_mul_of_nonneg_right hbase (Real.exp_pos (-(h * v))).le
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hp
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hp) (Real.exp_pos _).le
  have hnorm := (HasDerivAt.sub (hasDerivAt_const v (1 : ℝ))
    (hsum.div_const (n : ℝ))).sub (hf.const_mul c)
  change HasDerivAt (upperTailNormalizer n h c) _ v at hnorm
  have hs := hnorm.sqrt hA.ne'
  have hs₀ : 0 < Real.sqrt (upperTailNormalizer n h c v) := Real.sqrt_pos.2 hA
  have hq := (hasDerivAt_const v (1 : ℝ)).div hs hs₀.ne'
  refine ⟨_, ?_, hq⟩
  have hnorm₀ : 0 ≤ (0 - D / n) - c * f' := by
    linarith [div_nonpos_of_nonpos_of_nonneg hD (by positivity : 0 ≤ (n : ℝ)),
      mul_nonpos_of_nonneg_of_nonpos hc hf']
  apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
  simpa only [zero_mul, one_mul, zero_sub, neg_nonpos] using
    div_nonneg hnorm₀ (by positivity : 0 ≤ 2 * Real.sqrt (upperTailNormalizer n h c v))

/-- Multiplication by the positive upper-coordinate factor preserves the
strict mixed sign under the two product derivative signs. -/
theorem upperTail_restore_upperFactor {F : ℝ → ℝ → MixedJet ℝ}
    {S : ℝ → ℝ} {u v s' : ℝ} (hF : MixedJet.IsAt F u v)
    (hS : HasDerivAt S s' v) (hS₀ : 0 < S v) (hS₁ : s' ≤ 0)
    (hFu : 0 ≤ (F u v).du) (hFuv : (F u v).duv < 0) :
    deriv (fun y ↦ deriv (fun x ↦ S y * (F x y).value) u) v < 0 := by
  have hj := (isAt_upperFactor hS u).mul hF
  have hfirst :
      (fun y ↦ deriv (fun x ↦ S y * (F x y).value) u) =ᶠ[𝓝 v]
      (fun y ↦ (⟨S y, 0, s', 0⟩ : MixedJet ℝ).mul (F u y) |>.du) := by
    filter_upwards [hj.1] with y hy
    exact hy.deriv
  rw [hfirst.deriv_eq, hj.2.2.deriv]
  change 0 * (F u v).value + 0 * (F u v).dv + s' * (F u v).du +
    S v * (F u v).duv < 0
  have h₀ := mul_nonpos_of_nonpos_of_nonneg hS₁ hFu
  have h₁ := mul_neg_of_pos_of_neg hS₀ hFuv
  linarith

#print axioms upperTail_baseline
#print axioms upperTailSlope_bounds
#print axioms upperTailGap_ge_three
#print axioms upperTailGap_logDeriv
#print axioms upperTailRatio_bounds
#print axioms upperTail_remainder_budget
#print axioms upperTail_baseline_scale
#print axioms upperTail_product_sign
#print axioms upperTail_normalized_sign
#print axioms upperTail_normalizer_invSqrt
#print axioms upperTail_restore_upperFactor

end RefinedBMV.PositiveCenter
