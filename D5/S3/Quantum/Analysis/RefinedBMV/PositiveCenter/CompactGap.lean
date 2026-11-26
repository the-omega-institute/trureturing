/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactGap
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact scaled kernel for the centered compact-gap Taylor calculation. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactGapIdentities
import Batteries.Tactic.OpenPrivate

/-! Short- and middle-gap sign estimates for the scaled kernel. -/

open Filter
open scoped Topology

namespace RefinedBMV.PositiveCenter.CompactGap

open private rate c R W X rate_pos gap_pos W_pos
  X_pos coordinate shortGapF_contDiffAt
  from D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactGapIdentities

private theorem shortGapQ_eq (h x : ℝ) (ha : upperTailGap h x ≠ 0) :
    R h x / upperTailGap h x - (3+h-1/4) = shortGapQuotient h x := by
  unfold R shortGapQuotient
  field_simp [ha] <;> ring

/-- Reduce the short-gap sign for the actual matrix kernel to curvature of
the scalar gap profile and the estimates for the marginal correction. -/
theorem logKernel_gap_mixed_of_profile_margin_of_slopes {p : ℕ} (hp : 11 ≤ p) {u v ε : ℝ}
    (hu₀ : 0 < u) (huv : u < v) :
    let h := rate p
    let d := v-u
    let a := upperTailGap h
    let P := fun x ↦ a x / Real.sqrt (W h x)
    let V := fun x ↦ 1 / Real.sqrt (W h x)
    let Z := fun x ↦ Real.sqrt (X h x)
    let α := fun x ↦ deriv P x / P x
    let β := fun x ↦ deriv V x / V x
    let m := 3 / 2 + h
    let Q := shortGapQuotient h
    let ξ := c h*a v*Real.exp (-((u+v)/2))
    0 ≤ α u → β v ≤ 0 → α u - β v ≤ 1 / 2 →
    0 ≤ shortGapF h d →
    ε < deriv (deriv (shortGapF h)) d - (α u - β v) * deriv (shortGapF h) d -
      (β v - m) * Real.exp (-m * d) * (deriv Q u + (α u + m) * Q u) →
    0 ≤ deriv (shortGapJ h) d →
    deriv (shortGapJ h) d / 2 ≤ deriv (deriv (shortGapJ h)) d →
    0 ≤ deriv Z v →
    deriv Z v * deriv (shortGapJ h) d ≤ ξ*(1/2-α u)*(1/2-α v) →
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < -(P u * V v * ε) := by
  let h := rate p
  let d := v-u
  let a := upperTailGap h
  let P : ℝ → ℝ := fun x ↦ a x / Real.sqrt (W h x)
  let V : ℝ → ℝ := fun x ↦ 1 / Real.sqrt (W h x)
  let Z : ℝ → ℝ := fun x ↦ Real.sqrt (X h x)
  let α : ℝ → ℝ := fun x ↦ deriv P x / P x
  let β : ℝ → ℝ := fun x ↦ deriv V x / V x
  let m := 3 / 2 + h
  let Q := shortGapQuotient h
  let E : ℝ → ℝ := fun x ↦ Real.exp (-x/2)
  let C : ℝ → ℝ := fun x ↦ c h*a x*E x
  let ξ := c h*a v*Real.exp (-((u+v)/2))
  change 0 ≤ α u → β v ≤ 0 → α u - β v ≤ 1 / 2 →
    0 ≤ shortGapF h d →
    ε < deriv (deriv (shortGapF h)) d - (α u - β v) * deriv (shortGapF h) d -
      (β v - m) * Real.exp (-m * d) * (deriv Q u + (α u + m) * Q u) →
    0 ≤ deriv (shortGapJ h) d →
    deriv (shortGapJ h) d / 2 ≤ deriv (deriv (shortGapJ h)) d → 0 ≤ deriv Z v →
    deriv Z v * deriv (shortGapJ h) d ≤ ξ*(1/2-α u)*(1/2-α v) →
    _
  intro hα hβ hαβ hf hmargin hj' hj'' hz' hc
  have hp₀ : 0 < p := by omega
  have hh := rate_pos hp₀
  have hv₀ := hu₀.trans huv
  have hd : 0 < d := sub_pos.mpr huv
  have hPpos {t : ℝ} (ht : 0 < t) : 0 < P t :=
    div_pos (gap_pos hp₀ ht) (Real.sqrt_pos.mpr (W_pos hp₀ ht))
  have hVpos {t : ℝ} (ht : 0 < t) : 0 < V t :=
    one_div_pos.mpr (Real.sqrt_pos.mpr (W_pos hp₀ ht))
  have hWdiff (t : ℝ) : DifferentiableAt ℝ (W h) t := by
    unfold W R upperTailGap
    fun_prop
  have hPdiff {t : ℝ} (ht : 0 < t) : DifferentiableAt ℝ P t :=
    (hasDerivAt_upperTailGap hh).differentiableAt.div
      ((hWdiff t).hasDerivAt.sqrt (W_pos hp₀ ht).ne').differentiableAt
      (Real.sqrt_pos.mpr (W_pos hp₀ ht)).ne'
  have hVdiff {t : ℝ} (ht : 0 < t) : DifferentiableAt ℝ V t :=
    (hasDerivAt_const t (1 : ℝ)).differentiableAt.div
      ((hWdiff t).hasDerivAt.sqrt (W_pos hp₀ ht).ne').differentiableAt
      (Real.sqrt_pos.mpr (W_pos hp₀ ht)).ne'
  have hPderiv {t : ℝ} (ht : 0 < t) : HasDerivAt P (α t*P t) t := by
    simpa only [α, div_mul_cancel₀ _ (hPpos ht).ne'] using (hPdiff ht).hasDerivAt
  have hVderiv : HasDerivAt V (β v*V v) v := by
    simpa only [β, div_mul_cancel₀ _ (hVpos hv₀).ne'] using (hVdiff hv₀).hasDerivAt
  have haEq : a =ᶠ[𝓝 v] fun x ↦ P x / V x := by
    filter_upwards [eventually_gt_nhds hv₀] with x hx
    dsimp [P, V]
    rw [div_div_eq_mul_div, div_one, div_mul_cancel₀ _ (Real.sqrt_pos.mpr (W_pos hp₀ hx)).ne']
  have haDeriv : HasDerivAt a ((α v-β v)*a v) v := by
    have H := ((hPderiv hv₀).div hVderiv (hVpos hv₀).ne').congr_of_eventuallyEq haEq
    refine H.congr_deriv ?_
    rw [haEq.eq_of_nhds]
    field_simp [(hVpos hv₀).ne'] <;> ring
  have he (t : ℝ) : HasDerivAt E (-(1/2)*E t) t := by
    have H := ((hasDerivAt_id' t).neg.div_const 2).exp
    convert H using 1 <;> simp [E] <;> ring
  have hC : HasDerivAt C ((α v-β v-1/2)*C v) v := by
    refine ((haDeriv.const_mul (c h)).mul (he v)).congr_deriv ?_
    dsimp only [C]
    ring
  have hX (t : ℝ) : ContDiff ℝ 2 (X h) := by
    unfold X upperTailLambda upperTailGap
    fun_prop
  have hJ : ContDiffAt ℝ 2 (shortGapJ h) d := by
    have hs := (hX d).contDiffAt.sqrt (X_pos hp₀ hd).ne'
    unfold shortGapJ
    apply ContDiffAt.div _ (by unfold upperTailGap; fun_prop) (gap_pos hp₀ hd).ne'
    exact (by fun_prop : ContDiffAt ℝ 2 (fun x : ℝ ↦ Real.exp (3*x/2)) d).mul hs
  have hF := shortGapF_contDiffAt hp₀ hd
  have hQ : DifferentiableAt ℝ (shortGapQuotient h) u := by
    unfold shortGapQuotient
    exact (hasDerivAt_const u (h+1/4)).differentiableAt.sub
      ((by fun_prop : DifferentiableAt ℝ (fun x : ℝ ↦ 1 - Real.exp (-((3+2*h)*x))) u).div
        (hasDerivAt_upperTailGap hh).differentiableAt (gap_pos hp₀ hu₀).ne')
  have hZ : DifferentiableAt ℝ Z v :=
    ((hX v).contDiffAt.sqrt (X_pos hp₀ hv₀).ne').differentiableAt (by norm_num)
  let F (x y : ℝ) := P x*V y*
    (shortGapF h (y-x) + shortGapQuotient h x*Real.exp (-(3/2+h)*(y-x)) +
      (1-Z y)*shortGapJ h (y-x) - E x*C y)
  have hEq {x y : ℝ} (hx : 0 < x) (hxy : x < y) : logKernel p x y = F x y := by
    have H := logKernel_eq_shortGap hp₀ hx (sub_pos.mpr hxy)
    dsimp only at H
    rw [sub_add_cancel] at H
    change _ = P x*V y*(shortGapF h (y-x) +
      (R h x/a x-(3+h-1/4))*Real.exp (-((3/2+h)*(y-x))) +
      (1-Z y)*shortGapJ h (y-x) - c h*a y*Real.exp (-((x+y)/2))) at H
    rw [shortGapQ_eq h x (gap_pos hp₀ hx).ne',
      show -((3/2+h)*(y-x)) = -(3/2+h)*(y-x) by ring] at H
    rw [H]
    have heq : Real.exp (-((x+y)/2)) = E x * E y := by
      unfold E
      rw [← Real.exp_add]
      congr 1
      ring
    unfold F C
    rw [heq]
    ring
  have hLoc : (fun y ↦ deriv (fun x ↦ logKernel p x y) u) =ᶠ[𝓝 v]
      (fun y ↦ deriv (fun x ↦ F x y) u) := by
    filter_upwards [eventually_gt_nhds huv] with y hy
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [eventually_gt_nhds hu₀, eventually_lt_nhds hy] with x hx hxy
    exact hEq hx hxy
  rw [hLoc.deriv_eq]
  change deriv (fun y ↦ deriv (fun x ↦ P x*V y*
    (shortGapF h (y-x) + shortGapQuotient h x*Real.exp (-(3/2+h)*(y-x)) +
      (1-Z y)*shortGapJ h (y-x) - Real.exp (-x/2)*C y)) u) v < _
  rw [shortGap_weighted_mixed_formula (hPderiv hu₀) hVderiv hF hJ hQ hZ hC]
  dsimp only
  have hξ : Real.exp (-u/2)*C v = ξ := by
    unfold C E ξ
    rw [show Real.exp (-u/2)*(c h*a v*Real.exp (-v/2)) =
        c h*a v*(Real.exp (-u/2)*Real.exp (-v/2)) by ring, ← Real.exp_add]
    congr 2
    ring
  rw [hξ, show -(P u * V v * ε) = P u * V v * (-ε) by ring]
  apply mul_lt_mul_of_pos_left _ (mul_pos (hPpos hu₀) (hVpos hv₀))
  have hj : 0 ≤ shortGapJ h d :=
    div_nonneg (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)) (gap_pos hp₀ hd).le
  have hz : 0 ≤ 1-Z v := by
    have H := Real.sqrt_le_sqrt (show X h v ≤ 1 by
      unfold X upperTailLambda
      have ha := (gap_pos hp₀ hv₀).le
      have hsum : 0 ≤ (1 + (3+h)*a v)*Real.exp (-((3+h)*v)) +
          ((3+h)*(3+2*h)/2)*(a v)^2*Real.exp (-(2*v)) := by positivity
      linarith only [hsum])
    rw [Real.sqrt_one] at H
    exact sub_nonneg.mpr H
  exact shortGap_mixed_lt_of_profile_margin_of_slopes hα hβ hαβ
    hf hmargin hj hj' hj'' hz hz' hc

/-- Reduce the short-gap sign for the actual matrix kernel to curvature of
the scalar gap profile and the estimates for the marginal correction. -/
theorem logKernel_gap_mixed_of_profile_margin {p : ℕ} (hp : 11 ≤ p) {u v ε : ℝ}
    (hu : 4 ≤ u) (huv : u < v) :
    let h := rate p
    let d := v-u
    let a := upperTailGap h
    let P := fun x ↦ a x / Real.sqrt (W h x)
    let V := fun x ↦ 1 / Real.sqrt (W h x)
    let Z := fun x ↦ Real.sqrt (X h x)
    let α := fun x ↦ deriv P x / P x
    let β := fun x ↦ deriv V x / V x
    let m := 3 / 2 + h
    let Q := shortGapQuotient h
    let ξ := c h*a v*Real.exp (-((u+v)/2))
    0 ≤ shortGapF h d →
    ε < deriv (deriv (shortGapF h)) d - (α u - β v) * deriv (shortGapF h) d -
      (β v - m) * Real.exp (-m * d) * (deriv Q u + (α u + m) * Q u) →
    0 ≤ deriv (shortGapJ h) d →
    deriv (shortGapJ h) d / 2 ≤ deriv (deriv (shortGapJ h)) d →
    0 ≤ deriv Z v →
    deriv Z v * deriv (shortGapJ h) d ≤ ξ*(1/2-α u)*(1/2-α v) →
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < -(P u * V v * ε) := by
  dsimp only
  have hp₀ : 0 < p := by omega
  have hreal : (11 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hh := rate_pos hp₀
  have hhp : rate p ≤ 3 / 11 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hreal
  have hv : 4 ≤ v := hu.trans huv.le
  have hn₁ := shortGapNormalization_bounds hh hhp hu
  have hn₂ := shortGapNormalization_bounds hh hhp hv
  let P : ℝ → ℝ := fun t ↦ upperTailGap (rate p) t / Real.sqrt (W (rate p) t)
  let V : ℝ → ℝ := fun t ↦ 1 / Real.sqrt (W (rate p) t)
  let α := deriv P u / P u
  let β := deriv V v / V v
  have hα₀ : 0 ≤ α := hn₁.1
  have hα₁ : α < 1 / 7 := hn₁.2.1
  have hβ₀ : β < 0 := hn₂.2.2.2
  have hβv : -(1 / v) ≤ β := hn₂.2.2.1
  have hβ : -(1 / 4 : ℝ) ≤ β := by
    have H := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hv
    linarith only [H, hβv]
  have hdiff : α - β ≤ 1 / 2 := by linarith only [hα₁, hβ]
  exact logKernel_gap_mixed_of_profile_margin_of_slopes hp (by linarith) huv hα₀ hβ₀.le hdiff

/-- Ordinary curvature and slope estimates give the short-gap mixed sign. -/
theorem logKernel_shortGap_mixed_of_scalar_bounds {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu : 4 ≤ u) (huv : u < v) :
    let h := rate p
    let d := v-u
    let a := upperTailGap h
    let P := fun x ↦ a x / Real.sqrt (W h x)
    let V := fun x ↦ 1 / Real.sqrt (W h x)
    let Z := fun x ↦ Real.sqrt (X h x)
    let α := fun x ↦ deriv P x / P x
    let ξ := c h*a v*Real.exp (-((u+v)/2))
    0 ≤ shortGapF h d →
    deriv (shortGapF h) d ≤ 0 →
    1/200 < deriv (deriv (shortGapF h)) d →
    0 ≤ deriv (shortGapJ h) d →
    deriv (shortGapJ h) d / 2 ≤ deriv (deriv (shortGapJ h)) d →
    0 ≤ deriv Z v →
    deriv Z v * deriv (shortGapJ h) d ≤ ξ*(1/2-α u)*(1/2-α v) →
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < -(P u*V v/200) := by
  dsimp only
  intro hf hf' hf'' hj' hj'' hz' hc
  have hp₀ : 0 < p := by omega
  have hpR : (11 : ℝ) ≤ p := by exact_mod_cast hp
  have hh := rate_pos hp₀
  have hhmax : rate p ≤ 3 / 11 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpR
  have hα := (shortGapNormalization_bounds hh hhmax hu).1
  have hβ := (shortGapNormalization_bounds hh hhmax (hu.trans huv.le)).2.2.2.le
  change 0 ≤ deriv (fun s ↦ upperTailGap (rate p) s / Real.sqrt (W (rate p) s)) u /
    (upperTailGap (rate p) u / Real.sqrt (W (rate p) u)) at hα
  change deriv (fun s ↦ 1 / Real.sqrt (W (rate p) s)) v /
    (1 / Real.sqrt (W (rate p) v)) ≤ 0 at hβ
  have hq := shortGapQuotient_nonneg hh hu
  have hq' : 0 ≤ deriv (shortGapQuotient (rate p)) u :=
    shortGapQuotient_deriv_nonneg hp₀ (by linarith)
  have hm : 0 ≤ 3 / 2 + rate p := by linarith
  have hfTerm := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hβ.trans hα)) hf'
  have hqTerm := mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hβ.trans hm))
      (Real.exp_pos (-(3 / 2 + rate p) * (v - u))).le)
    (add_nonneg hq' (mul_nonneg (add_nonneg hα hm) hq))
  have hsign := logKernel_gap_mixed_of_profile_margin hp hu huv (ε := 1 / 200)
    hf (by dsimp only; linarith only [hf'', hfTerm, hqTerm]) hj' hj'' hz' hc
  exact hsign.trans_eq (by ring)

#print axioms logKernel_shortGap_mixed_of_scalar_bounds

/-- The three scalar profile inequalities suffice everywhere on the
short-gap strip, including arbitrarily close to the diagonal. -/
theorem logKernel_shortGap_mixed_of_profile {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu : 4 ≤ u) (huv : u < v) (hdmax : v-u ≤ 2) :
    let h := rate p
    let F := shortGapF h
    let d := v-u
    0 ≤ F d →
    deriv F d ≤ 0 →
    1/200 < deriv (deriv F) d →
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v <
      -(upperTailGap h u / Real.sqrt (W h u) * (1 / Real.sqrt (W h v)) / 200) := by
  dsimp only
  intro hf hf' hf''
  let h := rate p
  let d := v-u
  let Z : ℝ → ℝ := fun x ↦ Real.sqrt (X h x)
  let P : ℝ → ℝ := fun x ↦ upperTailGap h x / Real.sqrt (W h x)
  let α : ℝ → ℝ := fun x ↦ deriv P x / P x
  have hp₀ : 0 < p := by omega
  have hh := rate_pos hp₀
  have hhp : h ≤ 3/11 := by
    have hpR : (11 : ℝ) ≤ p := by exact_mod_cast hp
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpR
  have hd : 0 < d := sub_pos.mpr huv
  have hv : 4 ≤ v := hu.trans huv.le
  have he : shortGapJ h =ᶠ[𝓝 d] RefinedBMV.PositiveCenter.shortGapJ p := by
    filter_upwards [eventually_gt_nhds hd] with t ht
    rw [shortGapJ_eq_sqrt hp₀ ht]
    have hj : 0 ≤ shortGapJ h t :=
      div_nonneg (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)) (gap_pos hp₀ ht).le
    have hsq : shortGapJ h t ^ 2 = c h*Real.exp t*compositionMoment p 0 t :=
      shortGapJ_sq hp₀ ht
    change shortGapJ h t = Real.sqrt (c h*Real.exp t*compositionMoment p 0 t)
    rw [← hsq, Real.sqrt_sq hj]
  refine logKernel_shortGap_mixed_of_scalar_bounds hp hu huv hf hf' hf'' ?_ ?_ ?_ ?_
  · rw [he.deriv_eq]
    exact (shortGapJ_deriv_pos hp₀ hd.le).le
  · rw [he.deriv_eq, he.deriv.deriv_eq]
    exact shortGapJ_deriv_half_le_second hp₀ hd.le
  · exact (shortGap_marginal_deriv_bounds hh hhp hv).1
  · change deriv Z v * deriv (shortGapJ h) d ≤ _
    rw [he.deriv_eq]
    have hαu : α u ≤ 1/7 := (shortGapNormalization_bounds hh hhp hu).2.1.le
    have hαv : α v ≤ 1/7 := (shortGapNormalization_bounds hh hhp hv).2.1.le
    have hj := shortGapJ_deriv_le hp hd.le
    have hc := shortGap_correction_lt hh hhp hu hd hdmax hj hαu hαv
    dsimp only [d] at hc
    rw [show u+(v-u) = v by ring, show -(u+v)/2 = -((u+v)/2) by ring] at hc
    exact hc.le

#print axioms logKernel_shortGap_mixed_of_profile

/-- For gaps at least two, the profile margin alone suffices for the mixed sign. -/
theorem logKernel_middleGap_mixed_of_profile_margin {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu : 4 ≤ u) (hd : 2 ≤ v - u) :
    let h := rate p
    let d := v - u
    let P := fun t ↦ upperTailGap h t / Real.sqrt (W h t)
    let V := fun t ↦ 1 / Real.sqrt (W h t)
    let α := fun t ↦ deriv P t / P t
    let β := fun t ↦ deriv V t / V t
    let m := 3 / 2 + h
    let Q := shortGapQuotient h
    0 ≤ shortGapF h d →
    0 < deriv (deriv (shortGapF h)) d - (α u - β v) * deriv (shortGapF h) d -
      (β v - m) * Real.exp (-m * d) * (deriv Q u + (α u + m) * Q u) →
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  dsimp only
  intro hf hmargin
  let h := rate p
  let d := v - u
  let a := upperTailGap h
  let Z : ℝ → ℝ := fun t ↦ Real.sqrt (X h t)
  let P : ℝ → ℝ := fun t ↦ a t / Real.sqrt (W h t)
  let α : ℝ → ℝ := fun t ↦ deriv P t / P t
  have hp₀ : 0 < p := by omega
  have hpR : (11 : ℝ) ≤ p := by exact_mod_cast hp
  have hh := rate_pos hp₀
  have hhmax : h ≤ 3 / 11 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpR
  have huv : u < v := by linarith
  have hv : 4 ≤ v := hu.trans huv.le
  have hαu : α u ≤ 1 / 7 := (shortGapNormalization_bounds hh hhmax hu).2.1.le
  have hαv : α v ≤ 1 / 7 := (shortGapNormalization_bounds hh hhmax hv).2.1.le
  have he : shortGapJ h =ᶠ[𝓝 d] RefinedBMV.PositiveCenter.shortGapJ p := by
    filter_upwards [eventually_gt_nhds (show 0 < d by dsimp [d]; linarith)] with t ht
    rw [shortGapJ_eq_sqrt hp₀ ht]
    have hj : 0 ≤ shortGapJ h t :=
      div_nonneg (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)) (gap_pos hp₀ ht).le
    have hsq : shortGapJ h t ^ 2 = c h * Real.exp t * compositionMoment p 0 t :=
      shortGapJ_sq hp₀ ht
    change shortGapJ h t = Real.sqrt (c h * Real.exp t * compositionMoment p 0 t)
    rw [← hsq, Real.sqrt_sq hj]
  have hj' : 0 ≤ deriv (shortGapJ h) d := by
    rw [he.deriv_eq]
    exact (shortGapJ_deriv_pos hp₀ (by dsimp [d]; linarith)).le
  have hj'' : deriv (shortGapJ h) d / 2 ≤ deriv (deriv (shortGapJ h)) d := by
    rw [he.deriv_eq, he.deriv.deriv_eq]
    exact shortGapJ_deriv_half_le_second hp₀ (by dsimp [d]; linarith)
  have hz' : 0 ≤ deriv Z v := (shortGap_marginal_deriv_bounds hh hhmax hv).1
  have hc := middleGap_correction_lt hh hhmax hu hd (shortGapJ_deriv_le_of_two_le hp hd) hαu hαv
  change deriv Z (u+d) * deriv (shortGapJ h) d <
    c h * a (u+d) * Real.exp (-(u+(u+d))/2) * (1/2-α u) * (1/2-α v) at hc
  rw [show u+d = v by dsimp [d]; ring, show -(u+v)/2 = -((u+v)/2) by ring] at hc
  have hsign := logKernel_gap_mixed_of_profile_margin hp hu huv (ε := 0)
    hf hmargin hj' hj'' hz' hc.le
  simpa only [mul_zero, neg_zero] using hsign

/-- Positivity of the short-gap profile follows from the difference of
squares and holds on the full positive gap axis. -/
theorem shortGapF_pos {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) :
    0 < shortGapF (3/(p : ℝ)) t := by
  let h := rate p
  let g : ℝ := 3+h
  let k : ℝ := 3+2*h
  let a := upperTailGap h t
  let r := (1-Real.exp (-(g*t)))/a
  let e := Real.exp (3*t/2)
  let l := e*r
  let j := shortGapJ h t
  have hh : 0 < h := rate_pos hp
  have hg : 0 < g := by dsimp [g]; linarith
  have ha : 0 < a := gap_pos hp ht
  have he : 0 < e := Real.exp_pos _
  have hq : Real.exp (-(g*t)) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos hg ht))
  have hr : 0 < r := div_pos (sub_pos.mpr hq) ha
  have hl : 0 < l := mul_pos he hr
  have hj : 0 ≤ j :=
    div_nonneg (mul_nonneg he.le (Real.sqrt_nonneg _)) ha.le
  have hmean : expGapMean g t ≤ expGapMean h t := by
    unfold expGapMean
    apply intervalIntegral.integral_mono_on zero_le_one
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
    intro s hs
    have hhg : h ≤ g := by dsimp [g]; linarith
    exact Real.exp_le_exp.mpr (neg_le_neg
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hhg ht.le) hs.1))
  have hrbound : r ≤ g := by
    apply (div_le_iff₀ ha).2
    have hcomparison := mul_le_mul_of_nonneg_left hmean (mul_nonneg hg.le ht.le)
    have h₁ := expGapMean_eq hg t
    have h₂ := expGapMean_eq hh t
    unfold upperTailGap at h₁
    have heq := (div_eq_iff hg.ne').mp h₁
    dsimp only [a]
    rw [heq, h₂]
    linarith only [hcomparison, show t*expGapMean g t*g = g*t*expGapMean g t by ring,
      show g*(t*expGapMean h t) = g*t*expGapMean h t by ring]
  have he₂ : e^2 = Real.exp (3*t) := by
    unfold e
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hx : 0 ≤ X h t := (X_pos hp ht).le
  have hsq :
      l^2-j^2 = c h*Real.exp t + Real.exp (-(h*t))/a*(g-r) := by
    calc
      _ = c h*(Real.exp (3*t)*Real.exp (-(2*t))) +
          (Real.exp (3*t)*Real.exp (-(g*t)))/a*(g-r) := by
        change (e*r)^2 - (e*Real.sqrt (X h t)/a)^2 = _
        rw [mul_pow e r, div_pow (e*Real.sqrt (X h t)), mul_pow e, Real.sq_sqrt hx, he₂]
        unfold X upperTailLambda
        dsimp only [r, g, a, c] at *
        field_simp [ha.ne'] <;> ring
      _ = _ := by
        rw [← Real.exp_add, show 3*t + -(2*t) = t by ring,
          ← Real.exp_add, show 3*t + -(g*t) = -(h*t) by dsimp [g]; ring]
  have hc : 0 < c h := by unfold c; positivity
  have hbudget : c h*Real.exp t ≤ l^2-j^2 := by
    rw [hsq]
    linarith only [mul_nonneg (div_nonneg (Real.exp_pos (-(h*t))).le ha.le)
      (sub_nonneg.mpr hrbound)]
  have hjl : j ≤ l := by
    have hpos : 0 < c h*Real.exp t := mul_pos hc (Real.exp_pos _)
    by_contra! hcontra
    have hneg := mul_pos (sub_pos.mpr hcontra) (add_pos_of_nonneg_of_pos hj hl)
    nlinarith only [hneg, hbudget, hpos]
  have hlbound : l ≤ g*e := by
    rw [mul_comm g]
    exact mul_le_mul_of_nonneg_left hrbound he.le
  have hbig : c h*Real.exp t ≤ (l-j)*(2*g*e) := calc
    _ ≤ l^2-j^2 := hbudget
    _ = (l-j)*(l+j) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (sub_nonneg.mpr hjl)
  have hmul : (2*g*e)*(k/4*Real.exp (-t/2)) = c h*Real.exp t := by
    have hE : e*Real.exp (-t/2) = Real.exp t := by
      unfold e
      rw [← Real.exp_add, show 3*t/2 + -t/2 = t by ring]
    calc
      _ = c h*(e*Real.exp (-t/2)) := by dsimp [c, g, k]; ring
      _ = _ := by rw [hE]
  have hdiff : k/4*Real.exp (-t/2) ≤ l-j := by
    apply le_of_mul_le_mul_left _ (show 0 < 2*g*e by positivity)
    rw [hmul, mul_comm (2*g*e)]
    exact hbig
  have hm : Real.exp (-((3/2+h)*t)) ≤ Real.exp (-t/2) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonneg hh.le ht.le, ht]
  have hk : 1 < k := by dsimp [k]; linarith
  have hsmall : Real.exp (-((3/2+h)*t))/4 < k/4*Real.exp (-t/2) := calc
    _ ≤ Real.exp (-t/2)/4 := by linarith
    _ < _ := by
      have h := mul_lt_mul_of_pos_right hk (Real.exp_pos (-t/2))
      linarith
  unfold shortGapF
  rw [mul_div_assoc]
  change 0 < l - Real.exp (-((3/2+h)*t))/4 - j
  linarith

#print axioms shortGapF_pos

/-- The one-variable profile including the constant part of the geometric correction. -/
noncomputable def middleGapProfile (h t : ℝ) : ℝ :=
  shortGapF h t + Real.exp (-((3 / 2 + h) * t)) / 4

/-- Two gap-dependent estimates suffice for the mixed sign uniformly in the lower coordinate. -/
theorem logKernel_middleGap_mixed_of_recentered {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu : 4 ≤ u) (hd : 2 ≤ v - u)
    (hslope : middleGapSlopeBudget (rate p) (v - u) ≤
      -deriv (middleGapProfile (rate p)) (v - u))
    (hcurve : 0 < deriv (deriv (middleGapProfile (rate p))) (v - u)) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  let h := rate p
  let d := v - u
  let m : ℝ := 3 / 2 + h
  let E : ℝ → ℝ := fun t ↦ Real.exp (-(m * t))
  let P : ℝ → ℝ := fun t ↦ upperTailGap h t / Real.sqrt (W h t)
  let V : ℝ → ℝ := fun t ↦ 1 / Real.sqrt (W h t)
  let α : ℝ → ℝ := fun t ↦ deriv P t / P t
  let β : ℝ → ℝ := fun t ↦ deriv V t / V t
  let r := upperTailSlope h u * (1 - Real.exp (-((3 + h) * u)))
  have hp₀ : 0 < p := by omega
  have hh := rate_pos hp₀
  have hpR : (11 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hhmax : h ≤ 3 / 11 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpR
  have hu₀ : 0 < u := by linarith
  have hd₀ : 0 < d := by dsimp [d]; linarith
  have huv : u < v := sub_pos.mp hd₀
  have hv : 4 ≤ v := hu.trans huv.le
  have hv₀ : 0 < v := hu₀.trans huv
  have hvd : u + d = v := by dsimp [d]; ring
  have huNorm : 0 ≤ α u ∧ α u < 1 / 7 ∧ -(1 / u) ≤ β u ∧ β u < 0 :=
    shortGapNormalization_bounds hh hhmax hu
  have hvNorm : 0 ≤ α v ∧ α v < 1 / 7 ∧ -(1 / v) ≤ β v ∧ β v < 0 :=
    shortGapNormalization_bounds hh hhmax hv
  have hβbound {t : ℝ} (ht : 4 ≤ t) : upperTailSlope h t / 2 ≤ -β t := by
    have ht' : β t ≤ -upperTailSlope h t / 2 := shortGap_upperLogDeriv_le hh hhmax ht
    simpa only [neg_div, neg_neg] using neg_le_neg ht'
  have hlog : α u - β u = upperTailSlope h u := shortGapNormalization_logDiff hh hu₀
  have hq : shortGapQuotient h u = 1 / 4 - r := shortGapQuotient_recenter hh hu₀
  have hqd : -deriv (shortGapQuotient h) u + (α u + m) * r =
      (3 / 2 + β u + upperTailSlope (3 + h) u) * r :=
    shortGapQuotient_recentered_slope hh hu₀ hlog
  have hgeo : (m - β v) * (3 / 2 + β u + upperTailSlope (3 + h) u) * r * E d ≤
      -β v * middleGapSlopeBudget h d := by
    have hbv' : upperTailSlope h (u + d) / 2 ≤ -β v := by simpa only [hvd] using hβbound hv
    have hbvmax : -β v ≤ 1 / (u + d) := by
      rw [hvd]
      simpa only [neg_neg] using neg_le_neg hvNorm.2.2.1
    have hb := middleGap_geometric_absorption hh hhmax hu hd (hβbound hu) hbv' hbvmax
    change (m + -β v) * (3 / 2 - (-β u) + upperTailSlope (3 + h) u) * r * E d ≤ _ at hb
    simpa only [← sub_eq_add_neg, sub_neg_eq_add] using hb
  have hE (t : ℝ) : HasDerivAt E (-m * E t) t := by
    convert (((hasDerivAt_id' t).const_mul m).neg.exp) using 1 <;> simp [E] <;> ring
  have hfirst {t : ℝ} (ht : 0 < t) : deriv (middleGapProfile h) t =
      deriv (shortGapF h) t + (-m * E t) / 4 :=
    (((shortGapF_contDiffAt hp₀ ht).differentiableAt (by norm_num)).hasDerivAt.add
      ((hE t).div_const 4)).deriv
  have hsecond : deriv (deriv (middleGapProfile h)) d =
      deriv (deriv (shortGapF h)) d + m ^ 2 * E d / 4 := by
    have heq : deriv (middleGapProfile h) =ᶠ[𝓝 d]
        fun t ↦ deriv (shortGapF h) t + (-m * E t) / 4 := by
      filter_upwards [eventually_gt_nhds hd₀] with t ht using hfirst ht
    have hFd : DifferentiableAt ℝ (deriv (shortGapF h)) d :=
      ((shortGapF_contDiffAt hp₀ hd₀).derivWithin (m := 1) (by norm_num)).differentiableAt one_ne_zero
    rw [heq.deriv_eq, (hFd.hasDerivAt.fun_add (((hE d).const_mul (-m)).div_const 4)).deriv]
    ring
  have hB : 0 ≤ middleGapSlopeBudget h d := by
    have ha := (gap_pos hp₀ hd₀).le
    have hmd : 0 ≤ 3 / 2 + h + 1 / (4 + d) := by positivity
    unfold middleGapSlopeBudget
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hmd)
      (add_nonneg zero_le_one (div_nonneg ha (by norm_num)))) (Real.exp_pos _).le
  change middleGapSlopeBudget h d ≤ -deriv (middleGapProfile h) d at hslope
  change 0 < deriv (deriv (middleGapProfile h)) d at hcurve
  have hβ : 0 ≤ -β v := neg_nonneg.mpr hvNorm.2.2.2.le
  have hgain := mul_le_mul_of_nonneg_left hslope hβ
  have hα := mul_nonneg huNorm.1 (hB.trans hslope)
  have hαβ : 0 ≤ α u * (-β v) * E d / 4 :=
    div_nonneg (mul_nonneg (mul_nonneg huNorm.1 hβ) (Real.exp_pos _).le) (by norm_num)
  refine logKernel_middleGap_mixed_of_profile_margin hp hu hd (shortGapF_pos hp₀ hd₀).le ?_
  rw [neg_mul]
  change 0 < deriv (deriv (shortGapF h)) d - (α u - β v) * deriv (shortGapF h) d -
    (β v - m) * E d * (deriv (shortGapQuotient h) u + (α u + m) * shortGapQuotient h u)
  have hrecenter : deriv (deriv (shortGapF h)) d - (α u - β v) * deriv (shortGapF h) d -
        (β v - m) * E d * (deriv (shortGapQuotient h) u + (α u + m) * shortGapQuotient h u) =
      deriv (deriv (middleGapProfile h)) d - (α u - β v) * deriv (middleGapProfile h) d +
        α u * (-β v) * E d / 4 -
        (m - β v) * ((3 / 2 + β u + upperTailSlope (3 + h) u) * r) * E d := by
    rw [hfirst hd₀, hsecond, hq, ← hqd]
    ring
  rw [hrecenter]
  nlinarith only [hcurve, hgeo, hgain, hα, hαβ]

#print axioms logKernel_middleGap_mixed_of_recentered

/-- A certificate for the scalar discriminant and endpoint slope implies the
strict mixed sign on the entire unbounded short-gap region. -/
theorem logKernel_shortGap_mixed_of_certificate {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu : 4 ≤ u) (huv : u < v) (hdmax : v-u ≤ 2)
    (hD : ∀ t ∈ Set.Icc (0 : ℝ) 2,
      0 < shortGapProfileD (shortGapProfileT p (3/(p : ℝ))) (shortGapProfileU p) t)
    (hH : 0 < shortGapProfileH (shortGapProfileT p (3/(p : ℝ))) (shortGapProfileU p) 2) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  let h := rate p
  let d := v-u
  let J := RefinedBMV.PositiveCenter.shortGapJ p
  have hp₀ : 0 < p := by omega
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp₀
  have hh := rate_pos hp₀
  have hd : 0 < d := sub_pos.mpr huv
  have hcancel : h*(p : ℝ) = 3 := div_mul_cancel₀ 3 hpR.ne'
  have hprofile := shortGapProfile_of_signs hh hcancel (shortGapProfileU_contDiff p)
    (shortGapProfileU_pos hp₀) (J := J) rfl (shortGapJ_deriv_pos hp₀ (by norm_num)) hD hH
  have he : shortGapF h =ᶠ[𝓝 d] fun t ↦ shortGapProfileT p h t - J t := by
    filter_upwards [eventually_gt_nhds hd] with t ht
    unfold shortGapF shortGapProfileT
    rw [show Real.exp (3*t/2)*(1-Real.exp (-((3+h)*t)))/upperTailGap h t =
      h*∑ l ∈ Finset.range (p+1), Real.exp ((h*l-3/2)*t) from shortGap_geometric_eq hp₀ ht]
    have hj : 0 ≤ shortGapJ h t :=
      div_nonneg (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)) (gap_pos hp₀ ht).le
    have hsq : shortGapJ h t ^ 2 = c h * Real.exp t * compositionMoment p 0 t :=
      shortGapJ_sq hp₀ ht
    have hj_eq : shortGapJ h t = J t := by
      unfold J
      rw [shortGapJ_eq_sqrt hp₀ ht]
      change shortGapJ h t = Real.sqrt (c h * Real.exp t * compositionMoment p 0 t)
      rw [← hsq, Real.sqrt_sq hj]
    rw [hj_eq, show -((3/2+h)*t) = -(3/2+h)*t by ring]
  have hs := hprofile d ⟨hd.le, hdmax⟩
  have hf' : deriv (shortGapF h) d ≤ 0 := he.deriv_eq.trans_lt hs.2 |>.le
  have hf'' : 1/200 < deriv (deriv (shortGapF h)) d :=
    hs.1.trans_eq he.deriv.deriv_eq.symm
  have hm := logKernel_shortGap_mixed_of_profile hp hu huv hdmax
    (shortGapF_pos hp₀ hd).le hf' hf''
  refine hm.trans_le (neg_nonpos.mpr ?_)
  exact div_nonneg (mul_nonneg (div_nonneg (gap_pos hp₀ (by linarith)).le (Real.sqrt_nonneg _))
    (one_div_nonneg.mpr (Real.sqrt_nonneg _))) (by norm_num)

#print axioms logKernel_shortGap_mixed_of_certificate

/-- The mixed derivative is strictly negative throughout the unbounded short-gap strip. -/
theorem logKernel_shortGap_mixed {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu : 4 ≤ u) (huv : u < v) (hdmax : v - u ≤ 2) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  obtain ⟨hD, hH⟩ := shortGap_profile_signs hp
  exact logKernel_shortGap_mixed_of_certificate hp hu huv hdmax hD hH

#print axioms logKernel_shortGap_mixed

end RefinedBMV.PositiveCenter.CompactGap
