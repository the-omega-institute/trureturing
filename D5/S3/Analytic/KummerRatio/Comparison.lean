/- GID: D5/S3/Analytic/KummerRatio/Comparison
   generality: G
   mirror-B: D5/B/S3/Analytic/KummerRatio/Comparison
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.Deriv.MeanValue, mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Deriv, mathlib/module/Mathlib.Analysis.SpecialFunctions.ExpDeriv]
   utility: none
   digest: Logarithmic derivative ordering and strict ratio comparison for positive Kummer solutions. -/

import D5.S3.Analytic.KummerRatio.Defs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Set Filter Topology

namespace D5.S3.Analytic.KummerRatio.Comparison

/-- A positive family of regular solutions of the confluent hypergeometric equation. -/
structure SolutionFamily (c : ℝ) (y dy ddy : ℝ → ℝ → ℝ) : Prop where
  pos : ∀ s, 0 < s → ∀ x, 0 ≤ x → 0 < y s x
  continuous : ∀ s, 0 < s → ContinuousOn (y s) (Ici 0)
  continuous_deriv : ∀ s, 0 < s → ContinuousOn (dy s) (Ici 0)
  hasDeriv : ∀ s, 0 < s → ∀ x, 0 < x → HasDerivAt (y s) (dy s x) x
  hasDeriv_deriv : ∀ s, 0 < s → ∀ x, 0 < x → HasDerivAt (dy s) (ddy s x) x
  ode : ∀ s, 0 < s → ∀ x, 0 < x →
    x * ddy s x + (c - x) * dy s x - s * y s x = 0

private noncomputable def h (y dy : ℝ → ℝ → ℝ) (s x : ℝ) : ℝ := dy s x / y s x
private noncomputable def p (c x : ℝ) : ℝ := x ^ c * Real.exp (-x)
private noncomputable def μ (c : ℝ) (y : ℝ → ℝ → ℝ) (u v x : ℝ) : ℝ :=
  p c x * y u x * y v x

variable {c : ℝ} {y dy ddy : ℝ → ℝ → ℝ}

private lemma p_pos (hx : 0 < x) : 0 < p c x := by
  exact mul_pos (Real.rpow_pos_of_pos hx _) (Real.exp_pos _)

private lemma p_continuous (hc : 0 < c) : Continuous (p c) := by
  exact (Real.continuous_rpow_const hc.le).mul (Real.continuous_exp.comp continuous_id.neg)

private lemma p_zero (hc : 0 < c) : p c 0 = 0 := by
  simp [p, Real.zero_rpow hc.ne']

private lemma p_deriv (hx : 0 < x) :
    HasDerivAt (p c) ((c / x - 1) * p c x) x := by
  have hd := (Real.hasDerivAt_rpow_const (p := c) (Or.inl hx.ne')).mul
    ((hasDerivAt_id x).neg.exp)
  apply hd.congr_deriv
  dsimp [p]
  rw [Real.rpow_sub hx c 1, Real.rpow_one]
  field_simp
  ring

private lemma h_continuous (H : SolutionFamily c y dy ddy) (hs : 0 < s) :
    ContinuousOn (h y dy s) (Ici 0) :=
  (H.continuous_deriv s hs).div (H.continuous s hs) (fun x hx => (H.pos s hs x hx).ne')

private lemma h_deriv (H : SolutionFamily c y dy ddy) (hs : 0 < s) (hx : 0 < x) :
    HasDerivAt (h y dy s)
      (s / x - (c / x - 1) * h y dy s x - (h y dy s x) ^ 2) x := by
  have hy := (H.pos s hs x hx.le).ne'
  have he : ddy s x = (s * y s x - (c - x) * dy s x) / x := by
    apply (eq_div_iff hx.ne').2
    nlinarith [H.ode s hs x hx]
  apply ((H.hasDeriv_deriv s hs x hx).div (H.hasDeriv s hs x hx) hy).congr_deriv
  dsimp [h]
  rw [he]
  field_simp

private lemma μ_pos (H : SolutionFamily c y dy ddy) (hu : 0 < u) (hv : 0 < v)
    (hx : 0 < x) : 0 < μ c y u v x :=
  mul_pos (mul_pos (p_pos hx) (H.pos u hu x hx.le)) (H.pos v hv x hx.le)

private lemma μ_continuous (H : SolutionFamily c y dy ddy) (hc : 0 < c)
    (hu : 0 < u) (hv : 0 < v) : ContinuousOn (μ c y u v) (Ici 0) :=
  ((p_continuous hc).continuousOn.mul (H.continuous u hu)).mul (H.continuous v hv)

private lemma μ_deriv (H : SolutionFamily c y dy ddy) (hu : 0 < u) (hv : 0 < v)
    (hx : 0 < x) : HasDerivAt (μ c y u v)
      ((c / x - 1 + h y dy u x + h y dy v x) * μ c y u v x) x := by
  apply (((p_deriv hx).mul (H.hasDeriv u hu x hx)).mul (H.hasDeriv v hv x hx)).congr_deriv
  dsimp [μ, h]
  field_simp [(H.pos u hu x hx.le).ne', (H.pos v hv x hx.le).ne']

private lemma weighted_difference_deriv (H : SolutionFamily c y dy ddy)
    (hu : 0 < u) (hv : 0 < v) (hx : 0 < x) :
    HasDerivAt (fun t => μ c y u v t * (h y dy v t - h y dy u t))
      ((v - u) / x * μ c y u v x) x := by
  apply ((μ_deriv H hu hv hx).mul ((h_deriv H hv hx).sub (h_deriv H hu hx))).congr_deriv
  simp only [Pi.sub_apply]
  ring

private lemma h_lt (H : SolutionFamily c y dy ddy) (hc : 0 < c)
    (hu : 0 < u) (huv : u < v) (hx : 0 < x) : h y dy u x < h y dy v x := by
  have hv : 0 < v := hu.trans huv
  let F : ℝ → ℝ := fun t => μ c y u v t * (h y dy v t - h y dy u t)
  have hF : StrictMonoOn F (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact (μ_continuous H hc hu hv).mul ((h_continuous H hv).sub (h_continuous H hu))
    · intro t ht
      have ht : 0 < t := by simpa using ht
      rw [(weighted_difference_deriv H hu hv ht).deriv]
      exact mul_pos (div_pos (sub_pos.mpr huv) ht) (μ_pos H hu hv ht)
  have h0 : F 0 = 0 := by simp [F, μ, p_zero hc]
  have hh := hF (show (0 : ℝ) ∈ Ici 0 from by simp) hx.le hx
  rw [h0] at hh
  exact sub_pos.mp ((mul_pos_iff_of_pos_left (μ_pos H hu hv hx)).mp hh)


private noncomputable def w (y dy : ℝ → ℝ → ℝ) (δ s x : ℝ) : ℝ :=
  h y dy (s + δ) x - h y dy s x

private lemma w_deriv (H : SolutionFamily c y dy ddy) (hs : 0 < s) (hδ : 0 < δ)
    (hx : 0 < x) : HasDerivAt (w y dy δ s)
      (δ / x - (c / x - 1 + h y dy (s + δ) x + h y dy s x) * w y dy δ s x) x := by
  apply ((h_deriv H (by linarith : 0 < s + δ) hx).sub (h_deriv H hs hx)).congr_deriv
  dsimp [w]
  ring

private lemma weighted_increment_deriv (H : SolutionFamily c y dy ddy)
    (ha : 0 < a) (hab : a < b) (hδ : 0 < δ) (hx : 0 < x) :
    HasDerivAt (fun t => μ c y b (b + δ) t * (w y dy δ b t - w y dy δ a t))
      (μ c y b (b + δ) x *
        ((h y dy (a + δ) x + h y dy a x) - (h y dy (b + δ) x + h y dy b x)) *
        w y dy δ a x) x := by
  have hb : 0 < b := ha.trans hab
  apply ((μ_deriv H hb (by linarith : 0 < b + δ) hx).mul
    ((w_deriv H hb hδ hx).sub (w_deriv H ha hδ hx))).congr_deriv
  simp only [Pi.sub_apply]
  ring

private lemma w_lt (H : SolutionFamily c y dy ddy) (hc : 0 < c)
    (ha : 0 < a) (hab : a < b) (hδ : 0 < δ) (hx : 0 < x) :
    w y dy δ b x < w y dy δ a x := by
  have hb : 0 < b := ha.trans hab
  have had : 0 < a + δ := by linarith
  have hbd : 0 < b + δ := by linarith
  let F : ℝ → ℝ := fun t => μ c y b (b + δ) t * (w y dy δ b t - w y dy δ a t)
  have hF : StrictAntiOn F (Ici 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici 0)
    · exact (μ_continuous H hc hb hbd).mul
        (((h_continuous H hbd).sub (h_continuous H hb)).sub
          ((h_continuous H had).sub (h_continuous H ha)))
    · intro t ht
      have ht : 0 < t := by simpa using ht
      rw [(weighted_increment_deriv H ha hab hδ ht).deriv]
      apply mul_neg_of_neg_of_pos
      · apply mul_neg_of_pos_of_neg (μ_pos H hb hbd ht)
        exact sub_neg.mpr (add_lt_add (h_lt H hc had (by linarith) ht) (h_lt H hc ha hab ht))
      · exact sub_pos.mpr (h_lt H hc ha (by linarith : a < a + δ) ht)
  have h0 : F 0 = 0 := by simp [F, μ, p_zero hc]
  have hh := hF (show (0 : ℝ) ∈ Ici 0 from by simp) hx.le hx
  rw [h0] at hh
  have hm := μ_pos H hb hbd hx
  change μ c y b (b + δ) x * (w y dy δ b x - w y dy δ a x) < 0 at hh
  nlinarith

/-- Upper-parameter product ratios of any positive regular solution family strictly decrease. -/
theorem solution_ratio_strictAntiOn (H : SolutionFamily c y dy ddy) (hc : 0 < c)
    (ha : 0 < a) (hab : a < b) (hδ : 0 < δ) :
    StrictAntiOn (fun x => y (b + δ) x * y a x / (y (a + δ) x * y b x)) (Ioi 0) := by
  have hb : 0 < b := ha.trans hab
  have had : 0 < a + δ := by linarith
  have hbd : 0 < b + δ := by linarith
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · exact (((H.continuous (b + δ) hbd).mul (H.continuous a ha)).div
      ((H.continuous (a + δ) had).mul (H.continuous b hb))
      (fun x hx => mul_ne_zero (H.pos (a + δ) had x hx).ne' (H.pos b hb x hx).ne')).mono
        (by
          intro x hx
          exact Set.mem_Ici.mpr (Set.mem_Ioi.mp hx).le)
  · intro x hx
    have hx : 0 < x := by simpa using hx
    have hyA := H.pos a ha x hx.le
    have hyB := H.pos b hb x hx.le
    have hyAD := H.pos (a + δ) had x hx.le
    have hyBD := H.pos (b + δ) hbd x hx.le
    have hd := ((H.hasDeriv (b + δ) hbd x hx).mul (H.hasDeriv a ha x hx)).div
      ((H.hasDeriv (a + δ) had x hx).mul (H.hasDeriv b hb x hx))
      (mul_ne_zero hyAD.ne' hyB.ne')
    have hd' : HasDerivAt (fun t => y (b + δ) t * y a t / (y (a + δ) t * y b t))
        ((y (b + δ) x * y a x / (y (a + δ) x * y b x)) *
          (w y dy δ b x - w y dy δ a x)) x := by
      apply hd.congr_deriv
      simp only [Pi.mul_apply]
      dsimp [w, h]
      field_simp
      ring
    rw [hd'.deriv]
    exact mul_neg_of_pos_of_neg (div_pos (mul_pos hyBD hyA) (mul_pos hyAD hyB))
      (sub_neg.mpr (w_lt H hc ha hab hδ hx))

end D5.S3.Analytic.KummerRatio.Comparison
