/- GID: D5/S3/Quantum/PositiveResolvent/MasterStripPoles
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Classify and remove the two simple poles of the logarithmic master strip kernel. -/

import D5.S3.Weil.ZetaPntBase.ResidueRectangles
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

open Set Complex Filter Asymptotics
open scoped Topology Interval

namespace D5.S3.Quantum.PositiveResolvent.MasterStripPoles

noncomputable def stripPoleKernel (x : ℝ) (z : ℂ) : ℂ :=
  1 / (((x : ℂ) + Complex.exp z) * (z - (Real.pi : ℂ) * I))

noncomputable def logPole (x : ℝ) : ℂ := (Real.log x : ℂ) + (Real.pi : ℂ) * I

private lemma exp_logPole {x : ℝ} (hx : 0 < x) : Complex.exp (logPole x) = -(x : ℂ) := by
  rw [logPole, Complex.exp_add, Complex.exp_pi_mul_I, ← Complex.ofReal_exp,
    Real.exp_log hx]
  ring

theorem exp_upper_boundary (s : ℝ) :
    Complex.exp ((s : ℂ) + (2 * Real.pi : ℂ) * I) = (Real.exp s : ℂ) := by
  have hc : (2 * Real.pi : ℂ) = 2 * (Real.pi : ℂ) := by norm_cast
  rw [Complex.exp_add, hc, Complex.exp_two_pi_mul_I, mul_one, ← Complex.ofReal_exp]

theorem logistic_zero_iff {x : ℝ} (hx : 0 < x) {z : ℂ}
    (hlo : 0 ≤ z.im) (hhi : z.im ≤ 2 * Real.pi) :
    (x : ℂ) + Complex.exp z = 0 ↔ z = logPole x := by
  constructor
  · intro h
    have hs : Real.sin z.im = 0 := by
      have hh := congrArg Complex.im h
      simp only [add_im, ofReal_im, exp_im, zero_im, zero_add] at hh
      exact (mul_eq_zero.mp hh).resolve_left (Real.exp_pos z.re).ne'
    have him : z.im = Real.pi := by
      by_cases hz : z.im = 0
      · have hh := congrArg Complex.re h
        simp only [add_re, ofReal_re, Complex.exp_re, hz, Real.cos_zero, mul_one, zero_re] at hh
        linarith [Real.exp_pos z.re]
      by_cases ht : z.im = 2 * Real.pi
      · have hh := congrArg Complex.re h
        simp only [add_re, ofReal_re, Complex.exp_re, ht, Real.cos_two_pi, mul_one, zero_re] at hh
        linarith [Real.exp_pos z.re]
      have he : Real.sin (z.im - Real.pi) = 0 := by rw [Real.sin_sub_pi, hs, neg_zero]
      have hloStrict : 0 < z.im := lt_of_le_of_ne hlo (Ne.symm hz)
      have hhiStrict : z.im < 2 * Real.pi := lt_of_le_of_ne hhi ht
      have heq := (Real.sin_eq_zero_iff_of_lt_of_lt
        (by linarith : -Real.pi < z.im - Real.pi)
        (by linarith : z.im - Real.pi < Real.pi)).mp he
      linarith
    have hre : z.re = Real.log x := by
      have hh := congrArg Complex.re h
      simp only [add_re, ofReal_re, Complex.exp_re, him, Real.cos_pi, mul_neg, mul_one, zero_re] at hh
      have he : Real.exp z.re = x := by linarith
      rw [← Real.exp_log hx] at he
      exact Real.exp_injective he
    apply Complex.ext <;> simp [logPole, hre, him]
  · rintro rfl
    rw [exp_logPole hx, add_neg_cancel]

private lemma stripPoleKernel_differentiableAt {x : ℝ} (hx : 0 < x) {z : ℂ}
    (hlo : 0 ≤ z.im) (hhi : z.im ≤ 2 * Real.pi)
    (hp : z ≠ (Real.pi : ℂ) * I) (hq : z ≠ logPole x) :
    DifferentiableAt ℂ (stripPoleKernel x) z := by
  exact (differentiableAt_const _).div
    (((differentiableAt_const _).add Complex.differentiableAt_exp).mul
      ((differentiableAt_id).sub (differentiableAt_const _)))
    (mul_ne_zero (mt (logistic_zero_iff hx hlo hhi).mp hq) (sub_ne_zero.mpr hp))



private lemma log_ne_zero {x : ℝ} (hx : 0 < x) (hne : x ≠ 1) : Real.log x ≠ 0 := by
  intro h
  have he := Real.exp_log hx
  rw [h, Real.exp_zero] at he
  exact hne he.symm

private lemma pole_ne {x : ℝ} (hx : 0 < x) (hne : x ≠ 1) :
    logPole x ≠ (Real.pi : ℂ) * I := by
  intro h
  have hh := congrArg Complex.re h
  simp only [logPole, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, zero_mul, sub_zero, add_zero] at hh
  exact log_ne_zero hx hne hh

private lemma principal_bound {F f : ℂ → ℂ} {p : ℂ}
    (hd : DifferentiableAt ℂ F p)
    (he : f =ᶠ[𝓝[≠] p] fun z => F z / (z - p)) :
    (f - fun z => F p / (z - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  have hb : dslope F p =O[𝓝[≠] p] (1 : ℂ → ℂ) :=
    ((continuousAt_dslope_same.mpr hd).tendsto.mono_left
    nhdsWithin_le_nhds).isBigO_one ℂ
  refine hb.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [he, self_mem_nhdsWithin] with z hz hzp
  have hn : z ≠ p := hzp
  simp only [Pi.sub_apply, hz, dslope_of_ne F hn, slope, smul_eq_mul]
  simp only [div_eq_mul_inv, vsub_eq_sub]
  ring

private noncomputable def expPoleFactor (x : ℝ) (z : ℂ) : ℂ :=
  1 / (dslope Complex.exp (logPole x) z * (z - (Real.pi : ℂ) * I))

private lemma expPoleFactor_value {x : ℝ} (hx : 0 < x) :
    expPoleFactor x (logPole x) = -1 / ((x : ℂ) * (Real.log x : ℂ)) := by
  rw [expPoleFactor, dslope_same, Complex.deriv_exp, exp_logPole hx]
  simp [logPole, div_eq_mul_inv, mul_comm]

private lemma expPoleFactor_differentiableAt {x : ℝ} (hx : 0 < x) (hne : x ≠ 1) :
    DifferentiableAt ℂ (expPoleFactor x) (logPole x) := by
  have hd : Differentiable ℂ (dslope Complex.exp (logPole x)) := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope (by simp)).mpr
      Complex.differentiable_exp.differentiableOn
  apply (differentiableAt_const _).div
    ((hd _).mul ((differentiableAt_id).sub (differentiableAt_const _)))
  apply mul_ne_zero
  · simp [dslope_same, Complex.deriv_exp, exp_logPole hx, hx.ne']
  · exact sub_ne_zero.mpr (pole_ne hx hne)

private lemma stripPoleKernel_logPole_factor {x : ℝ} (hx : 0 < x) (z : ℂ) :
    stripPoleKernel x z = expPoleFactor x z / (z - logPole x) := by
  have hf := sub_smul_dslope Complex.exp (logPole x) z
  rw [smul_eq_mul, exp_logPole hx] at hf
  unfold stripPoleKernel expPoleFactor
  rw [div_div]
  congr 1
  rw [mul_comm _ (z - logPole x), ← mul_assoc, hf]
  ring

theorem principal_part_at_pi {x : ℝ} (_hx : 0 < x) (hne : x ≠ 1) :
    (stripPoleKernel x - fun z =>
      (1 / ((x : ℂ) - 1)) / (z - (Real.pi : ℂ) * I))
      =O[𝓝[≠] ((Real.pi : ℂ) * I)] (1 : ℂ → ℂ) := by
  have hd : DifferentiableAt ℂ (fun z : ℂ => 1 / ((x : ℂ) + Complex.exp z))
      ((Real.pi : ℂ) * I) := by
    apply (differentiableAt_const _).div
      ((differentiableAt_const _).add Complex.differentiableAt_exp)
    simpa [Complex.exp_pi_mul_I, sub_eq_add_neg] using
      (sub_ne_zero.mpr (show (x : ℂ) ≠ 1 by exact_mod_cast hne))
  have he : stripPoleKernel x =ᶠ[𝓝[≠] ((Real.pi : ℂ) * I)]
      fun z => (1 / ((x : ℂ) + Complex.exp z)) / (z - (Real.pi : ℂ) * I) := by
    exact Eventually.of_forall fun z => by simp [stripPoleKernel, div_eq_mul_inv, mul_comm]
  simpa [Complex.exp_pi_mul_I, sub_eq_add_neg] using principal_bound hd he

theorem principal_part_at_logPole {x : ℝ} (hx : 0 < x) (hne : x ≠ 1) :
    (stripPoleKernel x - fun z =>
      (-1 / ((x : ℂ) * (Real.log x : ℂ))) / (z - logPole x))
      =O[𝓝[≠] (logPole x)] (1 : ℂ → ℂ) := by
  have he : stripPoleKernel x =ᶠ[𝓝[≠] (logPole x)]
      fun z => expPoleFactor x z / (z - logPole x) := by
    exact Eventually.of_forall (stripPoleKernel_logPole_factor hx)
  simpa only [expPoleFactor_value hx] using
    principal_bound (expPoleFactor_differentiableAt hx hne) he



private lemma rectangle_two_poles {f : ℂ → ℂ} {z w p q A B : ℂ}
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im) (hpq : p ≠ q)
    (hp : Rectangle z w ∈ 𝓝 p) (hq : Rectangle z w ∈ 𝓝 q)
    (hd : HolomorphicOn f (Rectangle z w \ {p, q}))
    (hbp : (f - fun s => A / (s - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ))
    (hbq : (f - fun s => B / (s - q)) =O[𝓝[≠] q] (1 : ℂ → ℂ)) :
    RectangleIntegral f z w = 2 * (Real.pi : ℂ) * I * (A + B) := by
  classical
  let f0 : ℂ → ℂ := f - fun s => A / (s - p)
  let g : ℂ → ℂ := Function.update f0 p (limUnder (𝓝[≠] p) f0)
  obtain ⟨U, hU, hUb⟩ := IsBigO_to_BddAbove hbp
  let V := (U ∩ Rectangle z w) ∩ {q}ᶜ
  have hV : V ∈ 𝓝 p := inter_mem (inter_mem hU hp) (isOpen_ne.mem_nhds hpq)
  have hdV : HolomorphicOn f0 (V \ {p}) := by
    intro s hs
    have hsp : s ≠ p := hs.2
    have hsq : s ≠ q := hs.1.2
    refine ((hd s ?_).mono ?_).sub ?_
    · exact ⟨hs.1.1.2, by simp [hsp, hsq]⟩
    · intro r hr
      exact ⟨hr.1.1.2, by simpa only [mem_insert_iff, mem_singleton_iff, not_or]
        using (And.intro hr.2 (show r ≠ q from hr.1.2))⟩
    · exact (differentiableWithinAt_const _).div
        ((differentiableWithinAt_id).sub (differentiableWithinAt_const _))
        (sub_ne_zero.mpr hsp)
  have hsub : V \ {p} ⊆ U \ {p} := fun s hs => ⟨hs.1.1.1, hs.2⟩
  have hbV : BddAbove (norm ∘ f0 '' (V \ {p})) := hUb.mono (image_mono hsub)
  have hgV : HolomorphicOn g V :=
    Complex.differentiableOn_update_limUnder_of_bddAbove hV hdV hbV
  have hge {s : ℂ} (hs : s ≠ p) : g =ᶠ[𝓝 s] f0 := by
    filter_upwards [isOpen_ne.mem_nhds hs] with r hr
    exact Function.update_of_ne hr _ _
  have hg : HolomorphicOn g (Rectangle z w \ {q}) := by
    intro s hs
    by_cases hsp : s = p
    · subst s
      exact (hgV.differentiableAt hV).differentiableWithinAt
    · have hh : HolomorphicOn f0 (Rectangle z w \ {p, q}) := by
        refine hd.sub ?_
        intro r hr
        have hrp : r ≠ p := by
          intro he
          exact hr.2 (by simp [he])
        exact (differentiableWithinAt_const _).div
          ((differentiableWithinAt_id).sub (differentiableWithinAt_const _))
          (sub_ne_zero.mpr hrp)
      have hh1 := hh s ⟨hs.1, by simp [hsp, hs.2]⟩
      exact (hh1.mono_of_mem_nhdsWithin (by
        filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
          (isOpen_ne.mem_nhds hsp)] with r hr hrp
        exact ⟨hr.1, by simp [hrp, hr.2]⟩)).congr_of_eventuallyEq
          ((hge hsp).filter_mono nhdsWithin_le_nhds) (Function.update_of_ne hsp _ _)
  have ha : (fun s : ℂ => A / (s - p)) =O[𝓝[≠] q] (1 : ℂ → ℂ) :=
    (((continuousAt_const.div (continuousAt_id.sub continuousAt_const)
      (sub_ne_zero.mpr hpq.symm)).tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℂ)
  have hb : (g - fun s => B / (s - q)) =O[𝓝[≠] q] (1 : ℂ → ℂ) := by
    refine (hbq.sub ha).congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [(hge hpq.symm).filter_mono nhdsWithin_le_nhds] with s hs
    simp only [Pi.sub_apply, hs, f0]
    ring
  have hgI := ResidueTheoremOnRectangleWithSimplePole' hre him hq hg hb
  have hpB := not_mem_rectangleBorder_of_rectangle_mem_nhds hp
  have hfEq : EqOn f (g + fun s => A / (s - p)) (RectangleBorder z w) := by
    intro s hs
    have hsp : s ≠ p := fun he => hpB (he ▸ hs)
    simp [g, Function.update_of_ne hsp, f0]
  have hAg : HolomorphicOn (fun s : ℂ => A / (s - p)) (Rectangle z w \ {p}) := by
    intro s hs
    exact (differentiableWithinAt_const _).div
      ((differentiableWithinAt_id).sub (differentiableWithinAt_const _))
      (sub_ne_zero.mpr hs.2)
  have hadd := RectangleBorderIntegrable.add
    (hg.rectangleBorderIntegrable' hq) (hAg.rectangleBorderIntegrable' hp)
  have hAi := ResidueTheoremInRectangle (c := A) hre him hp
  have hsum : RectangleIntegral' f z w = A + B := by
    rw [RectangleIntegral'_congr hfEq, RectangleIntegral', hadd, smul_add]
    change RectangleIntegral' g z w + RectangleIntegral' (fun s => A / (s - p)) z w = _
    rw [hgI, hAi, add_comm]
  change (1 / (2 * (Real.pi : ℂ) * I)) * RectangleIntegral f z w = A + B at hsum
  have hc : 2 * (Real.pi : ℂ) * I ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
  have hv := (div_eq_iff hc).mp (by simpa [div_eq_mul_inv, mul_comm] using hsum)
  simpa [mul_comm] using hv



theorem stripPoleKernel_rectangle {x T : ℝ} (hx : 0 < x) (hne : x ≠ 1)
    (hT : 0 < T) (hlog : |Real.log x| < T) :
    RectangleIntegral (stripPoleKernel x) (-T : ℂ) ((T : ℂ) + (2 * Real.pi : ℂ) * I) =
      2 * (Real.pi : ℂ) * I *
        (1 / ((x : ℂ) - 1) - 1 / ((x : ℂ) * (Real.log x : ℂ))) := by
  have hre : (-T : ℂ).re ≤ ((T : ℂ) + (2 * Real.pi : ℂ) * I).re := by
    simp
    linarith
  have him : (-T : ℂ).im ≤ ((T : ℂ) + (2 * Real.pi : ℂ) * I).im := by
    simpa using (show (0 : ℝ) ≤ 2 * Real.pi by positivity)
  have hp : Rectangle (-T : ℂ) ((T : ℂ) + (2 * Real.pi : ℂ) * I)
      ∈ 𝓝 ((Real.pi : ℂ) * I) := by
    rw [rectangle_mem_nhds_iff, uIoo_of_le hre, uIoo_of_le him]
    have hh : (-T < 0 ∧ 0 < T) ∧ (0 < Real.pi ∧ Real.pi < 2 * Real.pi) := by
      constructor <;> constructor <;> linarith [Real.pi_pos]
    simpa [mem_reProdIm, mem_Ioo] using hh
  have hq : Rectangle (-T : ℂ) ((T : ℂ) + (2 * Real.pi : ℂ) * I)
      ∈ 𝓝 (logPole x) := by
    rw [rectangle_mem_nhds_iff, uIoo_of_le hre, uIoo_of_le him]
    have hl := abs_lt.mp hlog
    have hh : (-T < Real.log x ∧ Real.log x < T) ∧ (0 < Real.pi ∧ Real.pi < 2 * Real.pi) := by
      constructor <;> constructor <;> linarith [Real.pi_pos]
    simpa [logPole, mem_reProdIm, mem_Ioo] using hh
  have hd : HolomorphicOn (stripPoleKernel x)
      (Rectangle (-T : ℂ) ((T : ℂ) + (2 * Real.pi : ℂ) * I) \ {(Real.pi : ℂ) * I, logPole x}) := by
    intro z hz
    have hpz : z ≠ (Real.pi : ℂ) * I := by
      intro he
      exact hz.2 (by simp [he])
    have hqz : z ≠ logPole x := by
      intro he
      exact hz.2 (by simp [he])
    have hiz := hz.1.2
    rw [uIcc_of_le him] at hiz
    simp at hiz
    exact (stripPoleKernel_differentiableAt hx hiz.1 hiz.2 hpz hqz).differentiableWithinAt
  have hh := rectangle_two_poles hre him (pole_ne hx hne).symm hp hq hd
    (principal_part_at_pi hx hne) (principal_part_at_logPole hx hne)
  simpa only [neg_div, sub_eq_add_neg] using hh

end D5.S3.Quantum.PositiveResolvent.MasterStripPoles
