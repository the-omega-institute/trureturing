/- GID: D5/S3/Weil/ZetaAnalytic/RoucheZeroCount
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaAnalytic/RoucheZeroCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Rectangle Rouche stability preserves the zero count with multiplicity. -/

import D5.S3.Weil.ZetaPntBase.Rectangle
import D5.S3.Weil.ZetaAnalytic.RectangleLogDeriv
import Mathlib.Topology.Connected.TotallyDisconnected

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Complex Set Topology BigOperators

noncomputable section

namespace D5.S3.Weil.ZetaAnalytic.RoucheZeroCount

private def straightLine (f g : ℂ → ℂ) (t : ℝ) : ℂ → ℂ :=
  fun s => g s + (t : ℂ) * (f s - g s)

private theorem g_ne_zero_on_rectangleBorder
    {f g : ℂ → ℂ} {z w : ℂ}
    (hbdry : ∀ s ∈ RectangleBorder z w, ‖f s - g s‖ < ‖g s‖) :
    ∀ s ∈ RectangleBorder z w, g s ≠ 0 := by
  intro s hs hgs
  have hlt := hbdry s hs
  rw [hgs, norm_zero] at hlt
  exact (not_lt_of_ge (norm_nonneg _)) hlt

private theorem f_ne_zero_on_rectangleBorder
    {f g : ℂ → ℂ} {z w : ℂ}
    (hbdry : ∀ s ∈ RectangleBorder z w, ‖f s - g s‖ < ‖g s‖) :
    ∀ s ∈ RectangleBorder z w, f s ≠ 0 := by
  intro s hs hfs
  have hlt := hbdry s hs
  rw [hfs, zero_sub, norm_neg] at hlt
  exact (lt_irrefl _) hlt

/-- The straight-line homotopy between `g` and `f` does not vanish on the
rectangle boundary under the strict Rouche estimate. -/
theorem homotopy_nonvanishing_on_rectangleBorder
    {f g : ℂ → ℂ} {z w : ℂ}
    (hbdry : ∀ s ∈ RectangleBorder z w, ‖f s - g s‖ < ‖g s‖) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ RectangleBorder z w,
      g s + (t : ℂ) * (f s - g s) ≠ 0 := by
  intro t ht s hs hzero
  have ht_norm : ‖(t : ℂ)‖ ≤ 1 := by
    calc
      ‖(t : ℂ)‖ = |t| := Complex.norm_real t
      _ = t := abs_of_nonneg ht.1
      _ ≤ 1 := ht.2
  have hg_eq : g s = -(t : ℂ) * (f s - g s) := by
    linear_combination hzero
  have hle : ‖g s‖ ≤ ‖f s - g s‖ := by
    calc
      ‖g s‖ = ‖-(t : ℂ) * (f s - g s)‖ := congrArg norm hg_eq
      _ = ‖(t : ℂ)‖ * ‖f s - g s‖ := by rw [norm_mul, norm_neg]
      _ ≤ ‖f s - g s‖ := mul_le_of_le_one_left (norm_nonneg _) ht_norm
  exact (not_lt_of_ge hle) (hbdry s hs)

private theorem straightLine_analyticOnNhd
    {f g : ℂ → ℂ} {z w : ℂ}
    (hf : AnalyticOnNhd ℂ f (Rectangle z w))
    (hg : AnalyticOnNhd ℂ g (Rectangle z w)) (t : ℝ) :
    AnalyticOnNhd ℂ (straightLine f g t) (Rectangle z w) := by
  change AnalyticOnNhd ℂ (fun s => g s + (t : ℂ) * (f s - g s)) (Rectangle z w)
  have heq : (fun s => g s + (t : ℂ) * (f s - g s)) =
      g + (fun _ : ℂ => (t : ℂ)) * (f - g) := by
    funext s
    rfl
  rw [heq]
  exact hg.add (analyticOnNhd_const.mul (hf.sub hg))

private theorem straightLine_deriv
    {f g : ℂ → ℂ} {z w s : ℂ}
    (hf : AnalyticOnNhd ℂ f (Rectangle z w))
    (hg : AnalyticOnNhd ℂ g (Rectangle z w))
    (hs : s ∈ Rectangle z w) (t : ℝ) :
    deriv (straightLine f g t) s =
      deriv g s + (t : ℂ) * (deriv f s - deriv g s) := by
  have hfa := (hf s hs).differentiableAt
  have hga := (hg s hs).differentiableAt
  exact (hga.hasDerivAt.add
    ((hfa.hasDerivAt.sub hga.hasDerivAt).const_mul (t : ℂ))).deriv

private def explicitLogDeriv (f g : ℂ → ℂ) (t : ℝ) (s : ℂ) : ℂ :=
  (deriv g s + (t : ℂ) * (deriv f s - deriv g s)) /
    (g s + (t : ℂ) * (f s - g s))

private theorem explicitLogDeriv_eq
    {f g : ℂ → ℂ} {z w s : ℂ}
    (hf : AnalyticOnNhd ℂ f (Rectangle z w))
    (hg : AnalyticOnNhd ℂ g (Rectangle z w))
    (hs : s ∈ Rectangle z w) (t : ℝ) :
    explicitLogDeriv f g t s = logDeriv (straightLine f g t) s := by
  rw [logDeriv_apply, straightLine_deriv hf hg hs t]
  rfl

private theorem explicitLogDeriv_continuousOn
    {f g : ℂ → ℂ} {z w : ℂ}
    (hf : AnalyticOnNhd ℂ f (Rectangle z w))
    (hg : AnalyticOnNhd ℂ g (Rectangle z w))
    (hbdry : ∀ s ∈ RectangleBorder z w, ‖f s - g s‖ < ‖g s‖) :
    ContinuousOn (fun p : ℝ × ℂ => explicitLogDeriv f g p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ RectangleBorder z w) := by
  have hfR : ContinuousOn f (Rectangle z w) := hf.continuousOn
  have hgR : ContinuousOn g (Rectangle z w) := hg.continuousOn
  have hdfR : ContinuousOn (deriv f) (Rectangle z w) := hf.deriv.continuousOn
  have hdgR : ContinuousOn (deriv g) (Rectangle z w) := hg.deriv.continuousOn
  have hmaps : MapsTo (fun p : ℝ × ℂ => p.2)
      (Icc (0 : ℝ) 1 ×ˢ RectangleBorder z w) (Rectangle z w) :=
    fun p hp => rectangleBorder_subset_rectangle z w hp.2
  have hfP := hfR.comp continuous_snd.continuousOn hmaps
  have hgP := hgR.comp continuous_snd.continuousOn hmaps
  have hdfP := hdfR.comp continuous_snd.continuousOn hmaps
  have hdgP := hdgR.comp continuous_snd.continuousOn hmaps
  have htP : ContinuousOn (fun p : ℝ × ℂ => (p.1 : ℂ))
      (Icc (0 : ℝ) 1 ×ˢ RectangleBorder z w) :=
    (Complex.continuous_ofReal.comp continuous_fst).continuousOn
  change ContinuousOn
    (fun p : ℝ × ℂ =>
      (deriv g p.2 + (p.1 : ℂ) * (deriv f p.2 - deriv g p.2)) /
        (g p.2 + (p.1 : ℂ) * (f p.2 - g p.2))) _
  apply ContinuousOn.div
  · exact hdgP.add (htP.mul (hdfP.sub hdgP))
  · exact hgP.add (htP.mul (hfP.sub hgP))
  · intro p hp
    exact homotopy_nonvanishing_on_rectangleBorder hbdry p.1 hp.1 p.2 hp.2

private theorem continuousOn_parametric_intervalIntegral
    {F : ℝ → ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hF : ContinuousOn F.uncurry (Icc (0 : ℝ) 1 ×ˢ Icc a b)) :
    ContinuousOn (fun t => ∫ x in a..b, F t x) (Icc (0 : ℝ) 1) := by
  let Fc : ℝ → ℝ → ℂ := fun t x =>
    F (Set.projIcc 0 1 zero_le_one t) (Set.projIcc a b hab x)
  have hproj : Continuous (fun p : ℝ × ℝ =>
      ((Set.projIcc 0 1 zero_le_one p.1 : ℝ),
        (Set.projIcc a b hab p.2 : ℝ))) := by
    fun_prop
  have hFc : Continuous Fc.uncurry := by
    rw [← continuousOn_univ]
    exact hF.comp hproj.continuousOn (fun p _ =>
      ⟨(Set.projIcc 0 1 zero_le_one p.1).property,
        (Set.projIcc a b hab p.2).property⟩)
  have hci : Continuous (fun t => ∫ x in a..b, Fc t x) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hFc a b
  apply hci.continuousOn.congr
  intro t ht
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ Icc a b := by simpa [uIcc_of_le hab] using hx
  simp only [Fc]
  rw [Set.projIcc_of_mem zero_le_one ht, Set.projIcc_of_mem hab hx']

set_option maxHeartbeats 257750 in
private theorem continuousOn_explicitLogDeriv_intervalIntegral
    {f g : ℂ → ℂ} {z w : ℂ}
    (hf : AnalyticOnNhd ℂ f (Rectangle z w))
    (hg : AnalyticOnNhd ℂ g (Rectangle z w))
    (hbdry : ∀ s ∈ RectangleBorder z w, ‖f s - g s‖ < ‖g s‖)
    {a b : ℝ} (hab : a ≤ b) {curve : ℝ → ℂ}
    (hcurve : Continuous curve)
    (hcurve_mem : ∀ x ∈ Icc a b, curve x ∈ RectangleBorder z w) :
    ContinuousOn (fun t => ∫ x in a..b, explicitLogDeriv f g t (curve x))
      (Icc (0 : ℝ) 1) := by
  refine continuousOn_parametric_intervalIntegral
    (F := fun t x => explicitLogDeriv f g t (curve x)) hab ?_
  let q : ℝ × ℝ → ℝ × ℂ := fun p => (p.1, curve p.2)
  have hq : Continuous q := continuous_fst.prodMk (hcurve.comp continuous_snd)
  have hqmaps : MapsTo q (Icc (0 : ℝ) 1 ×ˢ Icc a b)
      (Icc (0 : ℝ) 1 ×ˢ RectangleBorder z w) :=
    fun p hp => ⟨hp.1, hcurve_mem p.2 hp.2⟩
  exact (explicitLogDeriv_continuousOn hf hg hbdry).comp hq.continuousOn hqmaps

private theorem continuousOn_rectangleIntegral_explicitLogDeriv
    {f g : ℂ → ℂ} {z w : ℂ}
    (hre : z.re < w.re) (him : z.im < w.im)
    (hf : AnalyticOnNhd ℂ f (Rectangle z w))
    (hg : AnalyticOnNhd ℂ g (Rectangle z w))
    (hbdry : ∀ s ∈ RectangleBorder z w, ‖f s - g s‖ < ‖g s‖) :
    ContinuousOn
      (fun t : ℝ => RectangleIntegral' (explicitLogDeriv f g t) z w)
      (Icc (0 : ℝ) 1) := by
  have hbot := continuousOn_explicitLogDeriv_intervalIntegral hf hg hbdry hre.le
    (curve := fun x : ℝ => (x : ℂ) + (z.im : ℂ) * I) (by fun_prop)
    (fun x hx => Or.inl (Or.inl (Or.inl ⟨by simpa [uIcc_of_le hre.le] using hx, by simp⟩)))
  have htop := continuousOn_explicitLogDeriv_intervalIntegral hf hg hbdry hre.le
    (curve := fun x : ℝ => (x : ℂ) + (w.im : ℂ) * I) (by fun_prop)
    (fun x hx => Or.inl (Or.inr ⟨by simpa [uIcc_of_le hre.le] using hx, by simp⟩))
  have hleft := continuousOn_explicitLogDeriv_intervalIntegral hf hg hbdry him.le
    (curve := fun y : ℝ => (z.re : ℂ) + (y : ℂ) * I) (by fun_prop)
    (fun y hy => Or.inl (Or.inl (Or.inr ⟨by simp, by simpa [uIcc_of_le him.le] using hy⟩)))
  have hright := continuousOn_explicitLogDeriv_intervalIntegral hf hg hbdry him.le
    (curve := fun y : ℝ => (w.re : ℂ) + (y : ℂ) * I) (by fun_prop)
    (fun y hy => Or.inr ⟨by simp, by simpa [uIcc_of_le him.le] using hy⟩)
  change ContinuousOn (fun t : ℝ => (1 / (2 * Real.pi * I)) •
    ((∫ x in z.re..w.re, explicitLogDeriv f g t (x + z.im * I)) -
      (∫ x in z.re..w.re, explicitLogDeriv f g t (x + w.im * I)) +
      I • (∫ y in z.im..w.im, explicitLogDeriv f g t (w.re + y * I)) -
      I • (∫ y in z.im..w.im, explicitLogDeriv f g t (z.re + y * I)))) _
  fun_prop

/-- The normalized rectangle integral of the logarithmic derivative along the
straight-line homotopy is continuous in the homotopy parameter. -/
theorem continuousOn_rectangleIntegral_logDeriv_straightLine
    {f g : ℂ → ℂ} {z w : ℂ}
    (hre : z.re < w.re) (him : z.im < w.im)
    (hf : AnalyticOnNhd ℂ f (Rectangle z w))
    (hg : AnalyticOnNhd ℂ g (Rectangle z w))
    (hbdry : ∀ s ∈ RectangleBorder z w, ‖f s - g s‖ < ‖g s‖) :
    ContinuousOn
      (fun t : ℝ => RectangleIntegral'
        (fun s => logDeriv (fun u => g u + (t : ℂ) * (f u - g u)) s) z w)
      (Icc (0 : ℝ) 1) := by
  apply (continuousOn_rectangleIntegral_explicitLogDeriv hre him hf hg hbdry).congr
  intro t ht
  exact RectangleIntegral'_congr fun s hs =>
    (explicitLogDeriv_eq hf hg (rectangleBorder_subset_rectangle z w hs) t).symm

private theorem rectangle_zero_count_eq_of_continuous_logDeriv_integral
    {f g : ℂ → ℂ} {z w : ℂ}
    (hre : z.re < w.re) (him : z.im < w.im)
    (hf : AnalyticOnNhd ℂ f (Rectangle z w))
    (hg : AnalyticOnNhd ℂ g (Rectangle z w))
    (hbdry : ∀ s ∈ RectangleBorder z w, ‖f s - g s‖ < ‖g s‖)
    (Zf Zg : Finset ℂ)
    (hZf : ∀ s ∈ Rectangle z w, f s = 0 ↔ s ∈ Zf)
    (hZfsub : (Zf : Set ℂ) ⊆ Rectangle z w)
    (hZg : ∀ s ∈ Rectangle z w, g s = 0 ↔ s ∈ Zg)
    (hZgsub : (Zg : Set ℂ) ⊆ Rectangle z w)
    (hcont : ContinuousOn
      (fun t : ℝ => RectangleIntegral'
        (fun s => logDeriv (straightLine f g t) s) z w)
      (Icc (0 : ℝ) 1)) :
    ∑ ρ ∈ Zf, analyticOrderNatAt f ρ =
      ∑ ρ ∈ Zg, analyticOrderNatAt g ρ := by
  let J : ℝ → ℂ := fun t => RectangleIntegral'
    (fun s => logDeriv (straightLine f g t) s) z w
  have hline0 : straightLine f g 0 = g := by
    funext s
    simp [straightLine]
  have hline1 : straightLine f g 1 = f := by
    funext s
    simp [straightLine]
  have hmaps : MapsTo J (Icc (0 : ℝ) 1) (Set.range ((↑) : ℤ → ℂ)) := by
    intro t ht
    have harg := Zeta23.Analytic.rectangleIntegral'_mul_logDeriv'
      (g := fun _ : ℂ => (1 : ℂ)) hre.le him.le
      (straightLine_analyticOnNhd hf hg t) analyticOnNhd_const
      (homotopy_nonvanishing_on_rectangleBorder hbdry t ht)
    let Zt := (Zeta23.Analytic.finite_zeros_rectangle
      (straightLine_analyticOnNhd hf hg t)
      (rectangleBorder_subset_rectangle z w
        (show z ∈ RectangleBorder z w from
          Or.inl (Or.inl (Or.inl ⟨left_mem_uIcc, rfl⟩))))
      (homotopy_nonvanishing_on_rectangleBorder hbdry t ht z
        (Or.inl (Or.inl (Or.inl ⟨left_mem_uIcc, rfl⟩))))).toFinset
    refine ⟨(∑ ρ ∈ Zt, analyticOrderNatAt (straightLine f g t) ρ : ℕ), ?_⟩
    simpa [J, Zt, straightLine] using harg.symm
  have hdisc : IsDiscrete (Set.range ((↑) : ℤ → ℂ)) :=
    Complex.isClosedEmbedding_intCast.isEmbedding.isInducing.isDiscrete_range
  have hconst : J 0 = J 1 :=
    isPreconnected_Icc.constant_of_mapsTo hdisc hcont hmaps
      (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
      (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
  have harg_g := Zeta23.Analytic.rectangleIntegral'_mul_logDeriv
    (g := fun _ : ℂ => (1 : ℂ)) hre.le him.le hg analyticOnNhd_const
    (g_ne_zero_on_rectangleBorder hbdry) Zg hZg hZgsub
  have harg_f := Zeta23.Analytic.rectangleIntegral'_mul_logDeriv
    (g := fun _ : ℂ => (1 : ℂ)) hre.le him.le hf analyticOnNhd_const
    (f_ne_zero_on_rectangleBorder hbdry) Zf hZf hZfsub
  have hcount_g : J 0 = (↑(∑ ρ ∈ Zg, analyticOrderNatAt g ρ) : ℂ) := by
    change RectangleIntegral' (fun s => logDeriv (straightLine f g 0) s) z w = _
    rw [hline0]
    simpa using harg_g
  have hcount_f : J 1 = (↑(∑ ρ ∈ Zf, analyticOrderNatAt f ρ) : ℂ) := by
    change RectangleIntegral' (fun s => logDeriv (straightLine f g 1) s) z w = _
    rw [hline1]
    simpa using harg_f
  have hcast : (↑(∑ ρ ∈ Zf, analyticOrderNatAt f ρ) : ℂ) =
      (↑(∑ ρ ∈ Zg, analyticOrderNatAt g ρ) : ℂ) := by
    rw [← hcount_f, ← hcount_g]
    exact hconst.symm
  exact_mod_cast hcast

/-- **Rouche zero-count stability on a rectangle.** If `f - g` is strictly
smaller than `g` on the boundary, then `f` and `g` have the same number of
zeros in the rectangle, counted with analytic multiplicity. -/
theorem rectangle_zero_count_eq_of_norm_sub_lt
    {f g : ℂ → ℂ} {z w : ℂ}
    (hre : z.re < w.re) (him : z.im < w.im)
    (hf : AnalyticOnNhd ℂ f (Rectangle z w))
    (hg : AnalyticOnNhd ℂ g (Rectangle z w))
    (hbdry : ∀ s ∈ RectangleBorder z w, ‖f s - g s‖ < ‖g s‖)
    (Zf Zg : Finset ℂ)
    (hZf : ∀ s ∈ Rectangle z w, (f s = 0 ↔ s ∈ Zf))
    (hZfsub : (Zf : Set ℂ) ⊆ Rectangle z w)
    (hZg : ∀ s ∈ Rectangle z w, (g s = 0 ↔ s ∈ Zg))
    (hZgsub : (Zg : Set ℂ) ⊆ Rectangle z w) :
    ∑ ρ ∈ Zf, analyticOrderNatAt f ρ =
      ∑ ρ ∈ Zg, analyticOrderNatAt g ρ := by
  exact rectangle_zero_count_eq_of_continuous_logDeriv_integral
    hre him hf hg hbdry Zf Zg hZf hZfsub hZg hZgsub
    (continuousOn_rectangleIntegral_logDeriv_straightLine hre him hf hg hbdry)

-- Fidelity witnesses: the common constant-function instance satisfies every
-- hypothesis, and the selected rectangle is inhabited.
example :
    ∃ (f g : ℂ → ℂ) (z w : ℂ) (Zf Zg : Finset ℂ),
      z.re < w.re ∧ z.im < w.im ∧
      AnalyticOnNhd ℂ f (Rectangle z w) ∧
      AnalyticOnNhd ℂ g (Rectangle z w) ∧
      (∀ s ∈ RectangleBorder z w, ‖f s - g s‖ < ‖g s‖) ∧
      (∀ s ∈ Rectangle z w, (f s = 0 ↔ s ∈ Zf)) ∧
      ((Zf : Set ℂ) ⊆ Rectangle z w) ∧
      (∀ s ∈ Rectangle z w, (g s = 0 ↔ s ∈ Zg)) ∧
      ((Zg : Set ℂ) ⊆ Rectangle z w) := by
  refine ⟨fun _ => 1, fun _ => 1, 0, 1 + I, ∅, ∅, ?_⟩
  simp [analyticOnNhd_const]

example : (0 : ℂ) ∈ Rectangle 0 (1 + I) := by
  exact left_mem_rect 0 (1 + I)

#print axioms homotopy_nonvanishing_on_rectangleBorder
#print axioms continuousOn_rectangleIntegral_logDeriv_straightLine
#print axioms rectangle_zero_count_eq_of_norm_sub_lt

end D5.S3.Weil.ZetaAnalytic.RoucheZeroCount
