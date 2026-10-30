/- GID: D5/S3/Analytic/Interpolation/SchurConjugateSlope
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/SchurConjugateSlope
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Complex.CauchyIntegral, mathlib/module/Mathlib.Analysis.Complex.RealDeriv, mathlib/module/Mathlib.Analysis.Calculus.MeanValue]
   utility: none
   digest: Horizontal transport of an actual entire-function conjugate-pair slope. -/

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Set Metric Complex

namespace D5.S3.Analytic.Interpolation.SchurConjugateSlope

/-- The original closed-disk second-derivative norm, without coefficient restrictions. -/
def diskNorm (g : ℂ → ℂ) : ℝ :=
  sSup ((fun z => ‖deriv (deriv g) z‖) '' closedBall (0 : ℂ) 1)

/-- The divided difference at the two actual nodes. -/
def slope (g : ℂ → ℂ) (a b : ℝ) : ℂ :=
  (g ((a : ℂ) + b * I) - g ((a : ℂ) - b * I)) / (2 * b * I)

/-- The original two-node Lagrange expression. -/
def interpolant (g : ℂ → ℂ) (a b : ℝ) (z : ℂ) : ℂ :=
  (z - ((a : ℂ) - b * I)) / (2 * b * I) * g ((a : ℂ) + b * I) +
    (((a : ℂ) + b * I) - z) / (2 * b * I) * g ((a : ℂ) - b * I)

private theorem diskNorm_bdd (g : ℂ → ℂ) (hg : Differentiable ℂ g) :
    BddAbove ((fun z => ‖deriv (deriv g) z‖) '' closedBall (0 : ℂ) 1) :=
  (isCompact_closedBall (0 : ℂ) 1).bddAbove_image hg.deriv.deriv.continuous.norm.continuousOn

private theorem le_diskNorm {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) : ‖deriv (deriv g) z‖ ≤ diskNorm g :=
  le_csSup (diskNorm_bdd g hg) ⟨z, hz, rfl⟩

private theorem node_mem {a b s : ℝ} (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hs : |s| ≤ |a|) : (s : ℂ) + b * I ∈ closedBall (0 : ℂ) 1 := by
  rw [mem_closedBall, dist_zero_right]
  have hn : ‖(s : ℂ) + b * I‖ ^ 2 = s ^ 2 + b ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hsa : s ^ 2 ≤ a ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg s) (abs_nonneg a)).mpr hs
  nlinarith [norm_nonneg ((s : ℂ) + b * I)]

private theorem slope_hasDeriv {g : ℂ → ℂ} (hg : Differentiable ℂ g) (b : ℝ) (s : ℂ) :
    HasDerivAt (fun z : ℂ => (g (z + b * I) - g (z - b * I)) / (2 * b * I))
      ((deriv g (s + b * I) - deriv g (s - b * I)) / (2 * b * I)) s := by
  simpa using (((hg (s + b * I)).hasDerivAt.comp s ((hasDerivAt_id s).add_const (b * I))).sub
    ((hg (s - b * I)).hasDerivAt.comp s ((hasDerivAt_id s).sub_const (b * I)))).div_const
      (2 * b * I)

/-- The actual Lagrange derivative is the original slope at every complex test point. -/
theorem interpolant_deriv (g : ℂ → ℂ) (a b : ℝ) (z : ℂ) :
    deriv (interpolant g a b) z = slope g a b := by
  have h := ((((hasDerivAt_id z).sub_const ((a : ℂ) - b * I)).div_const
    (2 * b * I)).mul_const (g ((a : ℂ) + b * I))).add
      ((((hasDerivAt_const z ((a : ℂ) + b * I)).sub (hasDerivAt_id z)).div_const
        (2 * b * I)).mul_const (g ((a : ℂ) - b * I)))
  have hh : HasDerivAt (interpolant g a b)
      (1 / (2 * b * I) * g ((a : ℂ) + b * I) +
        (0 - 1) / (2 * b * I) * g ((a : ℂ) - b * I)) z := h
  rw [hh.deriv]
  unfold slope
  ring

/-- Horizontal displacement on the full admissible closed disk, for every entire function. -/
theorem slope_transport (g : ℂ → ℂ) (hg : Differentiable ℂ g) (a b : ℝ)
    (hb : 0 < b) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    ‖slope g a b - slope g 0 b‖ ≤ |a| * diskNorm g := by
  have hden : (2 * (b : ℂ) * I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr hb.ne')) I_ne_zero
  let f : ℝ → ℂ := fun s => slope g s b
  let f' : ℝ → ℂ := fun s =>
    (deriv g ((s : ℂ) + b * I) - deriv g ((s : ℂ) - b * I)) / (2 * b * I)
  have hf (s : ℝ) : HasDerivAt f (f' s) s := (slope_hasDeriv hg b s).comp_ofReal
  have hbound (s : ℝ) (hs : s ∈ Icc (-|a|) |a|) : ‖f' s‖ ≤ diskNorm g := by
    have hs' : |s| ≤ |a| := abs_le.mpr hs
    have hu := node_mem hab hs'
    have hv : (s : ℂ) - b * I ∈ closedBall (0 : ℂ) 1 := by
      have hh := node_mem (b := -b) (by nlinarith : a ^ 2 + (-b) ^ 2 ≤ 1) hs'
      simpa [sub_eq_add_neg] using hh
    have hh := (convex_closedBall (0 : ℂ) 1).norm_image_sub_le_of_norm_deriv_le
      (fun z _ => hg.deriv z) (fun z hz => le_diskNorm hg hz) hv hu
    have he : ((s : ℂ) + b * I) - ((s : ℂ) - b * I) = 2 * b * I := by ring
    rw [he] at hh
    dsimp [f']
    rw [norm_div]
    exact (div_le_iff₀ (norm_pos_iff.mpr hden)).mpr hh
  have hh := (convex_Icc (-|a|) |a|).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ => (hf s).hasDerivWithinAt) hbound
    (show (0 : ℝ) ∈ Icc (-|a|) |a| by constructor <;> linarith [abs_nonneg a])
    (show a ∈ Icc (-|a|) |a| from ⟨neg_abs_le a, le_abs_self a⟩)
  simpa only [f, sub_zero, Real.norm_eq_abs, mul_comm] using hh

/-- The original arbitrary-complex entire class with the closed-disk norm constraint. -/
def entireClass : Set (ℂ → ℂ) := {g | Differentiable ℂ g ∧ diskNorm g ≤ 1}

/-- The original inner value set, with the actual interpolant derivative. -/
def innerValues (g : ℂ → ℂ) (a b : ℝ) : Set ℝ :=
  (fun x : ℝ => ‖deriv g x - deriv (interpolant g a b) x‖) '' Icc (-1 : ℝ) 1

/-- The original outer value set. No exchange of suprema is made. -/
def outerValues (a b : ℝ) : Set ℝ :=
  (fun g => sSup (innerValues g a b)) '' entireClass

def uniformError (a b : ℝ) : ℝ := sSup (outerValues a b)

private theorem coarse_error_bound (g : ℂ → ℂ) (hg : Differentiable ℂ g) (a b x : ℝ)
    (hb : 0 < b) (hab : a ^ 2 + b ^ 2 ≤ 1) (hx : x ∈ Icc (-1 : ℝ) 1) :
    ‖deriv g x - deriv (interpolant g a b) x‖ ≤ 2 * diskNorm g := by
  have hM : 0 ≤ diskNorm g := (norm_nonneg _).trans (le_diskNorm (z := 0) hg (by simp))
  have hx' : (x : ℂ) ∈ closedBall (0 : ℂ) 1 := by
    simpa only [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] using
      abs_le.mpr hx
  have hw := node_mem hab (le_refl |a|)
  have hv : (a : ℂ) - b * I ∈ closedBall (0 : ℂ) 1 := by
    simpa [sub_eq_add_neg] using node_mem (b := -b) (by nlinarith : a ^ 2 + (-b) ^ 2 ≤ 1) (le_refl |a|)
  let f : ℂ → ℂ := fun z => g z - deriv g x * z
  have hf (z : ℂ) : HasDerivAt f (deriv g z - deriv g x) z := by
    simpa [f] using (hg z).hasDerivAt.sub ((hasDerivAt_id z).const_mul (deriv g x))
  have hd (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 1) : ‖deriv f z‖ ≤ 2 * diskNorm g := by
    rw [(hf z).deriv]
    have hh := (convex_closedBall (0 : ℂ) 1).norm_image_sub_le_of_norm_deriv_le
      (fun t _ => hg.deriv t) (fun t ht => le_diskNorm hg ht) hx' hz
    have hdist : ‖z - (x : ℂ)‖ ≤ 2 := by
      have hz' : ‖z‖ ≤ 1 := by simpa using hz
      have hx'' : ‖(x : ℂ)‖ ≤ 1 := by simpa using hx'
      exact (norm_sub_le _ _).trans (by linarith)
    exact hh.trans (by nlinarith)
  have hh := (convex_closedBall (0 : ℂ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun z _ => (hf z).differentiableAt) hd hv hw
  have he : ((a : ℂ) + b * I) - ((a : ℂ) - b * I) = 2 * b * I := by ring
  rw [he] at hh
  have hden : (2 * (b : ℂ) * I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr hb.ne')) I_ne_zero
  have hh' : ‖(f ((a : ℂ) + b * I) - f ((a : ℂ) - b * I)) / (2 * b * I)‖ ≤
      2 * diskNorm g := by
    rw [norm_div]
    exact (div_le_iff₀ (norm_pos_iff.mpr hden)).mpr hh
  have hquot : (f ((a : ℂ) + b * I) - f ((a : ℂ) - b * I)) / (2 * b * I) =
      slope g a b - deriv g x := by
    dsimp [f, slope]
    field_simp
    <;> ring
  rw [hquot, norm_sub_rev, ← interpolant_deriv g a b x] at hh'
  exact hh'

private def quadratic : ℂ → ℂ := fun z => z ^ 2 / 2

private theorem quadratic_deriv : deriv quadratic = id := by
  funext z
  have h : HasDerivAt quadratic (2 * z ^ (2 - 1) * 1 / 2) z :=
    ((hasDerivAt_id z).pow 2).div_const (2 : ℂ)
  rw [h.deriv]
  dsimp
  ring

private theorem quadratic_second : deriv (deriv quadratic) = fun _ => 1 := by
  rw [quadratic_deriv]
  funext z
  exact deriv_id z

private theorem quadratic_member : quadratic ∈ entireClass := by
  constructor
  · unfold quadratic
    fun_prop
  · unfold diskNorm
    apply csSup_le
    · exact ⟨_, 0, by simp, rfl⟩
    · rintro v ⟨z, hz, rfl⟩
      simp [quadratic_second]

private theorem quadratic_slope (a b : ℝ) (hb : 0 < b) : slope quadratic a b = a := by
  have hden : (2 * (b : ℂ) * I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr hb.ne')) I_ne_zero
  dsimp [slope, quadratic]
  apply (div_eq_iff hden).mpr
  ring

private theorem quadratic_error (a b x : ℝ) (hb : 0 < b) :
    ‖deriv quadratic x - deriv (interpolant quadratic a b) x‖ = |x - a| := by
  rw [quadratic_deriv, interpolant_deriv, quadratic_slope a b hb]
  simpa only [id_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

private theorem quadratic_sup (a b : ℝ) (hb : 0 < b) :
    sSup (innerValues quadratic a b) = 1 + |a| := by
  have hbound : ∀ v ∈ innerValues quadratic a b, v ≤ 1 + |a| := by
    rintro v ⟨x, hx, rfl⟩
    change ‖deriv quadratic x - deriv (interpolant quadratic a b) x‖ ≤ _
    rw [quadratic_error a b x hb]
    exact (abs_sub x a).trans (by linarith [abs_le.mpr hx])
  have hatt : 1 + |a| ∈ innerValues quadratic a b := by
    by_cases ha : 0 ≤ a
    · refine ⟨-1, by norm_num, ?_⟩
      change ‖deriv quadratic (-1) - deriv (interpolant quadratic a b) (-1)‖ = _
      rw [quadratic_error a b (-1) hb, abs_of_nonneg ha, abs_of_nonpos (by linarith)]
      ring
    · refine ⟨1, by norm_num, ?_⟩
      change ‖deriv quadratic 1 - deriv (interpolant quadratic a b) 1‖ = _
      rw [quadratic_error a b 1 hb, abs_of_nonpos (le_of_not_ge ha),
        abs_of_nonneg (by linarith)]
      ring
  exact le_antisymm (csSup_le ⟨_, hatt⟩ hbound) (le_csSup ⟨_, hbound⟩ hatt)

/-- Both original supremum levels are nonempty and bounded; the actual quadratic supplies
    the sharp proposed lower value. The separate sharp upper estimate is not assumed. -/
theorem original_suprema_bounded (a b : ℝ) (hb : 0 < b) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    entireClass.Nonempty ∧
    (∀ g ∈ entireClass, (innerValues g a b).Nonempty ∧ BddAbove (innerValues g a b)) ∧
    (outerValues a b).Nonempty ∧ BddAbove (outerValues a b) ∧
    1 + |a| ≤ uniformError a b ∧ uniformError a b ≤ 2 ∧
    ∃ g ∈ entireClass, sSup (innerValues g a b) = 1 + |a| := by
  have hinner (g : ℂ → ℂ) (hg : g ∈ entireClass) :
      (innerValues g a b).Nonempty ∧ BddAbove (innerValues g a b) := by
    refine ⟨⟨_, 0, by norm_num, rfl⟩, ⟨2, ?_⟩⟩
    rintro v ⟨x, hx, rfl⟩
    exact (coarse_error_bound g hg.1 a b x hb hab hx).trans (by linarith [hg.2])
  have hout : (outerValues a b).Nonempty :=
    ⟨_, quadratic, quadratic_member, rfl⟩
  have hbout : BddAbove (outerValues a b) := by
    refine ⟨2, ?_⟩
    rintro v ⟨g, hg, rfl⟩
    apply csSup_le (hinner g hg).1
    rintro w ⟨x, hx, rfl⟩
    exact (coarse_error_bound g hg.1 a b x hb hab hx).trans (by linarith [hg.2])
  refine ⟨⟨quadratic, quadratic_member⟩, hinner, hout, hbout, ?_, ?_,
    quadratic, quadratic_member, quadratic_sup a b hb⟩
  · apply le_csSup hbout
    exact ⟨quadratic, quadratic_member, quadratic_sup a b hb⟩
  · apply csSup_le hout
    rintro v ⟨g, hg, rfl⟩
    apply csSup_le (hinner g hg).1
    rintro w ⟨x, hx, rfl⟩
    exact (coarse_error_bound g hg.1 a b x hb hab hx).trans (by linarith [hg.2])

#print axioms original_suprema_bounded

end D5.S3.Analytic.Interpolation.SchurConjugateSlope
