/- GID: D5/S3/Analytic/Interpolation/SchurConjugateSlope
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/SchurConjugateSlope
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Complex.CauchyIntegral, mathlib/module/Mathlib.Analysis.Complex.RealDeriv, mathlib/module/Mathlib.Analysis.Calculus.MeanValue]
   utility: none
   digest: Horizontal transport of an actual entire-function conjugate-pair slope. -/

import D5.S3.Analytic.Interpolation.SchurIntegratedKernel
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.MeanValue

/-! Actual entire-function conjugate slopes and original compact suprema. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Set Metric Complex MeasureTheory

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

/-- The actual nodal polynomial, as the product at the two original nodes. -/
def nodalPolynomial (a b : ℝ) (z : ℂ) : ℂ :=
  (z - ((a : ℂ) + b * I)) * (z - ((a : ℂ) - b * I))

/-- The original derivative norm of the nodal polynomial on the closed real interval. -/
def nodalDerivativeNorm (a b : ℝ) : ℝ :=
  sSup ((fun x : ℝ => ‖deriv (nodalPolynomial a b) x‖) '' Icc (-1 : ℝ) 1)

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

private theorem diskNorm_attained (g : ℂ → ℂ) (hg : Differentiable ℂ g) :
    ∃ z ∈ closedBall (0 : ℂ) 1, diskNorm g = ‖deriv (deriv g) z‖ :=
  (isCompact_closedBall (0 : ℂ) 1).exists_sSup_image_eq
    ⟨0, by simp⟩ hg.deriv.deriv.continuous.norm.continuousOn

private theorem innerSup_attained (g : ℂ → ℂ) (hg : Differentiable ℂ g) (a b : ℝ) :
    ∃ x ∈ Icc (-1 : ℝ) 1,
      sSup (innerValues g a b) = ‖deriv g x - deriv (interpolant g a b) x‖ := by
  have hc : Continuous (fun x : ℝ => ‖deriv g x - deriv (interpolant g a b) x‖) := by
    simp_rw [interpolant_deriv]
    exact ((hg.deriv.continuous.comp Complex.continuous_ofReal).sub continuous_const).norm
  exact isCompact_Icc.exists_sSup_image_eq ⟨0, by norm_num⟩ hc.continuousOn

private theorem coarse_error_bound (g : ℂ → ℂ) (hg : Differentiable ℂ g) (a b x : ℝ)
    (hb : 0 < b) (hab : a ^ 2 + b ^ 2 ≤ 1) (hx : x ∈ Icc (-1 : ℝ) 1) :
    ‖deriv g x - deriv (interpolant g a b) x‖ ≤ 2 * diskNorm g := by
  have hM : 0 ≤ diskNorm g := (norm_nonneg _).trans (le_diskNorm (z := 0) hg (by simp))
  have hx' : (x : ℂ) ∈ closedBall (0 : ℂ) 1 := by
    simpa only [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] using
      abs_le.mpr hx
  let R : ℝ := Real.sqrt (1 + b ^ 2)
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = 1 + b ^ 2 := Real.sq_sqrt (by positivity)
  let K : Set ℂ := closedBall (0 : ℂ) 1 ∩ closedBall (x : ℂ) R
  have hcv : Convex ℝ K := (convex_closedBall (0 : ℂ) 1).inter (convex_closedBall (x : ℂ) R)
  have hnode (c : ℝ) (hc : c ^ 2 = b ^ 2) : (c : ℂ) * I ∈ K := by
    constructor
    · have hh := node_mem (a := a) (b := c) (s := 0) (by nlinarith [hab])
        (by simpa using abs_nonneg a)
      simpa using hh
    · rw [mem_closedBall, dist_eq_norm]
      have hn : ‖(c : ℂ) * I - (x : ℂ)‖ ^ 2 = x ^ 2 + c ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp
        ring
      apply (sq_le_sq₀ (norm_nonneg _) hR0).mp
      rw [hn, hR2, hc]
      have hxabs := abs_le.mpr hx
      have hxs : x ^ 2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x]
      linarith
  let f : ℂ → ℂ := fun z => g z - deriv g x * z
  have hf (z : ℂ) := (hg z).hasDerivAt.sub
    ((hasDerivAt_id z).const_mul (deriv g x))
  have hd (z : ℂ) (hz : z ∈ K) :
      ‖deriv g z - deriv g x * 1‖ ≤ R * diskNorm g := by
    rw [mul_one]
    have hh := (convex_closedBall (0 : ℂ) 1).norm_image_sub_le_of_norm_deriv_le
      (fun t _ => hg.deriv t) (fun t ht => le_diskNorm hg ht) hx' hz.1
    have hdist : ‖z - (x : ℂ)‖ ≤ R := by simpa only [mem_closedBall, dist_eq_norm] using hz.2
    exact hh.trans (by nlinarith)
  have hh : ‖f ((b : ℂ) * I) - f ((-b : ℝ) * I)‖ ≤
      R * diskNorm g * ‖(b : ℂ) * I - ((-b : ℝ) * I)‖ := by
    simpa only [f, Pi.sub_apply, id_eq] using
      hcv.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun z _ => (hf z).hasDerivWithinAt) hd
        (hnode (-b) (by ring)) (hnode b rfl)
  have he : (b : ℂ) * I - ((-b : ℝ) * I) = 2 * b * I := by push_cast; ring
  rw [he] at hh
  have hden : (2 * (b : ℂ) * I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr hb.ne')) I_ne_zero
  have hh' : ‖(f ((b : ℂ) * I) - f ((-b : ℝ) * I)) / (2 * b * I)‖ ≤
      R * diskNorm g := by
    rw [norm_div]
    exact (div_le_iff₀ (norm_pos_iff.mpr hden)).mpr hh
  have hquot : (f ((b : ℂ) * I) - f ((-b : ℝ) * I)) / (2 * b * I) =
      slope g 0 b - deriv g x := by
    dsimp [f, slope]
    have hbC : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
    push_cast
    field_simp [hbC]
    <;> ring
  rw [hquot, norm_sub_rev] at hh'
  have htransport := slope_transport g hg a b hb hab
  have hA : |a| ≤ 1 := by nlinarith [sq_abs a, abs_nonneg a, sq_nonneg b]
  have hsum : R + |a| ≤ 2 := by
    have hle : R ≤ 2 - |a| := by
      apply (sq_le_sq₀ hR0 (by linarith : 0 ≤ 2 - |a|)).mp
      nlinarith [sq_abs a, sq_nonneg (|a| - 1)]
    linarith
  rw [interpolant_deriv]
  calc
    ‖deriv g x - slope g a b‖ ≤ ‖deriv g x - slope g 0 b‖ +
        ‖slope g 0 b - slope g a b‖ := by
          simpa only [dist_eq_norm] using dist_triangle (deriv g x) (slope g 0 b) (slope g a b)
    _ ≤ R * diskNorm g + |a| * diskNorm g := by
      rw [norm_sub_rev (slope g 0 b)]
      exact add_le_add hh' htransport
    _ ≤ 2 * diskNorm g := by nlinarith

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
      change ‖deriv quadratic ((-1 : ℝ) : ℂ) -
        deriv (interpolant quadratic a b) ((-1 : ℝ) : ℂ)‖ = _
      rw [quadratic_error a b (-1) hb, abs_of_nonneg ha, abs_of_nonpos (by linarith)]
      ring
    · refine ⟨1, by norm_num, ?_⟩
      change ‖deriv quadratic ((1 : ℝ) : ℂ) -
        deriv (interpolant quadratic a b) ((1 : ℝ) : ℂ)‖ = _
      rw [quadratic_error a b 1 hb, abs_of_nonpos (le_of_not_ge ha),
        abs_of_nonneg (by linarith)]
      ring
  exact le_antisymm (csSup_le ⟨_, hatt⟩ hbound) (le_csSup ⟨_, hbound⟩ hatt)

private theorem quadratic_norm : diskNorm quadratic = 1 := by
  apply le_antisymm quadratic_member.2
  apply le_csSup (diskNorm_bdd quadratic quadratic_member.1)
  refine ⟨0, by simp, ?_⟩
  simp [quadratic_second]

private theorem nodal_derivative_norm (a b x : ℝ) :
    ‖deriv (nodalPolynomial a b) x‖ = 2 * |x - a| := by
  have hd := (((hasDerivAt_id (x : ℂ)).sub_const ((a : ℂ) + b * I)).mul
    ((hasDerivAt_id (x : ℂ)).sub_const ((a : ℂ) - b * I)))
  have he : deriv (nodalPolynomial a b) (x : ℂ) = (2 : ℂ) * ((x : ℂ) - a) := by
    have hd' : HasDerivAt (nodalPolynomial a b)
        (1 * ((x : ℂ) - ((a : ℂ) - b * I)) +
          ((x : ℂ) - ((a : ℂ) + b * I)) * 1) (x : ℂ) := by
      exact hd
    rw [hd'.deriv]
    ring
  rw [he, norm_mul]
  simp only [norm_ofNat, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

private theorem nodal_sup (a b : ℝ) :
    nodalDerivativeNorm a b = 2 * (1 + |a|) ∧
    ∃ x ∈ Icc (-1 : ℝ) 1, nodalDerivativeNorm a b = ‖deriv (nodalPolynomial a b) x‖ := by
  have hbound : ∀ v ∈ ((fun x : ℝ => ‖deriv (nodalPolynomial a b) x‖) '' Icc (-1 : ℝ) 1),
      v ≤ 2 * (1 + |a|) := by
    rintro v ⟨x, hx, rfl⟩
    change ‖deriv (nodalPolynomial a b) (x : ℂ)‖ ≤ _
    rw [nodal_derivative_norm]
    have hh := (abs_sub x a).trans (show |x| + |a| ≤ 1 + |a| by linarith [abs_le.mpr hx])
    linarith
  have hatt : ∃ x ∈ Icc (-1 : ℝ) 1,
      ‖deriv (nodalPolynomial a b) x‖ = 2 * (1 + |a|) := by
    by_cases ha : 0 ≤ a
    · refine ⟨-1, by norm_num, ?_⟩
      rw [nodal_derivative_norm a b (-1), abs_of_nonneg ha, abs_of_nonpos (by linarith)]
      ring
    · refine ⟨1, by norm_num, ?_⟩
      rw [nodal_derivative_norm a b 1, abs_of_nonpos (le_of_not_ge ha),
        abs_of_nonneg (by linarith)]
      ring
  obtain ⟨x, hx, he⟩ := hatt
  have hmem : 2 * (1 + |a|) ∈
      ((fun x : ℝ => ‖deriv (nodalPolynomial a b) x‖) '' Icc (-1 : ℝ) 1) := ⟨x, hx, he⟩
  have hn : nodalDerivativeNorm a b = 2 * (1 + |a|) :=
    le_antisymm (csSup_le ⟨_, hmem⟩ hbound) (le_csSup ⟨_, hbound⟩ hmem)
  exact ⟨hn, x, hx, hn.trans he.symm⟩

/-- Both original supremum levels are nonempty and bounded; the actual quadratic supplies
    the sharp proposed lower value. The separate sharp upper estimate is not assumed. -/
theorem original_suprema_bounded (a b : ℝ) (hb : 0 < b) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    entireClass.Nonempty ∧
    (∀ g ∈ entireClass, (innerValues g a b).Nonempty ∧ BddAbove (innerValues g a b) ∧
      (∃ z ∈ closedBall (0 : ℂ) 1, diskNorm g = ‖deriv (deriv g) z‖) ∧
      ∃ x ∈ Icc (-1 : ℝ) 1,
        sSup (innerValues g a b) = ‖deriv g x - deriv (interpolant g a b) x‖) ∧
    (outerValues a b).Nonempty ∧ BddAbove (outerValues a b) ∧
    1 + |a| ≤ uniformError a b ∧ uniformError a b ≤ 2 ∧
    ∃ g ∈ entireClass, g = (fun z => z ^ 2 / 2) ∧ diskNorm g = 1 ∧
      slope g a b = a ∧ (∀ x : ℝ,
        ‖deriv g x - deriv (interpolant g a b) x‖ = |x - a|) ∧
      sSup (innerValues g a b) = 1 + |a| ∧
      nodalDerivativeNorm a b = 2 * (1 + |a|) ∧
      (1 / 2) * nodalDerivativeNorm a b = 1 + |a| ∧
      ∃ x ∈ Icc (-1 : ℝ) 1,
        nodalDerivativeNorm a b = ‖deriv (nodalPolynomial a b) x‖ := by
  have hinner (g : ℂ → ℂ) (hg : g ∈ entireClass) :
      (innerValues g a b).Nonempty ∧ BddAbove (innerValues g a b) ∧
      (∃ z ∈ closedBall (0 : ℂ) 1, diskNorm g = ‖deriv (deriv g) z‖) ∧
      ∃ x ∈ Icc (-1 : ℝ) 1,
        sSup (innerValues g a b) = ‖deriv g x - deriv (interpolant g a b) x‖ := by
    refine ⟨⟨_, 0, by norm_num, rfl⟩, ⟨2, ?_⟩,
      diskNorm_attained g hg.1, innerSup_attained g hg.1 a b⟩
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
  have hn := nodal_sup a b
  refine ⟨⟨quadratic, quadratic_member⟩, hinner, hout, hbout, ?_, ?_,
    quadratic, quadratic_member, rfl, quadratic_norm, quadratic_slope a b hb,
    (fun x => quadratic_error a b x hb), quadratic_sup a b hb, hn.1, ?_, hn.2⟩
  · apply le_csSup hbout
    exact ⟨quadratic, quadratic_member, quadratic_sup a b hb⟩
  · apply csSup_le hout
    rintro v ⟨g, hg, rfl⟩
    apply csSup_le (hinner g hg).1
    rintro w ⟨x, hx, rfl⟩
    exact (coarse_error_bound g hg.1 a b x hb hab hx).trans (by linarith [hg.2])
  · rw [hn.1]
    ring

private theorem slope_primitive_identity (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (b : ℝ) (hb : 0 < b) :
    slope g 0 b = deriv g 0 + (1 / (2 * b) : ℝ) •
      (∫ t in -b..b, (deriv g ((t : ℂ) * I) - deriv g 0)) := by
  let f : ℂ → ℂ := fun z => g (z * I)
  have hd (z : ℂ) : HasDerivAt f (deriv g (z * I) * I) z := by
    simpa only [one_mul, id_eq, Function.comp_def] using
      (hg (z * I)).hasDerivAt.comp z ((hasDerivAt_id z).mul_const I)
  have hc : Continuous (fun t : ℝ => deriv g ((t : ℂ) * I)) :=
    hg.deriv.continuous.comp (by fun_prop)
  have he : (∫ t in -b..b, deriv g ((t : ℂ) * I) * I) =
      g ((b : ℂ) * I) - g (-((b : ℂ) * I)) := by
    simpa only [f, Complex.ofReal_neg, neg_mul] using
      (intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t (_ : t ∈ uIcc (-b) b) => (hd (t : ℂ)).comp_ofReal)
        ((hc.mul continuous_const).intervalIntegrable (-b) b))
  rw [intervalIntegral.integral_mul_const] at he
  have hden : (2 * (b : ℂ) * I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr hb.ne')) I_ne_zero
  have hs : slope g 0 b = (1 / (2 * b) : ℝ) •
      (∫ t in -b..b, deriv g ((t : ℂ) * I)) := by
    simp only [slope, Complex.ofReal_zero, zero_add, zero_sub]
    apply (div_eq_iff hden).mpr
    rw [← he, Complex.real_smul]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hb.ne']
    <;> ring <;> simp only [mul_comm]
  have hH : (∫ t in -b..b, (deriv g ((t : ℂ) * I) - deriv g 0)) =
      (∫ t in -b..b, deriv g ((t : ℂ) * I)) - (2 * b : ℝ) • deriv g 0 := by
    rw [intervalIntegral.integral_sub (hc.intervalIntegrable (-b) b) intervalIntegrable_const,
      intervalIntegral.integral_const]
    congr 1
    rw [show b - -b = 2 * b by ring]
  rw [hs, hH]
  simp only [Complex.real_smul]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hb.ne']
  <;> ring <;> simp only [mul_comm]

private theorem imaginary_axis_bound (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (b x : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) (hx : x ∈ Icc (-1 : ℝ) 1) :
    ‖deriv g (x : ℂ) - slope g 0 b‖ ≤ diskNorm g := by
  have hH (z : ℂ) : HasDerivAt (fun z : ℂ => deriv g z - deriv g 0)
      (deriv (deriv g) z) z := (hg.deriv z).hasDerivAt.sub_const _
  have hp := SchurIntegratedKernel.primitive_error_bound (deriv (deriv g))
    (fun z : ℂ => deriv g z - deriv g 0) hg.deriv.deriv hH (by simp)
    b ⟨hb, hb1⟩ x hx
  have he : deriv g (x : ℂ) - slope g 0 b =
      (deriv g (x : ℂ) - deriv g 0) - (1 / (2 * b) : ℝ) •
        (∫ t in -b..b, (deriv g ((t : ℂ) * I) - deriv g 0)) := by
    rw [slope_primitive_identity g hg b hb]
    ring
  rw [he]
  exact hp

private theorem sharp_error_bound (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (a b x : ℝ) (hb : 0 < b) (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    ‖deriv g (x : ℂ) - deriv (interpolant g a b) (x : ℂ)‖ ≤
      (1 + |a|) * diskNorm g := by
  have hb1 : b ≤ 1 := by nlinarith [sq_nonneg a]
  rw [interpolant_deriv]
  calc
    _ = ‖(deriv g (x : ℂ) - slope g 0 b) + (slope g 0 b - slope g a b)‖ := by
      congr 1
      ring
    _ ≤ ‖deriv g (x : ℂ) - slope g 0 b‖ + ‖slope g 0 b - slope g a b‖ := norm_add_le _ _
    _ ≤ diskNorm g + |a| * diskNorm g := by
      apply add_le_add (imaginary_axis_bound g hg b x hb hb1 hx)
      rw [norm_sub_rev]
      exact slope_transport g hg a b hb hab
    _ = _ := by ring

/-- The original entire-function error and its nested supremum are sharp on the full
admissible closed half disk, with actual quadratic and endpoint attainment. -/
theorem complete_classification (a b : ℝ) (hb : 0 < b) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    uniformError a b = 1 + |a| ∧
    uniformError a b = (1 / 2) * nodalDerivativeNorm a b ∧
    (∀ g ∈ entireClass, ∀ x ∈ Icc (-1 : ℝ) 1,
      ‖deriv g (x : ℂ) - deriv (interpolant g a b) (x : ℂ)‖ ≤ 1 + |a|) ∧
    entireClass.Nonempty ∧
    (∀ g ∈ entireClass, (innerValues g a b).Nonempty ∧ BddAbove (innerValues g a b) ∧
      (∃ z ∈ closedBall (0 : ℂ) 1, diskNorm g = ‖deriv (deriv g) z‖) ∧
      ∃ x ∈ Icc (-1 : ℝ) 1,
        sSup (innerValues g a b) = ‖deriv g x - deriv (interpolant g a b) x‖) ∧
    (outerValues a b).Nonempty ∧ BddAbove (outerValues a b) ∧
    ∃ g ∈ entireClass, g = (fun z => z ^ 2 / 2) ∧ diskNorm g = 1 ∧
      slope g a b = a ∧
      (∀ x : ℝ, ‖deriv g x - deriv (interpolant g a b) x‖ = |x - a|) ∧
      sSup (innerValues g a b) = uniformError a b ∧
      (0 ≤ a → ‖deriv g ((-1 : ℝ) : ℂ) -
        deriv (interpolant g a b) ((-1 : ℝ) : ℂ)‖ = uniformError a b) ∧
      (a ≤ 0 → ‖deriv g ((1 : ℝ) : ℂ) -
        deriv (interpolant g a b) ((1 : ℝ) : ℂ)‖ = uniformError a b) ∧
      ∃ x ∈ Icc (-1 : ℝ) 1,
        nodalDerivativeNorm a b = ‖deriv (nodalPolynomial a b) x‖ := by
  obtain ⟨hclass, hinner, hout, hbout, hlo, _hcoarse,
    g, hg, hgquad, hgnorm, hgslope, hgerror, hgsup, _hnorm, hhalf, hnod⟩ :=
    original_suprema_bounded a b hb hab
  have hpoint (f : ℂ → ℂ) (hf : f ∈ entireClass) (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
      ‖deriv f (x : ℂ) - deriv (interpolant f a b) (x : ℂ)‖ ≤ 1 + |a| := by
    exact (sharp_error_bound f hf.1 a b x hb hab hx).trans
      (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hf.2 (show 0 ≤ 1 + |a| by positivity))
  have hub : uniformError a b ≤ 1 + |a| := by
    apply csSup_le hout
    rintro v ⟨f, hf, rfl⟩
    apply csSup_le (hinner f hf).1
    rintro w ⟨x, hx, rfl⟩
    exact hpoint f hf x hx
  have hE : uniformError a b = 1 + |a| := le_antisymm hub hlo
  refine ⟨hE, hE.trans hhalf.symm, hpoint, hclass, hinner, hout, hbout,
    g, hg, hgquad, hgnorm, hgslope, hgerror, hgsup.trans hE.symm, ?_, ?_, hnod⟩
  · intro ha
    rw [hgerror (-1), hE, abs_of_nonneg ha, abs_of_nonpos (by linarith : -1 - a ≤ 0)]
    ring
  · intro ha
    rw [hgerror 1, hE, abs_of_nonpos ha, abs_of_nonneg (by linarith : 0 ≤ 1 - a)]
    ring

#print axioms complete_classification
#print axioms original_suprema_bounded

end D5.S3.Analytic.Interpolation.SchurConjugateSlope
