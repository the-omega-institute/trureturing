/- GID: D5/S3/Zeros/CriticalPoints/ThreeLinesSchurMoment
   generality: G
   mirror-B: D5/B/S3/Zeros/CriticalPoints/ThreeLinesSchurMoment
   mirror-E: none(waiver:general-complex-interpolation)
   anchors: [mathlib/module/Mathlib.Analysis.Complex.Hadamard]
   utility: none
   digest: Scalar strip interpolation and propagation of equality to its boundary. -/

import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Convex
import Mathlib.Tactic

/-! The scalar analytic suppliers for Schur-basis moment interpolation. -/

set_option autoImplicit false

noncomputable section

open Set Complex
open Complex.HadamardThreeLines

namespace D5.S3.Zeros.CriticalPoints.ThreeLinesSchurMoment

/-- Entire functions with an explicit uniform bound on the closed unit strip. -/
structure StripData (f : ℂ → ℂ) : Prop where
  differentiable : Differentiable ℂ f
  norm_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ verticalClosedStrip 0 1, ‖f z‖ ≤ C

namespace StripData

theorem const (c : ℂ) : StripData (fun _ : ℂ => c) :=
  ⟨differentiable_const c, ‖c‖, norm_nonneg _, fun _ _ => le_rfl⟩

theorem add {f g : ℂ → ℂ} (hf : StripData f) (hg : StripData g) :
    StripData (fun z => f z + g z) := by
  rcases hf.norm_bound with ⟨C, hC, hfC⟩
  rcases hg.norm_bound with ⟨D, hD, hgD⟩
  exact ⟨hf.differentiable.add hg.differentiable, C + D, add_nonneg hC hD,
    fun z hz => (norm_add_le _ _).trans (add_le_add (hfC z hz) (hgD z hz))⟩

theorem mul {f g : ℂ → ℂ} (hf : StripData f) (hg : StripData g) :
    StripData (fun z => f z * g z) := by
  rcases hf.norm_bound with ⟨C, hC, hfC⟩
  rcases hg.norm_bound with ⟨D, hD, hgD⟩
  refine ⟨hf.differentiable.mul hg.differentiable, C * D, mul_nonneg hC hD, ?_⟩
  intro z hz
  rw [norm_mul]
  exact mul_le_mul (hfC z hz) (hgD z hz) (norm_nonneg _) hC

theorem sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, StripData (f i)) : StripData (fun z => ∑ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (0 : ℂ)
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (hf i (Finset.mem_insert_self _ _)).add (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem exp_real_slope (a : ℝ) (b : ℂ) :
    StripData (fun z : ℂ => exp (z * (a : ℂ) + b)) := by
  refine ⟨differentiable_exp.comp ((differentiable_id.mul_const _).add_const _),
    Real.exp (|a| + b.re), (Real.exp_pos _).le, ?_⟩
  intro z hz
  have hza : z.re * a ≤ |a| := by
    calc
      z.re * a ≤ |z.re * a| := le_abs_self _
      _ = z.re * |a| := by rw [abs_mul, abs_of_nonneg hz.1]
      _ ≤ 1 * |a| := mul_le_mul_of_nonneg_right hz.2 (abs_nonneg a)
      _ = |a| := one_mul _
  simp only [norm_exp, add_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  exact Real.exp_le_exp.mpr (add_le_add hza le_rfl)

theorem bddAbove {f : ℂ → ℂ} (hf : StripData f) :
    BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1) := by
  rcases hf.norm_bound with ⟨C, _, hC⟩
  refine ⟨C, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hC z hz

end StripData

/-- The normalized three-lines estimate, with equality propagated to the right boundary. -/
theorem strip_moment_bound_and_equality
    {f : ℂ → ℂ} {M : ℝ} (hM : 0 < M)
    (hd : DiffContOnCl ℂ f (verticalStrip 0 1))
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1))
    (hleft : ∀ z : ℂ, z.re = 0 → ‖f z‖ ≤ 1)
    (hright : ∀ z : ℂ, z.re = 1 → ‖f z‖ ≤ M) :
    (∀ z ∈ verticalClosedStrip 0 1, ‖f z‖ ≤ M ^ z.re) ∧
      (∀ θ : ℝ, 0 < θ → θ < 1 → ‖f (θ : ℂ)‖ = M ^ θ →
        ∀ y : ℝ, ‖f (1 + (y : ℂ) * I)‖ = M) := by
  have hbound : ∀ z ∈ verticalClosedStrip 0 1, ‖f z‖ ≤ M ^ z.re := by
    intro z hz
    simpa using norm_le_interp_of_mem_verticalClosedStrip₀₁' f hz hd hB
      (fun z hz => hleft z hz) (fun z hz => hright z hz)
  refine ⟨hbound, ?_⟩
  intro θ hθ0 hθ1 heq
  let g : ℂ → ℂ := fun z => exp (-(z * (Real.log M : ℂ))) * f z
  have hgnorm (z : ℂ) : ‖g z‖ = ‖f z‖ / M ^ z.re := by
    simp only [g, norm_mul, norm_exp, neg_re, mul_re, ofReal_re, ofReal_im,
      mul_zero, sub_zero, Real.rpow_def_of_pos hM, div_eq_mul_inv,
      ← Real.exp_neg]
    rw [mul_comm]
    congr 2
    ring
  have hgle : ∀ z ∈ verticalClosedStrip 0 1, ‖g z‖ ≤ 1 := by
    intro z hz
    rw [hgnorm]
    exact (div_le_one (Real.rpow_pos_of_pos hM _)).2 (hbound z hz)
  have hgθ : ‖g (θ : ℂ)‖ = 1 := by
    rw [hgnorm, ofReal_re, heq, div_self (ne_of_gt (Real.rpow_pos_of_pos hM _))]
  have hgd : DiffContOnCl ℂ g (verticalStrip 0 1) := by
    have he : Differentiable ℂ (fun z : ℂ => exp (-(z * (Real.log M : ℂ)))) :=
      differentiable_exp.comp ((differentiable_id.mul_const _).neg)
    exact ⟨he.differentiableOn.mul hd.1, he.continuous.continuousOn.mul hd.2⟩
  have hopen : IsOpen (verticalStrip 0 1) := continuous_re.isOpen_preimage _ isOpen_Ioo
  have hconv : Convex ℝ (verticalStrip 0 1) :=
    (convex_halfSpace_re_gt (r := 0)).inter (convex_halfSpace_re_lt (r := 1))
  have hθ : (θ : ℂ) ∈ verticalStrip 0 1 := ⟨hθ0, hθ1⟩
  have hmax : IsMaxOn (norm ∘ g) (verticalStrip 0 1) (θ : ℂ) := by
    intro z hz
    change ‖g z‖ ≤ ‖g (θ : ℂ)‖
    rw [hgθ]
    exact hgle z ⟨le_of_lt hz.1, le_of_lt hz.2⟩
  have hconstant := Complex.eqOn_closure_of_isPreconnected_of_isMaxOn_norm
    hconv.isPreconnected hopen hgd hθ hmax
  intro y
  have hy : 1 + (y : ℂ) * I ∈ closure (verticalStrip 0 1) := by
    rw [verticalStrip, closure_preimage_re, closure_Ioo zero_ne_one]
    simp
  have hnorm := congrArg norm (hconstant hy)
  change ‖g (1 + (y : ℂ) * I)‖ = ‖g (θ : ℂ)‖ at hnorm
  rw [hgnorm, hgθ] at hnorm
  simpa using (div_eq_one_iff_eq (ne_of_gt (Real.rpow_pos_of_pos hM _))).1 hnorm

/-- Equality of nonzero rotating phases at every frequency parameter fixes both data. -/
theorem rotating_phase_injective {u v : ℂ} {a b : ℝ} (hu : u ≠ 0)
    (h : ∀ y : ℝ, u * exp ((y : ℂ) * (a : ℂ) * I) =
      v * exp ((y : ℂ) * (b : ℂ) * I)) :
    u = v ∧ a = b := by
  have huv : u = v := by simpa using h 0
  refine ⟨huv, ?_⟩
  have heq : (fun y : ℝ => exp ((y : ℂ) * (a : ℂ) * I)) =
      fun y : ℝ => exp ((y : ℂ) * (b : ℂ) * I) := by
    funext y
    exact mul_left_cancel₀ hu (by simpa only [← huv] using h y)
  have ha : HasDerivAt (fun y : ℝ => exp ((y : ℂ) * (a : ℂ) * I))
      ((a : ℂ) * I) 0 := by
    simpa using ((((hasDerivAt_id (0 : ℂ)).mul_const (a : ℂ)).mul_const I).cexp).comp_ofReal
  have hb : HasDerivAt (fun y : ℝ => exp ((y : ℂ) * (b : ℂ) * I))
      ((b : ℂ) * I) 0 := by
    simpa using ((((hasDerivAt_id (0 : ℂ)).mul_const (b : ℂ)).mul_const I).cexp).comp_ofReal
  rw [heq] at ha
  exact Complex.ofReal_injective (mul_right_cancel₀ I_ne_zero (ha.unique hb))

end D5.S3.Zeros.CriticalPoints.ThreeLinesSchurMoment
