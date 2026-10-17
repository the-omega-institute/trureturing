import D5.S3.Analytic.Convexity.CFMPTransientLegendrePullback
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic

/-!
Transient source only. No elaboration or admission claim is made.
The local import is the byte-for-byte supplied, uncompiled Legendre consumer.
Q and the openness of the actual image are inputs, not constructions in this file.
-/

open Filter Set
open scoped Topology

noncomputable section

namespace TransientPotentialRecovery

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual forward map, defined on the ambient space. -/
def T (F : E → E) (x : E) : E := x + F x

/-- The domain of the one supplied inverse primitive is exactly this image. -/
def Omega (D : Set E) (F : E → E) : Set E := T F '' D

/-- A total function; its derivative and convexity are asserted only on D. -/
def P (F : E → E) (Q : E → ℝ) (x : E) : ℝ :=
  inner ℝ x (T F x) - Q (T F x) - (1 / 2 : ℝ) * ‖x‖ ^ 2

/-- Exact downstream recovery from the same image, inverse, and primitive.
There is no finite-dimensional, completeness, nonempty, or differentiability-of-F
hypothesis. All declarations in this file are temporary assembly artifacts. -/
theorem recover
    {D : Set E} {F G : E → E} {Q : E → ℝ}
    (hD : IsOpen D) (hconv : Convex ℝ D)
    (hF : ContinuousOn F D)
    (hmono : ∀ x ∈ D, ∀ y ∈ D,
      0 ≤ inner ℝ (F x - F y) (x - y))
    (hOmega : IsOpen (T F '' D))
    (hinv : ∀ x ∈ D, G (T F x) = x)
    (hQ : ∀ z ∈ T F '' D, HasFDerivAt Q (innerSL ℝ (G z)) z) :
    (∀ x ∈ D, HasFDerivAt (P F Q) (innerSL ℝ (F x)) x) ∧
      ConvexOn ℝ D (P F Q) := by
  have hGmono : ∀ z ∈ T F '' D, ∀ w ∈ T F '' D,
      0 ≤ inner ℝ (G z - G w) (z - w) := by
    intro z hz w hw
    rcases hz with ⟨x, hx, rfl⟩
    rcases hw with ⟨y, hy, rfl⟩
    rw [hinv x hx, hinv y hy]
    have hdiff : T F x - T F y = (x - y) + (F x - F y) := by
      dsimp [T]
      abel
    rw [hdiff, inner_add_right]
    have hFm : 0 ≤ inner ℝ (x - y) (F x - F y) := by
      rw [real_inner_comm]
      exact hmono x hx y hy
    exact add_nonneg real_inner_self_nonneg hFm
  have hP : ∀ x ∈ D, HasFDerivAt (P F Q) (innerSL ℝ (F x)) x := by
    intro x hx
    have hFx : ContinuousAt F x := (hF x hx).continuousAt (hD.mem_nhds hx)
    have hTx : ContinuousAt (T F) x := by
      apply (continuousAt_id.add hFx).congr_of_eventuallyEq
      exact Filter.Eventually.of_forall fun y => rfl
    have hnear : ∀ᶠ y in 𝓝 x, G (T F y) = y := by
      filter_upwards [hD.mem_nhds hx] with y hy
      exact hinv y hy
    have hL :=
      D5.S3.Analytic.Convexity.MonotoneLegendrePullback.hasFDerivAt_legendre_pullback_of_monotone
        hOmega (show T F x ∈ T F '' D from ⟨x, hx, rfl⟩)
        hTx hQ hGmono hnear
    have hquad : HasFDerivAt (fun y : E => (1 / 2 : ℝ) * ‖y‖ ^ 2)
        (innerSL ℝ x) x := by
      have hraw := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (1 / 2 : ℝ)
      have hcoeff : (1 / 2 : ℝ) • (2 • innerSL ℝ x) = innerSL ℝ x := by
        ext v
        simp only [two_smul, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.add_apply, smul_eq_mul]
        ring
      rw [hcoeff] at hraw
      exact hraw
    have hclm : innerSL ℝ (T F x) - innerSL ℝ x = innerSL ℝ (F x) := by
      ext v
      simp only [ContinuousLinearMap.sub_apply, innerSL_apply_apply, T, inner_add_left]
      ring
    apply ((hL.sub hquad).congr_fderiv hclm).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun y => rfl
  refine ⟨hP, hconv, ?_⟩
  intro x hx y hy a b ha hb hab
  let line : ℝ → E := fun t => x + t • (y - x)
  let f : ℝ → ℝ := fun t => P F Q (line t)
  have hline (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : line t ∈ D := by
    have htD := hconv hx hy (sub_nonneg.mpr ht.2) ht.1
      (show (1 - t) + t = 1 by ring)
    have heq : line t = (1 - t) • x + t • y := by
      dsimp [line]
      module
    rw [heq]
    exact htD
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt f (inner ℝ (F (line t)) (y - x)) t := by
    have hl : HasDerivAt line (y - x) t := by
      simpa only [line, one_smul, id_eq] using
        ((hasDerivAt_id t).smul_const (y - x)).const_add x
    simpa only [f, Function.comp_def, innerSL_apply_apply] using
      (hP (line t) (hline t ht)).comp_hasDerivAt t hl
  have hfcont : ContinuousOn f (Icc (0 : ℝ) 1) :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hfdiff : DifferentiableOn ℝ f (interior (Icc (0 : ℝ) 1)) :=
    fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
  have hderiv_mono : MonotoneOn (deriv f) (interior (Icc (0 : ℝ) 1)) := by
    intro s hs t ht hst
    have hsI : s ∈ Icc (0 : ℝ) 1 := interior_subset hs
    have htI : t ∈ Icc (0 : ℝ) 1 := interior_subset ht
    rw [(hd s hsI).deriv, (hd t htI).deriv]
    rcases eq_or_lt_of_le hst with heq | hlt
    · subst t
      exact le_rfl
    · have hm := hmono (line t) (hline t htI) (line s) (hline s hsI)
      have hdiff : line t - line s = (t - s) • (y - x) := by
        dsimp [line]
        module
      rw [hdiff, real_inner_smul_right, inner_sub_left] at hm
      exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hm (sub_pos.mpr hlt))
  have hfconv : ConvexOn ℝ (Icc (0 : ℝ) 1) f :=
    MonotoneOn.convexOn_of_deriv (convex_Icc 0 1) hfcont hfdiff hderiv_mono
  have hj := hfconv.2 (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num) ha hb hab
  have h0 : line 0 = x := by simp [line]
  have h1 : line 1 = y := by simp [line]
  have ha' : a = 1 - b := by linarith
  have habline : line b = a • x + b • y := by
    rw [ha']
    dsimp [line]
    module
  simpa only [smul_eq_mul, mul_zero, mul_one, zero_add, f, h0, h1, habline] using hj

end TransientPotentialRecovery
