/- GID: D5/S3/Quantum/Tomography/CayleyCoverAnalysis
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/CayleyCoverAnalysis
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Compact signed Cayley charts, quantitative uniqueness, root migration, and a uniform residual barrier supply analytic interfaces for exhaustive common-unbiased root coverage. -/

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/- Reuse audit:
   * Uses Mathlib's convex-set Frechet mean-value inequality directly.
   * Does not introduce interval arithmetic, Newton/Krawczyk syntax, graph
     carriers, a second Cayley map, Hadamard predicates, or an external PASS.
   * The two continuation statements expose only mathematical inequalities
     that an exact interval/reflection layer may later discharge.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.CayleyCoverAnalysis

private theorem right_semicircle_chart (x y : ℝ)
    (hcircle : x ^ 2 + y ^ 2 = 1) (hx : 0 ≤ x) :
    ∃ t ∈ Set.Icc (-1 : ℝ) 1,
      x = (1 - t ^ 2) / (1 + t ^ 2) ∧ y = 2 * t / (1 + t ^ 2) := by
  let t : ℝ := y / (1 + x)
  have hden : 0 < 1 + x := by linarith
  have hden0 : 1 + x ≠ 0 := ne_of_gt hden
  have hylo : -1 ≤ y := by nlinarith [sq_nonneg x]
  have hyhi : y ≤ 1 := by nlinarith [sq_nonneg x]
  have htlo : -1 ≤ t := by
    apply (le_div_iff₀ hden).2
    nlinarith
  have hthi : t ≤ 1 := by
    apply (div_le_iff₀ hden).2
    nlinarith
  have htden : 1 + t ^ 2 ≠ 0 := ne_of_gt (by positivity : 0 < 1 + t ^ 2)
  refine ⟨t, ⟨htlo, hthi⟩, ?_, ?_⟩
  · apply (eq_div_iff htden).2
    dsimp [t]
    field_simp [hden0]
    linear_combination (x + 1) * hcircle
  · apply (eq_div_iff htden).2
    dsimp [t]
    field_simp [hden0]
    linear_combination y * hcircle

/-- Every unit-circle point is covered by one of the two closed signed Cayley
charts with parameter in `[-1,1]`. Applied independently to five dephased
coordinates, this gives the 32 compact charts, including their seams. -/
theorem compact_signed_cayley_cover (x y : ℝ)
    (hcircle : x ^ 2 + y ^ 2 = 1) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      ∃ t ∈ Set.Icc (-1 : ℝ) 1,
        x = s * ((1 - t ^ 2) / (1 + t ^ 2)) ∧
        y = s * (2 * t / (1 + t ^ 2)) := by
  by_cases hx : 0 ≤ x
  · obtain ⟨t, ht, htx, hty⟩ := right_semicircle_chart x y hcircle hx
    exact ⟨1, Or.inl rfl, t, ht, by simpa using htx, by simpa using hty⟩
  · obtain ⟨t, ht, htx, hty⟩ :=
      right_semicircle_chart (-x) (-y) (by nlinarith [hcircle]) (by linarith)
    refine ⟨-1, Or.inr rfl, t, ht, ?_, ?_⟩
    · simp only [neg_one_mul]
      linarith
    · simp only [neg_one_mul]
      linarith

/-- Quantitative uniqueness from the actual Frechet derivative on a convex
set. If `q < 1`, equal residuals imply equal points. In particular a convex
root box contains at most one root. Neither injectivity of the preconditioner,
Banach completeness, nor a self-map/root-existence assumption is needed. -/
theorem preconditioned_residual_controls_displacement
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (J : E → E →L[ℝ] F) (C : F →L[ℝ] E)
    (B : Set E) (hconvex : Convex ℝ B) (q : ℝ)
    (hderiv : ∀ z ∈ B, HasFDerivAt f (J z) z)
    (hbound : ∀ z ∈ B,
      ‖C.comp (J z) - ContinuousLinearMap.id ℝ E‖ ≤ q)
    {x y : E} (hx : x ∈ B) (hy : y ∈ B) :
    (1 - q) * ‖y - x‖ ≤ ‖C (f y - f x)‖ := by
  have hcomp : ∀ z ∈ B,
      HasFDerivWithinAt (fun w ↦ C (f w)) (C.comp (J z)) B z := by
    intro z hz
    exact (C.hasFDerivAt.comp z (hderiv z hz)).hasFDerivWithinAt
  have hmv := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    hcomp hbound hconvex hx hy
  have hmv' : ‖C (f y - f x) - (y - x)‖ ≤ q * ‖y - x‖ := by
    simpa only [ContinuousLinearMap.id_apply, map_sub] using hmv
  have hsplit :
      y - x = -(C (f y - f x) - (y - x)) + C (f y - f x) := by
    abel
  have htriangle : ‖y - x‖ ≤
      ‖C (f y - f x) - (y - x)‖ + ‖C (f y - f x)‖ := by
    calc
      ‖y - x‖ =
          ‖-(C (f y - f x) - (y - x)) + C (f y - f x)‖ :=
        congrArg norm hsplit
      _ ≤ ‖-(C (f y - f x) - (y - x))‖ + ‖C (f y - f x)‖ :=
        norm_add_le _ _
      _ = ‖C (f y - f x) - (y - x)‖ + ‖C (f y - f x)‖ := by
        rw [norm_neg]
  nlinarith

/-- A root of a perturbed system cannot move far inside a convex uniqueness
box when the preconditioned parameter perturbation is small. This is the
continuation consumer of `preconditioned_residual_controls_displacement`.
The statement assumes root existence at the second parameter; it only bounds
its displacement and does not create a numerical continuation oracle. -/
theorem root_displacement_le_of_preconditioned_parameter_perturbation
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f₀ f₁ : E → F) (J : E → E →L[ℝ] F) (C : F →L[ℝ] E)
    (B : Set E) (hconvex : Convex ℝ B) (q ρ : ℝ)
    (hderiv : ∀ z ∈ B, HasFDerivAt f₀ (J z) z)
    (hbound : ∀ z ∈ B,
      ‖C.comp (J z) - ContinuousLinearMap.id ℝ E‖ ≤ q)
    (hq : q < 1)
    {x₀ x₁ : E} (hx₀ : x₀ ∈ B) (hx₁ : x₁ ∈ B)
    (hroot₀ : f₀ x₀ = 0) (hroot₁ : f₁ x₁ = 0)
    (hpert : ‖C (f₀ x₁ - f₁ x₁)‖ ≤ ρ) :
    ‖x₁ - x₀‖ ≤ ρ / (1 - q) := by
  have hmain := preconditioned_residual_controls_displacement
    f₀ J C B hconvex q hderiv hbound hx₀ hx₁
  have hres : ‖C (f₀ x₁ - f₀ x₀)‖ ≤ ρ := by
    rw [hroot₀, sub_zero]
    calc
      ‖C (f₀ x₁)‖ = ‖C (f₀ x₁ - f₁ x₁)‖ := by rw [hroot₁, sub_zero]
      _ ≤ ρ := hpert
  have hmul : (1 - q) * ‖x₁ - x₀‖ ≤ ρ := le_trans hmain hres
  have hpos : 0 < 1 - q := sub_pos.mpr hq
  apply (le_div_iff₀ hpos).2
  simpa [mul_comm] using hmul

/-- A uniform residual gap on the complement of already certified root
neighborhoods prevents new roots from appearing under a smaller uniform
parameter perturbation. This is the global compact-domain counterpart to the
local uniqueness theorem. Compactness is intentionally not built into the
statement: an interval or analytic layer may establish `hgap` by any sound
method. -/
theorem root_mem_iUnion_of_uniform_residual_gap
    {P X Y ι : Type*} [NormedAddCommGroup Y]
    (f : P → X → Y) (p₀ p : P) (K : Set X) (U : ι → Set X)
    (η ρ : ℝ)
    (hgap : ∀ x ∈ K, x ∉ ⋃ i, U i → η ≤ ‖f p₀ x‖)
    (hpert : ∀ x ∈ K, ‖f p x - f p₀ x‖ ≤ ρ)
    (hsmall : ρ < η)
    {x : X} (hx : x ∈ K) (hroot : f p x = 0) :
    x ∈ ⋃ i, U i := by
  by_contra hxU
  have hg := hgap x hx hxU
  have hp := hpert x hx
  rw [hroot, zero_sub, norm_neg] at hp
  exact (not_lt_of_ge hg) (lt_of_le_of_lt hp hsmall)

#print axioms compact_signed_cayley_cover
#print axioms preconditioned_residual_controls_displacement
#print axioms root_displacement_le_of_preconditioned_parameter_perturbation
#print axioms root_mem_iUnion_of_uniform_residual_gap

end D5.S3.Quantum.Tomography.CayleyCoverAnalysis
