import D5.S3.Analytic.Convexity.CFMPTransientPotentialRecovery
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Transient applications only; none has been elaborated. -/

open Set Filter
open scoped Topology

noncomputable section

namespace TransientPotentialRecovery.Sanity

/-- The core really accepts the empty set, for arbitrary total F, G, and Q.
No point of the domain or normalization point is supplied. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F G : E → E) (Q : E → ℝ) :
    (∀ x ∈ (∅ : Set E), HasFDerivAt (P F Q) (innerSL ℝ (F x)) x) ∧
      ConvexOn ℝ (∅ : Set E) (P F Q) := by
  apply recover (G := G) isOpen_empty convex_empty
  · intro x hx
    exact False.elim hx
  · intro x hx
    exact False.elim hx
  · simpa only [Set.image_empty] using (isOpen_empty : IsOpen (∅ : Set E))
  · intro x hx
    exact False.elim hx
  · intro z hz
    rcases hz with ⟨x, hx, _⟩
    exact False.elim hx

/-- A concrete real inner-product space of dimension zero. -/
abbrev E0 := EuclideanSpace ℝ (Fin 0)

example : Module.finrank ℝ E0 = 0 := by
  simp [E0]

/-- A nonempty domain in the zero-dimensional space, with Q identically zero. -/
example :
    (∀ x ∈ (univ : Set E0),
      HasFDerivAt (P (fun _ : E0 => 0) (fun _ => 0)) (innerSL ℝ (0 : E0)) x) ∧
      ConvexOn ℝ (univ : Set E0) (P (fun _ : E0 => 0) (fun _ => 0)) := by
  apply recover (G := fun x : E0 => x) isOpen_univ convex_univ
  · exact continuous_const.continuousOn
  · intro x hx y hy
    simp
  · simpa only [T, add_zero, image_id] using (isOpen_univ : IsOpen (univ : Set E0))
  · intro x hx
    simp [T]
  · intro z hz
    have hz0 : z = 0 := Subsingleton.elim _ _
    subst z
    simpa using (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) (0 : E0))

/-- A continuous monotone field with a genuine corner at zero. -/
def relu (x : ℝ) : ℝ := max x 0

/-- The same inverse is used for the image identity and for the derivative of Q. -/
def reluInverse (z : ℝ) : ℝ := min z (z / 2)

/-- An actual primitive of the explicit scalar inverse; this construction is
specific to this sanity example and supplies nothing for the general CFMP input. -/
def reluQ (z : ℝ) : ℝ := ∫ t in (0 : ℝ)..z, reluInverse t

private theorem relu_continuous : Continuous relu :=
  continuous_id.max continuous_const

private theorem relu_monotone : Monotone relu := by
  intro x y hxy
  exact max_le_max hxy le_rfl

private theorem relu_inner_monotone (x y : ℝ) :
    0 ≤ inner ℝ (relu x - relu y) (x - y) := by
  rw [Real.inner_apply]
  rcases le_total y x with hyx | hxy
  · exact mul_nonneg (sub_nonneg.mpr (relu_monotone hyx)) (sub_nonneg.mpr hyx)
  · exact mul_nonneg_of_nonpos_of_nonpos
      (sub_nonpos.mpr (relu_monotone hxy)) (sub_nonpos.mpr hxy)

private theorem reluInverse_continuous : Continuous reluInverse :=
  continuous_id.min (continuous_id.div_const 2)

private theorem relu_inverse (x : ℝ) : reluInverse (T relu x) = x := by
  rcases le_total x 0 with hx | hx
  · dsimp [reluInverse, T, relu]
    rw [max_eq_right hx, add_zero, min_eq_left (by linarith : x ≤ x / 2)]
  · dsimp [reluInverse, T, relu]
    rw [max_eq_left hx, min_eq_right (by linarith : (x + x) / 2 ≤ x + x)]
    ring

private theorem relu_forward_inverse (z : ℝ) : T relu (reluInverse z) = z := by
  rcases le_total z 0 with hz | hz
  · dsimp [T, relu, reluInverse]
    rw [min_eq_left (by linarith : z ≤ z / 2), max_eq_right hz, add_zero]
  · dsimp [T, relu, reluInverse]
    rw [min_eq_right (by linarith : z / 2 ≤ z),
      max_eq_left (by linarith : 0 ≤ z / 2)]
    ring

private theorem relu_image : T relu '' (univ : Set ℝ) = univ := by
  ext z
  constructor
  · intro _
    trivial
  · intro _
    exact ⟨reluInverse z, mem_univ _, relu_forward_inverse z⟩

private theorem reluQ_hasFDerivAt (z : ℝ) :
    HasFDerivAt reluQ (innerSL ℝ (reluInverse z)) z := by
  have hd : HasDerivAt reluQ (reluInverse z) z :=
    intervalIntegral.integral_hasDerivAt_right
      (reluInverse_continuous.intervalIntegrable 0 z)
      reluInverse_continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      reluInverse_continuous.continuousAt
  apply hasFDerivAt_iff_hasDerivAt.mpr
  simpa only [innerSL_apply_apply, Real.inner_apply, mul_one] using hd

/-- The concrete example satisfies every input, with the actual image equal to
univ and a single explicit G and a single integral-defined Q. -/
theorem relu_recovery :
    (∀ x ∈ (univ : Set ℝ),
      HasFDerivAt (P relu reluQ) (innerSL ℝ (relu x)) x) ∧
      ConvexOn ℝ (univ : Set ℝ) (P relu reluQ) := by
  apply recover (G := reluInverse) isOpen_univ convex_univ relu_continuous.continuousOn
  · intro x hx y hy
    exact relu_inner_monotone x y
  · rw [relu_image]
    exact isOpen_univ
  · intro x hx
    exact relu_inverse x
  · intro z hz
    exact reluQ_hasFDerivAt z

/-- The example does not accidentally smuggle differentiability of F into its data. -/
theorem relu_not_differentiableAt_zero : ¬ DifferentiableAt ℝ relu 0 := by
  intro h
  have habs : (fun x : ℝ => 2 * relu x - x) = abs := by
    funext x
    rcases le_total 0 x with hx | hx
    · simp only [relu, max_eq_left hx, abs_of_nonneg hx]
      ring
    · simp only [relu, max_eq_right hx, abs_of_nonpos hx, mul_zero, zero_sub]
  have hh : DifferentiableAt ℝ (fun x : ℝ => 2 * relu x - x) 0 :=
    (h.const_mul 2).sub differentiableAt_id
  rw [habs] at hh
  exact not_differentiableAt_abs_zero hh

example : relu 1 = 1 ∧ relu (-1) = 0 := by
  norm_num [relu]

end TransientPotentialRecovery.Sanity
