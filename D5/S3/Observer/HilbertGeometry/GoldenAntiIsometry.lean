/- GID: D5/S3/Observer/HilbertGeometry/GoldenAntiIsometry
   generality: I
   mirror-B: D5/B/S3/Observer/HilbertGeometry/GoldenAntiIsometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The Fibonacci update negates the golden quadratic form on every real Hilbert space. -/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic

/- Library-search audit trail (2026-09-02):
   * `GoldenCoding.golden_lorentz_update` is the two-dimensional precursor,
     not a duplicate of the arbitrary-Hilbert-space statement below.
   * Pinned Mathlib supplies `innerₗ`, `LinearMap.compl₁₂`,
     `BilinMap.toQuadraticMap`, and the product projections used here.
   * Loogle and LeanSearch found the supporting inner-product identities but
     no packaged Fibonacci anti-isometry on an arbitrary Hilbert space. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.HilbertGeometry.GoldenAntiIsometry

universe u

/-- The phase space `V = H ⊕ H` from the source theorem. -/
abbrev HilbertPhase (H : Type u) := H × H

/-- The bilinear presentation of
`Q(X,Y) = ‖X‖^2 - ⟨X,Y⟩ - ‖Y‖^2`. -/
noncomputable def goldenHilbertBilinear
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] :
    LinearMap.BilinForm ℝ (HilbertPhase H) :=
  let first : HilbertPhase H →ₗ[ℝ] H := LinearMap.fst ℝ H H
  let second : HilbertPhase H →ₗ[ℝ] H := LinearMap.snd ℝ H H
  (innerₗ H).compl₁₂ first first -
    (innerₗ H).compl₁₂ first second -
    (innerₗ H).compl₁₂ second second

/-- The source quadratic form on `H ⊕ H`, bundled as a Mathlib
`QuadraticForm`. -/
noncomputable def goldenHilbertForm
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] :
    QuadraticForm ℝ (HilbertPhase H) :=
  (goldenHilbertBilinear H).toQuadraticMap

/-- The dimension-independent Fibonacci update `F(X,Y) = (X+Y,X)`, bundled
as a linear map on `H ⊕ H`. -/
def goldenHilbertUpdate
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] :
    HilbertPhase H →ₗ[ℝ] HilbertPhase H :=
  ((LinearMap.fst ℝ H H + LinearMap.snd ℝ H H).prod
    (LinearMap.fst ℝ H H))

private theorem goldenHilbertForm_apply
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (X Y : H) :
    goldenHilbertForm H (X, Y) =
      ‖X‖ ^ 2 - inner ℝ X Y - ‖Y‖ ^ 2 := by
  simp [goldenHilbertForm, goldenHilbertBilinear]

/-- Theorem 736.1: the Fibonacci update is an anti-isometry of the golden
quadratic form in every real Hilbert dimension. -/
theorem golden_anti_isometry
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [hComplete : CompleteSpace H] (X Y : H) :
    goldenHilbertForm H (goldenHilbertUpdate H (X, Y)) =
      -goldenHilbertForm H (X, Y) := by
  rw [@goldenHilbertForm_apply H _ _ hComplete,
    @goldenHilbertForm_apply H _ _ hComplete]
  change
    ‖X + Y‖ ^ 2 - inner ℝ (X + Y) X - ‖X‖ ^ 2 =
      -(‖X‖ ^ 2 - inner ℝ X Y - ‖Y‖ ^ 2)
  rw [norm_add_sq_real, inner_add_left, real_inner_self_eq_norm_sq]
  rw [real_inner_comm Y X]
  ring

-- Reverse probe for CAS-A1: positive values cross to the negative sector.
example
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (X Y : H) (hPositive : 0 < goldenHilbertForm H (X, Y)) :
    goldenHilbertForm H (goldenHilbertUpdate H (X, Y)) < 0 := by
  rw [golden_anti_isometry]
  exact neg_neg_of_pos hPositive

-- Collapse probe for CAS-A1: the bundled form separates concrete phase points.
example :
    goldenHilbertForm ℝ ((1 : ℝ), 0) ≠
      goldenHilbertForm ℝ (0, (1 : ℝ)) := by
  norm_num [goldenHilbertForm_apply]

-- The universal identity includes the zero phase point without relying on it.
example :
    goldenHilbertForm ℝ (goldenHilbertUpdate ℝ (0, 0)) =
      -goldenHilbertForm ℝ (0, 0) := by
  exact golden_anti_isometry 0 0

#print axioms golden_anti_isometry

end D5.S3.Observer.HilbertGeometry.GoldenAntiIsometry
