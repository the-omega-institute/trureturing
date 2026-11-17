/- GID: D5/S3/FluidDynamics/Vortices/AlternatingPolygonDecomposition
   generality: I
   mirror-B: D5/B/S3/FluidDynamics/Vortices/AlternatingPolygonDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete invariant direct sum and geometric multiplicities of the actual vortex derivative. -/

import D5.S3.FluidDynamics.Vortices.AlternatingPolygonJordan
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonMultiplicity

/-! Explicit invariant blocks, reconstruction, uniqueness and multiplicities. -/
noncomputable section
open scoped BigOperators

namespace D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition
open AlternatingPolygonSpectrum AlternatingPolygonModes AlternatingPolygonJordan
open AlternatingPolygonMultiplicity

/-- Injection of the entire two-dimensional Fourier block into actual Cartesian space. -/
def block (m : ℕ) [NeZero (2 * m)] (q : ZMod (2 * m)) :
    (ℂ × ℂ) →ₗ[ℂ] Cartesian m :=
  (cartesianCoordinates m).symm.toLinearMap.comp (LinearMap.single ℂ (fun _ => ℂ × ℂ) q)

@[simp] theorem coordinates_block (m : ℕ) [NeZero (2 * m)]
    (q : ZMod (2 * m)) (w : ℂ × ℂ) :
    cartesianCoordinates m (block m q w) = Pi.single q w :=
  (cartesianCoordinates m).apply_symm_apply _

/-- The actual restriction action on each block, including the neutral block. -/
theorem block_restriction (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m)
    (q : ZMod (2 * m)) (w : ℂ × ℂ) :
    actualOperator m (block m q w) = block m q
      ((ell m q : ℂ) * w.2, ((ell m (q + m) + 1 : ℝ) : ℂ) * w.1) := by
  classical
  apply (cartesianCoordinates m).injective
  rw [actual_normal_form m hm, coordinates_block, coordinates_block]
  funext p
  by_cases hp : p = q
  · subst p; simp [modeOperator, pairedOperator]
  · simp [modeOperator, pairedOperator, Pi.single_eq_of_ne hp]

/-- Completeness: every Cartesian displacement is the sum of its actual invariant blocks. -/
theorem reconstruct (m : ℕ) [NeZero (2 * m)] (v : Cartesian m) :
    v = ∑ q : ZMod (2 * m), block m q (cartesianCoordinates m v q) := by
  classical
  apply (cartesianCoordinates m).injective
  simp only [map_sum, coordinates_block, LinearMap.sum_single_apply]

/-- Directness: the complete block expansion has unique coefficients. -/
theorem unique_coefficients (m : ℕ) [NeZero (2 * m)] (w : Modes m) :
    (∑ q : ZMod (2 * m), block m q (w q)) = 0 ↔ w = 0 := by
  classical
  constructor
  · intro h
    have h' := congrArg (cartesianCoordinates m) h
    simpa only [map_sum, coordinates_block, LinearMap.sum_single_apply, map_zero] using h'
  · rintro rfl
    simp

/-- The actual invariant subspace belonging to a single Fourier label. -/
def invariantSpace (m : ℕ) [NeZero (2 * m)] (q : ZMod (2 * m)) :
    Submodule ℂ (Cartesian m) := (block m q).range

theorem invariantSpace_finrank (m : ℕ) [NeZero (2 * m)] (q : ZMod (2 * m)) :
    Module.finrank ℂ (invariantSpace m q) = 2 := by
  have hi : Function.Injective (block m q) := by
    intro x y h
    have h' := congrArg (fun v => cartesianCoordinates m v q) h
    simpa only [coordinates_block, Pi.single_eq_same] using h'
  rw [invariantSpace, LinearMap.finrank_range_of_inj hi]
  simp

/-- All complex nonzero geometric multiplicities equal the full algebraic multiplicities. -/
theorem geometric_eq_algebraic (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m)
    {μ : ℂ} (hμ : μ ≠ 0) :
    Module.finrank ℂ ((actualOperator m).eigenspace μ) =
      (((jacobian (2 * m)).map Complex.ofRealHom).charpoly).rootMultiplicity μ := by
  rw [← actual_nonzero_semisimple m hm hμ,
    LinearMap.finrank_maxGenEigenspace_eq, actualOperator, Matrix.charpoly_toLin']

/-- Exact geometric multiplicity at each folded label, with all collisions counted. -/
theorem geometric_multiplicity_of_mode (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m)
    {r : ℕ} (hr : r ≤ m) (μ : ℂ) (hμ : μ ≠ 0)
    (hroot : μ ^ 2 = (squaredValue m r : ℂ)) :
    Module.finrank ℂ ((actualOperator m).eigenspace μ) =
      if r = 0 ∨ r = m then 1 else 2 := by
  rw [geometric_eq_algebraic m hm hμ]
  exact algebraic_multiplicity_of_mode m hm hr μ hμ hroot

end D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition
