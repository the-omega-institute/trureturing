/- GID: D5/S3/SpectralTopology/FiniteHermitianLocalizer
   generality: G
   mirror-B: D5/B/S3/SpectralTopology/FiniteHermitianLocalizer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite operator and position matrix determine a Hermitian block localizer with an exact zero-scale square. -/

import D5.S3.Weil.ZetaLinear.PosIndex
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic

/-!
# Finite Hermitian spectral localizer

A finite complex operator `H`, a Hermitian position matrix `X`, a spatial
centre `x`, a spectral point `z`, and a real scale `kappa` determine the block
matrix

`[[kappa (X-xI), H-zI], [(H-zI)ᴴ, -kappa (X-xI)]]`.

The matrix is Hermitian. At zero localization scale its square is block
diagonal with the two singular Gram matrices of `H-zI`. These are the finite
algebraic identities underlying the point-gap spectral localizer. No
infinite-volume index, K-theory class, mobility gap, or perturbation theorem
is claimed here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.SpectralTopology.FiniteHermitianLocalizer

noncomputable section

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- Shift a finite operator by a complex spectral point. -/
def centeredOperator (H : Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ :=
  H - z • 1

/-- Shift a Hermitian position matrix by a real centre. -/
def centeredPosition (X : Matrix n n ℂ) (x : ℝ) : Matrix n n ℂ :=
  X - (x : ℂ) • 1

/-- The finite Hermitian block spectral localizer. -/
def finiteHermitianLocalizer
    (X H : Matrix n n ℂ) (x : ℝ) (z : ℂ) (kappa : ℝ) :
    Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  Matrix.fromBlocks
    ((kappa : ℂ) • centeredPosition X x)
    (centeredOperator H z)
    (centeredOperator H z)ᴴ
    (-((kappa : ℂ) • centeredPosition X x))

/-- A real shift preserves Hermitianity of the position block. -/
theorem centeredPosition_isHermitian
    {X : Matrix n n ℂ} (hX : X.IsHermitian) (x : ℝ) :
    (centeredPosition X x).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp [centeredPosition, Matrix.conjTranspose_apply, hX.apply]

/-- The finite block localizer is Hermitian whenever the position matrix is. -/
theorem finiteHermitianLocalizer_isHermitian
    {X H : Matrix n n ℂ} (hX : X.IsHermitian)
    (x : ℝ) (z : ℂ) (kappa : ℝ) :
    (finiteHermitianLocalizer X H x z kappa).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [finiteHermitianLocalizer, centeredOperator,
      centeredPosition, Matrix.conjTranspose_apply, hX.apply]

/-- At zero localization scale the localizer is purely off diagonal. -/
theorem finiteHermitianLocalizer_zero_scale
    (X H : Matrix n n ℂ) (x : ℝ) (z : ℂ) :
    finiteHermitianLocalizer X H x z 0 =
      Matrix.fromBlocks 0 (centeredOperator H z)
        (centeredOperator H z)ᴴ 0 := by
  simp [finiteHermitianLocalizer]

/-- The square of the zero-scale localizer is the direct sum of the two
singular Gram matrices. -/
theorem finiteHermitianLocalizer_zero_scale_sq
    (X H : Matrix n n ℂ) (x : ℝ) (z : ℂ) :
    finiteHermitianLocalizer X H x z 0 *
        finiteHermitianLocalizer X H x z 0 =
      Matrix.fromBlocks
        (centeredOperator H z * (centeredOperator H z)ᴴ)
        0 0
        ((centeredOperator H z)ᴴ * centeredOperator H z) := by
  rw [finiteHermitianLocalizer_zero_scale]
  rw [Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp

/-- The zero-scale localizer vanishes exactly when the centred operator does. -/
theorem finiteHermitianLocalizer_zero_scale_eq_zero_iff
    (X H : Matrix n n ℂ) (x : ℝ) (z : ℂ) :
    finiteHermitianLocalizer X H x z 0 = 0 ↔
      centeredOperator H z = 0 := by
  rw [finiteHermitianLocalizer_zero_scale]
  constructor
  · intro h
    ext i j
    have hij := congrArg (fun M : Matrix (n ⊕ n) (n ⊕ n) ℂ =>
      M (Sum.inl i) (Sum.inr j)) h
    simpa using hij
  · intro h
    simp [h]

/-- Negative inertia of the Hermitian localizer is a finite natural number. -/
def localizerNegativeIndex
    {X H : Matrix n n ℂ} (hX : X.IsHermitian)
    (x : ℝ) (z : ℂ) (kappa : ℝ) : ℕ :=
  RHLinalg.negIndex
    (finiteHermitianLocalizer_isHermitian hX x z kappa)

example :
    finiteHermitianLocalizer
        (0 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 0 0 = 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [finiteHermitianLocalizer, centeredOperator, centeredPosition]

#print axioms centeredPosition_isHermitian
#print axioms finiteHermitianLocalizer_isHermitian
#print axioms finiteHermitianLocalizer_zero_scale_sq
#print axioms finiteHermitianLocalizer_zero_scale_eq_zero_iff

end

end D5.S3.SpectralTopology.FiniteHermitianLocalizer
