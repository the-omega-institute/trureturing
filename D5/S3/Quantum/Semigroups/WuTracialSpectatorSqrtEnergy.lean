/- GID: D5/S3/Quantum/Semigroups/WuTracialSpectatorSqrtEnergy
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuTracialSpectatorSqrtEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact tracial square-root cell and spectator energy bound on the complex CAR frame. -/

/-
proof_shape: content
admission_basis: escape-witness
escape_witness: The cubic cell differs from the squared square-root difference by an explicit
factorized remainder. On the actual spectator jump, the tracial trace exceeds
the compression remainder by half the squared norm of the diagonal block difference.
The directed cell sum gives the energy hypothesis of rankTwo_joint_lower.
-/

import D5.S3.Quantum.Semigroups.WuTwoTemperatureCubicPhysicalBridge
import D5.S3.Quantum.Semigroups.WuRankTwoSpectatorCompression

/-! Section 1 of the tracial spectator rank-two estimate, with ordinary traces
and the actual left CAR jump on the complex occupation frame. -/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder Kronecker

namespace D5.S3.Quantum.Semigroups.WuTracialSpectatorSqrtEnergy

open WuCubicOperatorBridge (Frame Mat Occupation)
open WuTwoModeCliffordPluecker (jump jump_left tracial)
open WuTwoTemperatureCubicPhysicalBridge (cost weight energy)
open WuRankTwoSpectatorCompression (coldMarginal liftCold trace_remainder_sq)
open WuCubicThermalBasis (e)
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence (pauliMatrix)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceLeft)
open private gamma from D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private trace_spectral_sandwich from D5.S3.Quantum.Semigroups.WuCubicOperatorBridge
open private jump_car tracial_eq_sub from D5.S3.Quantum.Semigroups.WuTwoModeCliffordPluecker

/-- The sharp polynomial remainder before substitution of the square roots. -/
theorem scalar_polynomial_identity (a b : ℝ) :
    (9 / 8 : ℝ) * (a^2 - b^2)^2 * (a^2 + b^2) - (a^3 - b^3)^2 =
      (a - b)^4 * (a^2 + 4*a*b + b^2) / 8 := by
  ring

private theorem sqrt_cube_eq_rpow (u : ℝ) (hu : 0 ≤ u) :
    Real.sqrt u ^ 3 = u ^ (3 / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hu]
  norm_num

/-- The exact loss in the cubic-to-square-root comparison, including zero roots. -/
theorem sharp_scalar_identity (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (9 / 8 : ℝ) * (u-v)^2 * (u+v) -
      (u ^ (3 / 2 : ℝ) - v ^ (3 / 2 : ℝ))^2 =
        (Real.sqrt u - Real.sqrt v)^4 *
          (u + 4 * Real.sqrt u * Real.sqrt v + v) / 8 := by
  simpa only [Real.sq_sqrt hu, Real.sq_sqrt hv, sqrt_cube_eq_rpow u hu,
    sqrt_cube_eq_rpow v hv] using scalar_polynomial_identity (Real.sqrt u) (Real.sqrt v)

theorem tracial_cell_lower (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (u ^ (3 / 2 : ℝ) - v ^ (3 / 2 : ℝ))^2 ≤ cost 1 u v := by
  have he := sharp_scalar_identity u v hu hv
  have hn : 0 ≤ (Real.sqrt u - Real.sqrt v)^4 *
      (u + 4 * Real.sqrt u * Real.sqrt v + v) / 8 := by positivity
  unfold cost
  norm_num [gamma]
  linarith only [he, hn]

/-- Difference of the two diagonal spectator blocks in the cold algebra. -/
def diagonalDifference (A : Mat) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i k => A (0, i) (0, k) - A (1, i) (1, k)

set_option maxHeartbeats 2000000 in
/-- The two gain terms exchange the diagonal spectator blocks. Their trace
pairing with A only sees these two blocks. -/
private theorem block_trace_identity (A : Mat) :
    2 * trace (coldMarginal A * coldMarginal A) -
      trace (A * ((jump 1)ᴴ * A * jump 1)) -
      trace (A * (jump 1 * A * (jump 1)ᴴ)) =
        (1 / 2 : ℂ) * trace (diagonalDifference A * diagonalDifference A) := by
  norm_num [coldMarginal, partialTraceLeft, diagonalDifference, jump_left,
    pauliMatrix, e, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Matrix.conjTranspose_apply, Matrix.mul_apply, Matrix.trace, Matrix.diag_apply,
    Matrix.smul_apply, Complex.real_smul, Complex.ofReal_div, Complex.star_def,
    Fintype.sum_prod_type, Fin.sum_univ_two] <;>
    ring

/-- The exact excess of the physical tracial spectator Dirichlet form over
the squared remainder of the normalized spectator partial trace. -/
theorem tracial_excess (A : Mat) (hA : A.IsHermitian) :
    (trace (A * tracial 1 A)).re -
      (trace ((A - liftCold (coldMarginal A)) *
        (A - liftCold (coldMarginal A)))).re =
      (1 / 2 : ℝ) * (trace ((diagonalDifference A)ᴴ * diagonalDifference A)).re := by
  have hB : (diagonalDifference A).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i k
    simp only [diagonalDifference, star_sub, hA.apply]
  have hblock := congrArg Complex.re (block_trace_identity A)
  norm_num [Complex.sub_re, Complex.mul_re] at hblock
  rw [hB.eq, trace_remainder_sq, tracial_eq_sub]
  simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  linarith only [hblock]

theorem remainder_le_tracial (A : Mat) (hA : A.IsHermitian) :
    (trace ((A - liftCold (coldMarginal A)) *
      (A - liftCold (coldMarginal A)))).re ≤ (trace (A * tracial 1 A)).re := by
  have h := tracial_excess A hA
  have hn : 0 ≤ (trace ((diagonalDifference A)ᴴ * diagonalDifference A)).re :=
    (Complex.le_def.mp (Matrix.posSemidef_conjTranspose_mul_self
      (diagonalDifference A)).trace_nonneg).1
  linarith only [h, hn]

/-- The square-root matrix of the cubic state in its actual complex frame. -/
def sqrtFrame (U : Frame) (v : Fin 4 → ℝ) : Mat :=
  U * diagonal (fun i => ((v i ^ (3 / 2 : ℝ) : ℝ) : ℂ)) * Uᴴ

/-- The same directed squared jump weights appearing in the physical cubic
energy evaluate the ordinary quadratic tracial Dirichlet form. -/
theorem tracial_trace_frame (U : Frame) (hU : Uᴴ * U = 1) (hUU : U * Uᴴ = 1)
    (v : Fin 4 → ℝ) :
    (trace (sqrtFrame U v * tracial 1 (sqrtFrame U v))).re =
      ∑ i, ∑ k, (v i ^ (3 / 2 : ℝ) - v k ^ (3 / 2 : ℝ))^2 * weight U 1 i k := by
  let s : Fin 4 → ℝ := fun i => v i ^ (3 / 2 : ℝ)
  let A := sqrtFrame U v
  let J := jump 1
  have hs (p q : ℕ) :
      (trace (A^p * Jᴴ * A^q * J)).re =
        ∑ i, ∑ k, weight U 1 i k * s k ^ p * s i ^ q :=
    trace_spectral_sandwich U hU hUU s J p q
  have hk : (trace (A^2 * Jᴴ * J)).re =
      ∑ i, ∑ k, weight U 1 i k * s k ^ 2 := by
    simpa only [pow_zero, Matrix.mul_one, mul_one] using hs 2 0
  have hi : (trace (A^2 * J * Jᴴ)).re =
      ∑ i, ∑ k, weight U 1 i k * s i ^ 2 := by
    have htrace : trace (A^2 * J * Jᴴ) = trace (Jᴴ * A^2 * J) := by
      calc
        _ = trace (A^2 * (J * Jᴴ)) := congrArg Matrix.trace (Matrix.mul_assoc (A^2) J Jᴴ)
        _ = trace (J * Jᴴ * A^2) := Matrix.trace_mul_comm (A^2) (J * Jᴴ)
        _ = _ := (Matrix.trace_mul_cycle Jᴴ (A^2) J).symm
    calc
      _ = (trace (Jᴴ * A^2 * J)).re := congrArg Complex.re htrace
      _ = _ := by simpa only [pow_zero, Matrix.one_mul, mul_one] using hs 0 2
  have hcross : (trace (A * Jᴴ * A * J)).re =
      ∑ i, ∑ k, weight U 1 i k * s k * s i := by
    simpa only [pow_one] using hs 1 1
  have hflip : trace (A * J * A * Jᴴ) = trace (A * Jᴴ * A * J) := by
    rw [Matrix.mul_assoc (A * J) A Jᴴ, Matrix.mul_assoc (A * Jᴴ) A J,
      Matrix.trace_mul_comm]
  have hmass : (trace (A^2)).re =
      (trace (A^2 * Jᴴ * J)).re + (trace (A^2 * J * Jᴴ)).re := by
    rw [← Complex.add_re, ← Matrix.trace_add,
      Matrix.mul_assoc (A^2) Jᴴ J, Matrix.mul_assoc (A^2) J Jᴴ,
      ← Matrix.mul_add, add_comm (Jᴴ * J) (J * Jᴴ),
      show J * Jᴴ + Jᴴ * J = 1 from jump_car 1, Matrix.mul_one]
  change (trace (A * tracial 1 A)).re = _
  rw [tracial_eq_sub]
  change (trace (A * (A - Jᴴ * A * J - J * A * Jᴴ))).re = _
  simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  rw [← pow_two, ← Matrix.mul_assoc A (Jᴴ * A) J,
    ← Matrix.mul_assoc A Jᴴ A, ← Matrix.mul_assoc A (J * A) Jᴴ,
    ← Matrix.mul_assoc A J A, hflip, hmass, hk, hi, hcross]
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  change _ = (s i - s k)^2 * weight U 1 i k
  ring

/-- Precisely the energy hypothesis of rankTwo_joint_lower, on the same
square-root frame and the same normalized cold marginal. -/
theorem hEs (U : Frame) (hU : Uᴴ * U = 1) (hUU : U * Uᴴ = 1)
    (v : Fin 4 → ℝ) (hv : ∀ i, 0 ≤ v i) :
    let A := sqrtFrame U v
    (trace ((A - liftCold (coldMarginal A)) *
      (A - liftCold (coldMarginal A)))).re ≤ energy 1 U 1 v := by
  let A := sqrtFrame U v
  have hD : (diagonal (fun i => ((v i ^ (3 / 2 : ℝ) : ℝ) : ℂ))).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    exact Complex.le_def.mpr ⟨Real.rpow_nonneg (hv i) (3 / 2 : ℝ), rfl⟩
  have hA : A.PosSemidef := hD.mul_mul_conjTranspose_same U
  refine (remainder_le_tracial A hA.isHermitian).trans ?_
  change (trace (sqrtFrame U v * tracial 1 (sqrtFrame U v))).re ≤ _
  rw [tracial_trace_frame U hU hUU]
  unfold energy
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro k _
  exact mul_le_mul_of_nonneg_right (tracial_cell_lower _ _ (hv i) (hv k))
    (Complex.normSq_nonneg _)

end D5.S3.Quantum.Semigroups.WuTracialSpectatorSqrtEnergy
