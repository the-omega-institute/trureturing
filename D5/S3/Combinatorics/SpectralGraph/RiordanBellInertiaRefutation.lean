/- GID: D5/S3/Combinatorics/SpectralGraph/RiordanBellInertiaRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/RiordanBellInertiaRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/SpectralGraph/RiordanBellInertiaRefutation.claim; result=D5/S3/Combinatorics/SpectralGraph/RiordanBellInertiaRefutation.result; claim=D5/S3/Combinatorics/SpectralGraph/RiordanBellInertiaRefutation.claim
   digest: A Bell-type Riordan graph of order five has positive inertia three and negative inertia two. -/

import D5.S3.QuadraticForms.StructuredRankOneInertia
import Mathlib.RingTheory.PowerSeries.Basic

/-! Cheon--Jung--Kitaev--Mojallal, arXiv:1801.07021v1, Problem 6.11.
The external open-problem-resolution route is conditional on source-faithful
prefreeze review; issue #29551. All proofs are bind-only normalization and
applications of existing inertia results; no escape witness is claimed.
-/

set_option autoImplicit false
noncomputable section
open Matrix

namespace D5.S3.Combinatorics.SpectralGraph.RiordanBellInertiaRefutation

/-- Definition 2.2 and equation (2), with Bell parameter f = X*g.
The element i of Fin n represents the source label i.val + 1.
Integer remainder modulo positive two is the unique binary residue. -/
def adjacency (n : ℕ) (g : PowerSeries ℤ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    if j.val < i.val then
      ((PowerSeries.coeff (i.val - 1) (g * (PowerSeries.X * g) ^ j.val) % 2 : ℤ) : ℝ)
    else if i.val < j.val then
      ((PowerSeries.coeff (j.val - 1) (g * (PowerSeries.X * g) ^ i.val) % 2 : ℤ) : ℝ)
    else 0

private theorem adjacency_hermitian (n : ℕ) (g : PowerSeries ℤ) :
    (adjacency n g).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, star_trivial, adjacency]
  split_ifs <;> first | rfl | omega

/-- Problem 6.11, with all integer formal series and all positive orders.
The two indices count strictly signed eigenvalues with algebraic multiplicity;
zero eigenvalues contribute to neither count. -/
def claim : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (g : PowerSeries ℤ),
    RHLinalg.posIndex (adjacency_hermitian n g) ≤
      RHLinalg.negIndex (adjacency_hermitian n g)

private def witness : PowerSeries ℤ := 1 + PowerSeries.X ^ 3

private def A : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0,1,0,0,1; 1,0,1,0,0; 0,1,0,1,0; 0,0,1,0,1; 1,0,0,1,0]

private def B : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1,1,-1,-1,1; 1,-1,0,0,-1; 0,0,1,1,-1; 0,0,1,-1,1; 0,0,0,0,1]

private def d : Fin 5 → ℝ := ![2,-2,2,-2,2]

private theorem adjacency_witness : adjacency 5 witness = A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [adjacency, witness, A, pow_succ, PowerSeries.coeff_mul,
      Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero,
      PowerSeries.coeff_add, PowerSeries.coeff_X_pow, PowerSeries.coeff_one,
      PowerSeries.coeff_X]

private theorem A_hermitian : A.IsHermitian := by
  rw [← adjacency_witness]
  exact adjacency_hermitian 5 witness

private theorem B_det : B.det = 4 := by
  norm_num [B, Matrix.det_succ_row_zero, Fin.sum_univ_succ]

private theorem congruence : Bᴴ * A * B = diagonal d := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [B, A, d, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.conjTranspose_apply, Matrix.diagonal]

private theorem witness_inertia :
    RHLinalg.posIndex (adjacency_hermitian 5 witness) = 3 ∧
    RHLinalg.negIndex (adjacency_hermitian 5 witness) = 2 := by
  have hB : IsUnit B.det := by rw [B_det]; exact isUnit_iff_ne_zero.mpr (by norm_num)
  have h := D5.S3.Weil.Pick.InvertibleHermitianInertiaPullback.inertia_invariant_of_isUnit_det
    A_hermitian B hB
  have hd := D5.S3.QuadraticForms.StructuredRankOneInertia.diagonal_counts d
  have heq : (Bᴴ * A * B) = diagonal d := congruence
  have hp : RHLinalg.posIndex A_hermitian = 3 := by
    rw [← h.1]
    convert hd.1 using 1 <;> norm_num [heq, d, Fin.sum_univ_succ, Finset.univ_fin_succ]
  have hn : RHLinalg.negIndex A_hermitian = 2 := by
    rw [← h.2]
    convert hd.2 using 1 <;> norm_num [heq, d, Fin.sum_univ_succ, Finset.univ_fin_succ]
  have hA := adjacency_witness
  subst hA
  exact ⟨hp, hn⟩

/-- The exact negation of the complete universal question, witnessed by n=5
and the integer formal power series 1+X^3. -/
theorem result : ¬ claim := by
  intro h
  have hle := h 5 (by norm_num) witness
  rw [witness_inertia.1, witness_inertia.2] at hle
  omega

#print axioms result

end D5.S3.Combinatorics.SpectralGraph.RiordanBellInertiaRefutation
