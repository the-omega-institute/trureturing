/- GID: D5/S3/QuantumBounds/PeritoTensorBlockBound
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bound unitary tensor sums by their scalar coefficients on the unit circle. -/

import D5.S3.Quantum.BlockNorm.EssentiallyHermitian
import D5.S3.Observer.WindowRegister
/-!
# Unitary tensor blocks

The Euclidean operator norm of a tensor sum is controlled by its scalar
coefficients on the unit circle. Diagonalizing the first unitary makes the
operator a direct sum of Bob-vector blocks. Triangle estimates within each
block and the sum of squared block norms give the uniform bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Kronecker Matrix.Norms.L2Operator
open Matrix
noncomputable section
namespace D5.S3.QuantumBounds.PeritoTensorBlockBound

/-- A unitary matrix preserves the Euclidean vector norm. -/
private theorem unitary_norm_map {a : Type*} [Fintype a] [DecidableEq a]
    (U : Matrix a a ℂ) (hU : U ∈ unitaryGroup a ℂ) (v : EuclideanSpace ℂ a) :
    ‖toEuclideanCLM (𝕜 := ℂ) U v‖ = ‖v‖ :=
  ContinuousLinearMap.norm_map_of_mem_unitary (Unitary.map_mem (toEuclideanCLM (𝕜 := ℂ)) hU) v

/-- Each first-factor coordinate is an invariant Bob-vector block. -/
private theorem diagonal_tensor_action {n m d : ℕ}
    (c : Fin d → Fin n → ℂ) (B : Fin d → Matrix (Fin m) (Fin m) ℂ)
    (v : EuclideanSpace ℂ (Fin n × Fin m)) (i : Fin n) :
    WithLp.toLp 2 (fun j => (toEuclideanCLM (𝕜 := ℂ) (∑ y, diagonal (c y) ⊗ₖ B y) v) (i,j)) =
      ∑ y, c y i • toEuclideanCLM (𝕜 := ℂ) (B y) (WithLp.toLp 2 (fun j => v (i,j))) := by
  ext j
  simp only [ofLp_toEuclideanCLM, sum_mulVec, Finset.sum_apply,
    WithLp.ofLp_sum, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro y hy
  simp [mulVec, dotProduct, Fintype.sum_prod_type, diagonal_apply, Finset.mul_sum, mul_assoc]

/-- A uniform bound for the diagonal blocks bounds the whole tensor operator. -/
theorem norm_diagonal_tensor_sum_le {n m d : ℕ}
    (c : Fin d → Fin n → ℂ) (B : Fin d → Matrix (Fin m) (Fin m) ℂ)
    (hB : ∀ y, B y ∈ unitaryGroup (Fin m) ℂ)
    (K : ℝ) (hK : 0 ≤ K) (hc : ∀ i, ∑ y, ‖c y i‖ ≤ K) :
    ‖∑ y, diagonal (c y) ⊗ₖ B y‖ ≤ K := by
  rw [← l2_opNorm_toEuclideanCLM]
  apply ContinuousLinearMap.opNorm_le_bound _ hK
  intro v
  let T := toEuclideanCLM (𝕜 := ℂ) (∑ y, diagonal (c y) ⊗ₖ B y)
  let row (i : Fin n) : EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 (fun j => v (i,j))
  have hrow (i : Fin n) :
      ‖WithLp.toLp 2 (fun j => (T v) (i,j))‖ ≤ K * ‖row i‖ := by
    rw [diagonal_tensor_action]
    calc
      ‖∑ y, c y i • toEuclideanCLM (𝕜 := ℂ) (B y) (row i)‖ ≤
          ∑ y, ‖c y i • toEuclideanCLM (𝕜 := ℂ) (B y) (row i)‖ := norm_sum_le _ _
      _ = (∑ y, ‖c y i‖) * ‖row i‖ := by
        simp only [norm_smul, unitary_norm_map _ (hB _)]; rw [Finset.sum_mul]
      _ ≤ K * ‖row i‖ := mul_le_mul_of_nonneg_right (hc i) (norm_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  calc
    ‖T v‖ ^ 2 = ∑ i, ‖WithLp.toLp 2 (fun j => (T v) (i,j))‖ ^ 2 := by
      simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    _ ≤ ∑ i, (K * ‖row i‖) ^ 2 := Finset.sum_le_sum fun i _ =>
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hrow i)
    _ = (K * ‖v‖) ^ 2 := by
      simp only [mul_pow, EuclideanSpace.norm_sq_eq, row,
        Fintype.sum_prod_type, Finset.mul_sum]

/-- Unitary diagonalization has unit-circle diagonal entries. -/
private theorem unitary_diagonalization {n : ℕ}
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U ∈ unitaryGroup (Fin n) ℂ) :
    ∃ P ∈ unitaryGroup (Fin n) ℂ, ∃ z : Fin n → ℂ,
      (∀ i, ‖z i‖ = 1) ∧ star P * U * P = diagonal z := by
  let : IsStarNormal U := isStarNormal_of_mem_unitary hU
  obtain ⟨P, hP, z, hz⟩ := exists_mem_unitaryGroup_star_mul_mul_eq_diagonal U
  refine ⟨P, hP, z, ?_, hz⟩
  have hd : diagonal z ∈ unitaryGroup (Fin n) ℂ := by
    rw [← hz]
    exact (unitaryGroup (Fin n) ℂ).mul_mem
      ((unitaryGroup (Fin n) ℂ).mul_mem (Unitary.star_mem hP) hU) hP
  intro i
  have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i i)
    (mem_unitaryGroup_iff'.mp hd)
  have hzi : star (z i) * z i = 1 := by
    simpa [star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal] using he
  have hn := congrArg norm hzi
  simp only [norm_mul, norm_star, norm_one] at hn
  nlinarith [norm_nonneg (z i)]

open D5.S3.Observer.WindowRegister

/-- The tensor sum is bounded by any uniform unit-circle coefficient bound. -/
theorem tensor_block_bound {n m d : ℕ}
    (U : Matrix (Fin n) (Fin n) ℂ) (B : Fin d → Matrix (Fin m) (Fin m) ℂ)
    (hU : U ∈ unitaryGroup (Fin n) ℂ) (hB : ∀ y, B y ∈ unitaryGroup (Fin m) ℂ)
    (K : ℝ) (hscalar : ∀ z : ℂ, ‖z‖ = 1 → ∑ y : Fin d,
      ‖1 + windowRoot d ^ y.val * z‖ ≤ K) :
    ‖∑ y : Fin d, (1 + windowRoot d ^ y.val • U) ⊗ₖ B y‖ ≤ K := by
  have hK : 0 ≤ K := (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans
    (hscalar 1 norm_one)
  obtain ⟨P, hP, z, hz, hdiag⟩ := unitary_diagonalization U hU
  let Q : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ := P ⊗ₖ 1
  have hQ : Q ∈ unitaryGroup (Fin n × Fin m) ℂ :=
    kronecker_mem_unitary hP (unitaryGroup (Fin m) ℂ).one_mem
  have hconj : star Q * (∑ y : Fin d, (1 + windowRoot d ^ y.val • U) ⊗ₖ B y) * Q =
      ∑ y : Fin d, diagonal (fun i => 1 + windowRoot d ^ y.val * z i) ⊗ₖ B y := by
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y hy
    simp only [Q, star_eq_conjTranspose, conjTranspose_kronecker,
      conjTranspose_one, ← mul_kronecker_mul, one_mul, mul_one]
    congr 1
    change star P * (1 + windowRoot d ^ y.val • U) * P = _
    rw [mul_add, add_mul, mul_one, mul_smul_comm, smul_mul_assoc,
      mem_unitaryGroup_iff'.mp hP, hdiag]
    ext i j
    by_cases hij : i = j <;> simp [one_apply, hij]
  have hnorm : ‖star Q * (∑ y : Fin d, (1 + windowRoot d ^ y.val • U) ⊗ₖ B y) * Q‖ =
      ‖∑ y : Fin d, (1 + windowRoot d ^ y.val • U) ⊗ₖ B y‖ := by
    rw [CStarRing.norm_mul_mem_unitary _ hQ,
      CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem hQ)]
  rw [← hnorm, hconj]
  exact norm_diagonal_tensor_sum_le _ B hB K hK (fun i => hscalar (z i) (hz i))
end D5.S3.QuantumBounds.PeritoTensorBlockBound
