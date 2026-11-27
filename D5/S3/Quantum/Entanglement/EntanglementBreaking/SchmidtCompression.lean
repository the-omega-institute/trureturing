/- GID: D5/S3/Quantum/Entanglement/EntanglementBreaking/SchmidtCompression
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EntanglementBreaking/SchmidtCompression
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Schmidt-restricted quadratic bounds imply separable Choi compressions. -/

import D5.S3.Quantum.Entanglement.EntanglementBreaking.PPTTrace
import D5.S3.Quantum.Entanglement.EntanglementBreaking.RightIsometry
import D5.S3.Quantum.Entanglement.AbsoluteSeparability.ContractionBlocks
import D5.S3.Quantum.Entanglement.WitnessKernelTraceCriteriaRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Quantum.Entanglement.EntanglementBreaking

open _root_.Matrix
open scoped ComplexOrder
open D5.S3.Resource.CompositeCones
open D5.S3.Resource.EntanglementWitness
open D5.S3.Quantum.Entanglement.AbsoluteSeparability.ContractionBlocks
open D5.S3.Quantum.Entanglement.WitnessKernelTraceCriteriaRefutation (schmidtRank)
open scoped Kronecker _root_.Matrix.Norms.L2Operator

/-- The bound in the hypothesis, using the pinned coefficient-matrix Schmidt rank. -/
def SchmidtQuadraticBound {d : ℕ} (k : ℕ)
    (H : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Prop :=
  ∀ v : Fin d × Fin d → ℂ, ‖WithLp.toLp 2 v‖ = 1 →
    schmidtRank v ≤ k → ‖star v ⬝ᵥ (H *ᵥ v)‖ ≤ (d : ℝ) / (32 * (k : ℝ))

private theorem quadratic_congruence {a b : Type} [Fintype a] [Fintype b]
    (H : Matrix b b ℂ) (L : Matrix b a ℂ) (x : a → ℂ) :
    star (L *ᵥ x) ⬝ᵥ (H *ᵥ (L *ᵥ x)) = star x ⬝ᵥ ((Lᴴ * H * L) *ᵥ x) := by
  rw [star_mulVec, ← dotProduct_mulVec]
  simp only [mulVec_mulVec, Matrix.mul_assoc]

private theorem lift_unit {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    [DecidableEq b] (L : Matrix b a ℂ) (hL : Lᴴ * L = 1) (x : a → ℂ)
    (hx : ‖WithLp.toLp 2 x‖ = 1) : ‖WithLp.toLp 2 (L *ᵥ x)‖ = 1 := by
  have he := quadratic_congruence (1 : Matrix b b ℂ) L x
  simp only [one_mulVec, Matrix.mul_one, hL] at he
  have hn : ‖WithLp.toLp 2 (L *ᵥ x)‖^2 = ‖WithLp.toLp 2 x‖^2 := by
    rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ]
    simp only [EuclideanSpace.inner_toLp_toLp, dotProduct_comm (L *ᵥ x),
      dotProduct_comm x, he]
  rw [hx] at hn
  nlinarith [norm_nonneg (WithLp.toLp 2 (L *ᵥ x))]

private theorem lift_schmidt_rank {k d : ℕ} (V : Matrix (Fin d) (Fin k) ℂ)
    (x : Fin k × Fin d → ℂ) :
    schmidtRank ((V ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ x) ≤ k := by
  classical
  let X : Matrix (Fin k) (Fin d) ℂ := Matrix.of fun i j => x (i, j)
  have hcoef :
      (Matrix.of fun i j =>
        ((V ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ x) (i, j)) = V * X := by
    ext i j
    simp [X, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Matrix.one_apply, Matrix.mul_apply, mul_ite, ite_mul, Finset.sum_ite_eq]
  rw [schmidtRank, hcoef]
  exact (rank_mul_le_left V X).trans (by simpa using rank_le_card_width V)

private theorem hermitian_contraction {a : Type} [Fintype a] [DecidableEq a]
    (T : Matrix a a ℂ) (hT : T.IsHermitian)
    (h : ∀ x : a → ℂ, ‖WithLp.toLp 2 x‖ = 1 → ‖star x ⬝ᵥ (T *ᵥ x)‖ ≤ 1) :
    ∀ x : a → ℂ, ‖WithLp.toLp 2 (T *ᵥ x)‖ ≤ ‖WithLp.toLp 2 x‖ := by
  classical
  have hspec (i : a) : ‖(hT.eigenvalues i : ℂ)‖ ≤ 1 := by
    let x := hT.eigenvectorBasis i
    have hx : ‖x‖ = 1 := hT.eigenvectorBasis.orthonormal.norm_eq_one i
    rw [Complex.norm_real, Real.norm_eq_abs, hT.eigenvalues_eq i]
    exact (Complex.abs_re_le_norm _).trans (h x.ofLp (by simpa using hx))
  have hnorm : ‖T‖ ≤ 1 := by
    rw [hT.spectral_theorem, Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
      CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul, l2_opNorm_diagonal]
    let f : a → ℂ := fun i => (hT.eigenvalues i : ℂ)
    change ‖f‖ ≤ 1
    exact (pi_norm_le_iff_of_nonneg (x := f) zero_le_one).mpr hspec
  intro x
  exact (l2_opNorm_mulVec T (WithLp.toLp 2 x)).trans
    (by simpa using mul_le_mul_of_nonneg_right hnorm (norm_nonneg (WithLp.toLp 2 x)))

theorem candidate_compression_separable {k d : ℕ} (hk : 1 ≤ k) (hkd : k ≤ d)
    (H : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hH : H.IsHermitian)
    (hQ : SchmidtQuadraticBound k H)
    (V : Matrix (Fin d) (Fin k) ℂ) (hV : Vᴴ * V = 1) :
    let L := V ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)
    separableCone (Lᴴ * choiCandidate H * L) := by
  let L := V ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)
  have hL : Lᴴ * L = 1 := by
    simp [L, conjTranspose_kronecker, ← mul_kronecker_mul, hV]
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hd' : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  let c : ℝ := (k : ℝ) * (16 / (d : ℝ))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  let T := (-c) • (Lᴴ * H * L)
  have hT : T.IsHermitian := (isHermitian_conjTranspose_mul_mul L hH).smul (by simp [IsSelfAdjoint])
  have hcontract := hermitian_contraction T hT (by
    intro x hx
    have hb := hQ (L *ᵥ x) (lift_unit L hL x hx) (lift_schmidt_rank V x)
    change ‖star x ⬝ᵥ (((-c) • (Lᴴ * H * L)) *ᵥ x)‖ ≤ 1
    rw [Matrix.smul_mulVec, dotProduct_smul, norm_smul, Real.norm_eq_abs,
      abs_neg, abs_of_nonneg hc, ← quadratic_congruence]
    have hs : c * ((d : ℝ) / (32 * (k : ℝ))) = 1 / 2 := by
      dsimp [c]
      field_simp
      ring
    exact (mul_le_mul_of_nonneg_left hb hc).trans (by rw [hs]; norm_num))
  have hsep := separableCone_smul (show 0 ≤ (k : ℝ)⁻¹ by positivity)
    (separableCone_scalar_add_of_opNorm_le_one T hT hcontract)
  have hshift : (k : ℝ)⁻¹ • ((k : ℂ) • (1 : Matrix (Fin k × Fin d) (Fin k × Fin d) ℂ) + T) =
      Lᴴ * choiCandidate H * L := by
    have hscalar : (k : ℝ)⁻¹ * -c = -(16 / (d : ℝ)) := by
      dsimp [c]
      field_simp
    have hid : (k : ℂ) • (1 : Matrix (Fin k × Fin d) (Fin k × Fin d) ℂ) =
        (k : ℝ) • (1 : Matrix (Fin k × Fin d) (Fin k × Fin d) ℂ) := by
      ext i j
      simp [Matrix.smul_apply, Complex.real_smul]
    simp only [hid, T, smul_add, smul_smul, inv_mul_cancel₀ hk'.ne', one_smul, hscalar,
      choiCandidate, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.mul_smul, Matrix.smul_mul, hL]
    rw [neg_smul, ← sub_eq_add_neg]
  change separableCone (Lᴴ * choiCandidate H * L)
  rw [← hshift]
  exact hsep

/-- Definition 3.1 follows from the bounded Schmidt quadratic values. -/
theorem candidate_isKEB {k d : ℕ} (hk : 1 ≤ k) (hkd : k ≤ d)
    (H : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hH : H.IsHermitian)
    (hQ : SchmidtQuadraticBound k H) :
    IsKEB k (fromInputChoi (choiCandidate H)) := by
  apply isKEB_of_choi_congruences
  intro A
  rw [inputChoi_fromInputChoi]
  obtain ⟨V, hV, hA⟩ := exists_right_isometry_factorization hkd A
  have hsep := separable_local_congruence (A * V)
    (candidate_compression_separable hk hkd H hH hQ V hV)
  let I : Matrix (Fin d) (Fin d) ℂ := 1
  let L := V ⊗ₖ I
  have hKr : A ⊗ₖ I = ((A * V) ⊗ₖ I) * Lᴴ := by
    dsimp only [L]
    rw [conjTranspose_kronecker, show Iᴴ = I by simp [I],
      ← mul_kronecker_mul, show I * I = I by simp [I], ← hA]
  change separableCone ((A ⊗ₖ I) * choiCandidate H * (A ⊗ₖ I)ᴴ)
  rw [hKr, conjTranspose_mul, conjTranspose_conjTranspose]
  simpa only [Matrix.mul_assoc] using hsep
