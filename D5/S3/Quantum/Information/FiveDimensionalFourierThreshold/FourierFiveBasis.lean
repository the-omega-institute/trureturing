/- GID: D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFiveBasis
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFiveBasis
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The normalized Fourier transform gives the coordinate law of an orthonormal basis. -/

import D5.S3.Quantum.Information.FiveDimensionalFourierThreshold.TwoBasisMasks
import D5.S3.Quantum.ShorCountingMarginal

/-! Coordinate and Fourier Born laws for the five-dimensional application. -/

open scoped BigOperators InnerProductSpace
open InnerProductSpace QuantumPhaseEstimationGeneral

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Information.FiveDimensionalFourierThreshold

/-- The basis coordinates are the existing normalized inverse QFT. -/
def fourierRepr (n : ℕ) (hn : 0 < n) :
    EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n) where
  toLinearEquiv :=
    { toFun := fun z => WithLp.toLp 2 (inverseQFT n (WithLp.ofLp z))
      invFun := fun z => WithLp.toLp 2 (QFT n (WithLp.ofLp z))
      left_inv := fun z => congrArg (WithLp.toLp 2) (qft_inverse_qft hn (WithLp.ofLp z))
      right_inv := fun z => congrArg (WithLp.toLp 2) (inverse_qft_qft hn (WithLp.ofLp z))
      map_add' := by
        intro x y
        apply WithLp.ofLp_injective 2
        funext j
        simp [inverseQFT, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro a x
        apply WithLp.ofLp_injective 2
        funext j
        simp only [RingHom.id_apply, WithLp.ofLp_smul, Pi.smul_apply,
          inverseQFT, smul_eq_mul]
        simp_rw [mul_left_comm _ a]
        rw [← Finset.mul_sum, mul_left_comm] }
  norm_map' := by
    intro z
    change ‖WithLp.toLp 2 (inverseQFT n (WithLp.ofLp z))‖ = ‖z‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simpa only [normSquared, Complex.normSq_eq_norm_sq, PiLp.toLp_apply] using
      inverse_qft_norm hn (WithLp.ofLp z)

def fourierBasis (n : ℕ) (hn : 0 < n) :
    OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)) :=
  OrthonormalBasis.ofRepr (fourierRepr n hn)

/-- The entry formula used for Fourier submatrix compressions. -/
theorem fourierBasis_entry (n : ℕ) (hn : 0 < n) (i j : Fin n) :
    fourierBasis n hn j i = scale n * kernel n i j := by
  change ((OrthonormalBasis.ofRepr (fourierRepr n hn) : Fin n → _) j) i = _
  rw [OrthonormalBasis.coe_ofRepr]
  change QFT n (Pi.single j 1) i = _
  unfold QFT
  have hsum : (∑ k : Fin n, kernel n i k * (Pi.single j 1 : Fin n → ℂ) k) = kernel n i j := by
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
    · simp
    · intro k _ hk
      simp [hk]
  rw [hsum]

abbrev CoordinateFive := EuclideanSpace ℂ (Fin 5)
abbrev coordinateBasisFive := EuclideanSpace.basisFun (Fin 5) ℂ
abbrev fourierBasisFive := fourierBasis 5 (by decide)

theorem five_cross_entry (i j : Fin 5) :
    ⟪coordinateBasisFive i, fourierBasisFive j⟫_ℂ = scale 5 * kernel 5 i j := by
  rw [← OrthonormalBasis.repr_apply_apply, EuclideanSpace.basisFun_repr, fourierBasis_entry]

def fiveScore (x y : CoordinateFive) : ℝ :=
  score (basisLaw coordinateBasisFive fourierBasisFive x)
    (basisLaw coordinateBasisFive fourierBasisFive y)

/-- The sum-indexed score is the sum of the two original table scores. -/
theorem fiveScore_eq_sum (x y : CoordinateFive) :
    fiveScore x y =
      score (fun i => ‖x i‖ ^ 2) (fun i => ‖y i‖ ^ 2) +
      score (fun i => ‖inverseQFT 5 (WithLp.ofLp x) i‖ ^ 2)
        (fun i => ‖inverseQFT 5 (WithLp.ofLp y) i‖ ^ 2) := by
  unfold fiveScore score
  rw [Fintype.sum_sum_type]
  simp only [basisLaw, Sum.elim_inl, Sum.elim_inr, ← OrthonormalBasis.repr_apply_apply,
    EuclideanSpace.basisFun_repr]
  rfl

end D5.S3.Quantum.Information.FiveDimensionalFourierThreshold
