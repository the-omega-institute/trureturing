import D5.S3.VertexAlgebra.TemporaryOriginalQuartet06
import D5.S3.VertexAlgebra.BrstAdaptedFrameTransient

namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open Module LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeSugawaraVirasoro
  LatticeBcGhostBrstCharge BcGhostFockSupport
open scoped BigOperators TensorProduct

noncomputable section

theorem original_nonzero_charge_Q_polarized_coordinate_consumer (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1)
    (rightGramInverse : gramComplex D * H = 1)
    (criticalRank : D.rank = 26) (charge : Charge D) (chargeNonzero : charge ≠ 0) :
    ∃ adapted : OriginalAdaptedFrameData D charge,
      (∀ (polynomial : Oscillator D) (ghost : Fock ℂ),
        (Q D H - delta D (adaptedPartner D charge adapted.nullDirection)
          (chosenP D charge adapted.nullDirection))
            (Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost) =
          ∑ᶠ mode : ℤ,
            if mode = 0 then A D H 0 (Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost) else
              chosenQ D charge adapted.nullDirection • C D (-mode)
                (O D adapted.nullDirection mode (Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost)) +
              C D (-mode)
                (oscillatorSugawaraMode D H mode (Finsupp.single charge polynomial) ⊗ₜ[ℂ] ghost) +
              (2 : ℂ)⁻¹ • N D mode (Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost)) ∧
      (∀ (polynomial : Oscillator D) (ghost : Fock ℂ) (row : Fin D.rank)
          (direction : Fin D.rank → ℂ) (frequency : ℕ),
        Function.Bijective (coordinateSub D adapted.frame) ∧
        O D (adapted.frame row) (-(frequency : ℤ) - 1)
          (Finsupp.single charge (coordinateSub D adapted.frame polynomial) ⊗ₜ[ℂ] ghost) =
          Finsupp.single charge (coordinateSub D adapted.frame
            (MvPolynomial.X (row, frequency) * polynomial)) ⊗ₜ[ℂ] ghost ∧
        O D direction ((frequency : ℤ) + 1)
          (Finsupp.single charge (coordinateSub D adapted.frame polynomial) ⊗ₜ[ℂ] ghost) =
          (frequency + 1 : ℂ) •
            (Finsupp.single charge (coordinateSub D adapted.frame
              (coordinateDerivative D adapted.frame direction frequency polynomial)) ⊗ₜ[ℂ] ghost) ∧
        O D direction 0
          (Finsupp.single charge (coordinateSub D adapted.frame polynomial) ⊗ₜ[ℂ] ghost) =
          gramPair D direction (fun index => (charge index : ℂ)) •
            (Finsupp.single charge (coordinateSub D adapted.frame polynomial) ⊗ₜ[ℂ] ghost)) ∧
      (∀ (powers : Index D →₀ ℕ) (scalar : ℂ) (subset : Finset ℕ) (frequency : ℕ),
        let polynomial := coordinateSub D adapted.frame (MvPolynomial.monomial powers scalar)
        let state := Finsupp.single charge polynomial ⊗ₜ[ℂ] downWord subset down
        Function.Bijective (coordinateSub D adapted.frame) ∧
        chosenH D charge = LatticeSugawaraVirasoro.chargeQuadratic D H charge ∧
        downWord subset down = polarizationSign subset • Finsupp.single (toggleOne subset) 1 ∧
        LatticeBcGhostBrstGhostNumber.J D state =
          ((1 + epsilonCount subset + (thetaCount subset : ℤ) - (etaCount subset : ℤ) : ℤ) : ℂ) • state ∧
        G D 0 state = ((-1 + polarizedLevel subset : ℤ) : ℂ) • state ∧
        normalKAtom D adapted.nullDirection (adaptedPartner D charge adapted.nullDirection)
            ((frequency : ℤ) + 1) state +
          normalKAtom D adapted.nullDirection (adaptedPartner D charge adapted.nullDirection)
            (-((frequency : ℤ) + 1)) state =
          (((powers (adapted.xAxis, frequency) + powers (adapted.yAxis, frequency) +
            (if thetaSite frequency ∈ subset then 1 else 0) +
            (if etaSite frequency ∈ subset then 1 else 0) : ℕ) : ℂ)) • state ∧
        (Q D H - delta D (adaptedPartner D charge adapted.nullDirection)
          (chosenP D charge adapted.nullDirection)) state =
          (∑ᶠ mode : ℤ, if mode = 0 then A D H 0 state else
            chosenQ D charge adapted.nullDirection • C D (-mode) (O D adapted.nullDirection mode state) +
            C D (-mode)
              (oscillatorSugawaraMode D H mode (Finsupp.single charge polynomial) ⊗ₜ[ℂ]
                downWord subset down) + (2 : ℂ)⁻¹ • N D mode state) ∧
        delta D (adaptedPartner D charge adapted.nullDirection) (chosenP D charge adapted.nullDirection) *
          delta D (adaptedPartner D charge adapted.nullDirection) (chosenP D charge adapted.nullDirection) = 0 ∧
        R D adapted.nullDirection (chosenP D charge adapted.nullDirection) *
          R D adapted.nullDirection (chosenP D charge adapted.nullDirection) = 0 ∧
        delta D (adaptedPartner D charge adapted.nullDirection) (chosenP D charge adapted.nullDirection) *
            R D adapted.nullDirection (chosenP D charge adapted.nullDirection) +
          R D adapted.nullDirection (chosenP D charge adapted.nullDirection) *
            delta D (adaptedPartner D charge adapted.nullDirection) (chosenP D charge adapted.nullDirection) =
          K D adapted.nullDirection (adaptedPartner D charge adapted.nullDirection)
            (adaptedPartner_relations D charge adapted.nullDirection
              adapted.nullSelf adapted.coefficientNonzero).1 ∧
        (∀ originalState : State D,
          K D adapted.nullDirection (adaptedPartner D charge adapted.nullDirection)
            (adaptedPartner_relations D charge adapted.nullDirection
              adapted.nullSelf adapted.coefficientNonzero).1 originalState =
            ∑ᶠ mode : ℤ,
              normalKAtom D adapted.nullDirection (adaptedPartner D charge adapted.nullDirection)
                mode originalState) ∧
        LatticeBcGhostBrstGhostNumber.J D *
            (Q D H - delta D (adaptedPartner D charge adapted.nullDirection)
              (chosenP D charge adapted.nullDirection)) -
          (Q D H - delta D (adaptedPartner D charge adapted.nullDirection)
            (chosenP D charge adapted.nullDirection)) * LatticeBcGhostBrstGhostNumber.J D =
            Q D H - delta D (adaptedPartner D charge adapted.nullDirection)
              (chosenP D charge adapted.nullDirection)) := by
  obtain ⟨adapted⟩ := original_nonzero_charge_adapted_frame_exists D H
    leftGramInverse rightGramInverse criticalRank charge chargeNonzero
  refine ⟨adapted, ?_, ?_, ?_⟩
  · intro polynomial ghost
    exact original_Q_corrected_finsum D H leftGramInverse rightGramInverse charge
      adapted.nullDirection adapted.nullSelf adapted.coefficientNonzero polynomial ghost
  · intro polynomial ghost row direction frequency
    exact original_coordinate_current_bridge D adapted.frame adapted.inverse
      adapted.leftFrameInverse adapted.rightFrameInverse charge polynomial ghost row direction frequency
  · intro powers scalar subset frequency
    exact original_Q_polarized_coordinate_consumer D H leftGramInverse rightGramInverse charge
      adapted.nullDirection adapted.nullSelf adapted.coefficientNonzero adapted.frame adapted.inverse
      adapted.leftFrameInverse adapted.rightFrameInverse adapted.xAxis adapted.yAxis
      adapted.xRow adapted.yRow adapted.xDual adapted.yDual powers scalar subset frequency

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
