/- GID: D5/S3/VertexAlgebra/OriginalZeroChargeBrstDifferential
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/OriginalZeroChargeBrstDifferential
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original BRST differential on every native exceptional energy-zero basis vector. -/

import D5.S3.VertexAlgebra.OriginalZeroChargeBrstAction

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.OriginalZeroChargeBrstDifferential

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
  LatticeSugawaraConformal LatticeSugawaraVirasoro LatticeBcGhostBrstCharge BcGhostFockSupport
  OriginalZeroChargeEnergySector OriginalZeroChargeEnergyBasis OriginalZeroChargeBrstAction
open scoped BigOperators TensorProduct

noncomputable section

private theorem c_positive_low (subset : Finset ℕ)
    (nonpositive : BcGhostLZeroSpectrum.energy subset ≤ 0)
    (mode : ℤ) (positive : 1 < mode) : c (K := ℂ) mode (Finsupp.single subset 1) = 0 := by
  have notOne : 2 * (mode - 2).toNat ≠ 1 := by omega
  have notThree : 2 * (mode - 2).toNat ≠ 3 := by omega
  have notFive : 2 * (mode - 2).toNat ≠ 5 := by omega
  have alternatives := (ghost_nonpositive_classification subset).mp nonpositive
  rcases alternatives with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [c, show ¬ mode ≤ 1 by omega, annihilate,
      Finsupp.linearCombination_single, annihilateBasis, notOne, notThree, notFive]

private theorem ground_zero (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    sugawaraMode D H 0 (Finsupp.single (0 : Charge D) (1 : Oscillator D)) = 0 := by
  rw [sugawaraMode_ground_zero]
  simp [chargeQuadratic, chargeScalar, bilinear]

theorem Q_ground_low (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : H * gramComplex D = 1) (rightInverse : gramComplex D * H = 1)
    (subset : Finset ℕ) (nonpositive : BcGhostLZeroSpectrum.energy subset ≤ 0) :
    Q D H (Finsupp.single (0 : Charge D) (1 : Oscillator D) ⊗ₜ[ℂ] Finsupp.single subset 1) =
      (2 : ℂ)⁻¹ • (Finsupp.single (0 : Charge D) (1 : Oscillator D) ⊗ₜ[ℂ]
        ghostDoubleSum (Finsupp.single subset 1)) := by
  rw [Q_tmul_split]
  have everyTerm (mode : ℤ) :
      sugawaraMode D H mode (Finsupp.single (0 : Charge D) (1 : Oscillator D)) ⊗ₜ[ℂ]
        c (K := ℂ) (-mode) (Finsupp.single subset 1) = 0 := by
    by_cases positive : 0 < mode
    · rw [sugawaraMode_ground_positive D H 0 mode positive]
      simp
    by_cases zero : mode = 0
    · subst mode
      rw [ground_zero]
      simp
    by_cases minusOne : mode = -1
    · subst mode
      rw [sugawaraMode_ground_minus_one D H leftInverse rightInverse]
      simp [chargePolynomial]
    · rw [c_positive_low subset nonpositive (-mode) (by omega)]
      simp
  simp only [everyTerm, finsum_zero, zero_add]

private theorem current_positive (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : H * gramComplex D = 1) (rightInverse : gramComplex D * H = 1)
    (axis : Fin D.rank) (mode : ℤ) (positive : 0 < mode) :
    sugawaraMode D H mode (Finsupp.single (0 : Charge D) (MvPolynomial.X (axis, 0))) = 0 := by
  have creation : neutralMode D axis (-1)
      (Finsupp.single (0 : Charge D) (1 : Oscillator D)) =
      Finsupp.single 0 (MvPolynomial.X (axis, 0)) := by
    simp [neutralPolynomialMode]
  have neutral : neutralMode D axis (mode - 1)
      (Finsupp.single (0 : Charge D) (1 : Oscillator D)) = 0 := by
    by_cases zeroMode : mode - 1 = 0 <;>
      simp [neutralPolynomialMode, show ¬ mode - 1 < 0 by omega, zeroMode, bilinear,
        LinearMap.smul_apply, LinearMap.sum_apply]
  have commutator := congrArg (fun operator : Module.End ℂ (Carrier D) =>
    operator (Finsupp.single (0 : Charge D) (1 : Oscillator D)))
      (sugawaraMode_current_commutator D H leftInverse rightInverse axis mode (-1))
  rw [show mode + -1 = mode - 1 by omega] at commutator
  simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    creation, sugawaraMode_ground_positive D H 0 mode positive, map_zero,
    sub_zero, Int.cast_neg, Int.cast_one, neg_neg, one_smul, neutral]
    using commutator

private theorem current_zero (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : H * gramComplex D = 1) (rightInverse : gramComplex D * H = 1)
    (axis : Fin D.rank) :
    sugawaraMode D H 0 (Finsupp.single (0 : Charge D) (MvPolynomial.X (axis, 0))) =
      Finsupp.single 0 (MvPolynomial.X (axis, 0)) := by
  have homogeneous := MvPolynomial.isWeightedHomogeneous_monomial
    (fun site : Index D => site.2 + 1) (Finsupp.single (axis, 0) 1) (1 : ℂ)
      (m := 1) (by simp [Finsupp.weight_single])
  have result := sugawaraMode_weighted_homogeneous D H leftInverse rightInverse
    0 (MvPolynomial.monomial (Finsupp.single (axis, 0) 1) 1) 1 homogeneous
  simpa [bilinear, MvPolynomial.X] using result

theorem Q_current_low (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : H * gramComplex D = 1) (rightInverse : gramComplex D * H = 1)
    (axis : Fin D.rank) (includeZero : Bool) :
    Q D H (Finsupp.single (0 : Charge D) (MvPolynomial.X (axis, 0)) ⊗ₜ[ℂ]
      Finsupp.single (if includeZero then {1, 3} else {1}) 1) = 0 := by
  let subset : Finset ℕ := if includeZero then {1, 3} else {1}
  have nonpositive : BcGhostLZeroSpectrum.energy subset ≤ 0 := by
    cases includeZero <;> norm_num [subset, BcGhostLZeroSpectrum.energy,
      BcGhostLZeroSpectrum.siteWeight]
  have cOne : c (K := ℂ) 1 (Finsupp.single subset 1) = 0 := by
    cases includeZero <;> norm_num [subset, c, create, createBasis]
  rw [Q_tmul_split]
  have matterSum :
      (∑ᶠ mode : ℤ,
        sugawaraMode D H mode (Finsupp.single (0 : Charge D) (MvPolynomial.X (axis, 0))) ⊗ₜ[ℂ]
          c (K := ℂ) (-mode) (Finsupp.single subset 1)) =
      Finsupp.single 0 (MvPolynomial.X (axis, 0)) ⊗ₜ[ℂ]
        c (K := ℂ) 0 (Finsupp.single subset 1) := by
    rw [finsum_eq_single _ 0]
    · simp [current_zero D H leftInverse rightInverse]
    · intro mode nonzero
      by_cases positive : 0 < mode
      · rw [current_positive D H leftInverse rightInverse axis mode positive]
        simp
      by_cases minusOne : mode = -1
      · subst mode
        simp [cOne]
      · rw [c_positive_low subset nonpositive (-mode) (by omega)]
        simp
  change (∑ᶠ mode : ℤ,
      sugawaraMode D H mode (Finsupp.single (0 : Charge D) (MvPolynomial.X (axis, 0))) ⊗ₜ[ℂ]
        c (K := ℂ) (-mode) (Finsupp.single subset 1)) +
      (2 : ℂ)⁻¹ • (Finsupp.single 0 (MvPolynomial.X (axis, 0)) ⊗ₜ[ℂ]
        ghostDoubleSum (Finsupp.single subset 1)) = 0
  rw [matterSum, ghostDoubleSum_nonpositive subset nonpositive]
  cases includeZero <;>
    norm_num [subset, c, create, createBasis, sign, Finset.filter_insert,
      Finset.filter_singleton, ← TensorProduct.tmul_smul, TensorProduct.tmul_neg,
      smul_smul, Finsupp.smul_single,
      show ({1, 3} : Finset ℕ) ≠ {1} from by decide,
      show ({3, 1} : Finset ℕ) = {1, 3} from by decide]

theorem Q_sectorBasis (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : H * gramComplex D = 1) (rightInverse : gramComplex D * H = 1)
    (index : BasisIndex D) :
    Q D H (sectorBasis D index : State D) =
      if index = .inl .zeroMode then
        (2 : ℂ) • (sectorBasis D (.inl .pair) : State D) else 0 := by
  classical
  rw [sectorBasis_coe, fullBasis_apply]
  rcases index with ghost | ⟨axis, includeZero⟩
  · cases ghost <;>
      simp only [basisLabel, ghostSites, MvPolynomial.monomial_zero',
        map_one, Sum.inl.injEq]
    all_goals rw [Q_ground_low D H leftInverse rightInverse _ (by decide)]
    all_goals rw [ghostDoubleSum_nonpositive _ (by decide)]
    all_goals norm_num [sectorBasis_coe, fullBasis_apply, basisLabel, ghostSites,
      ← TensorProduct.tmul_smul, smul_smul,
      show GhostIndex.empty ≠ GhostIndex.zeroMode from by decide,
      show GhostIndex.pair ≠ GhostIndex.zeroMode from by decide,
      show GhostIndex.triple ≠ GhostIndex.zeroMode from by decide,
      show ({1, 5} : Finset ℕ) ≠ {3} from by decide,
      show ({1, 5} : Finset ℕ) ≠ {1} from by decide,
      show ({1, 3, 5} : Finset ℕ) ≠ {3} from by decide,
      show ({1, 3, 5} : Finset ℕ) ≠ {1} from by decide]
  · simpa [basisLabel, MvPolynomial.X]
      using Q_current_low D H leftInverse rightInverse axis includeZero

#print axioms Q_sectorBasis

end
end D5.S3.VertexAlgebra.OriginalZeroChargeBrstDifferential
