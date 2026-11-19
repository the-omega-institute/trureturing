/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldVacuumChannel
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldVacuumChannel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual Leech orbifold mode-three pairing is perfect on twisted weight two. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldLowSpectrum
import Batteries.Tactic.OpenPrivate

/-! The original Leech orbifold field realizes a perfect vacuum pairing in twisted weight two. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldVacuumChannel

open ActualLeechHyperbolic (leechData leech_spec)
open LatticeAllStateField (vacuum)
open LatticeInvolution (FixedCarrier fixedSpace fixedVacuum fixedMode)
open LatticePositiveEnergy (grade_zero)
open LatticeHalfFockChargedTensorCoefficients (ActualTensor)
open LatticeHalfFockGradedTrace
open HalfFock.LatticeHalfFockParityField (paritySpace fixedParitySlice)
open HalfFock.NormFourFirstGradeSpectrum
  (parityMinusEnergyTwo actual_grade_one_eq_parity_minus_energy_two)
open ActualChargedAdjoint (actualForm actualForm_nondegenerate)
open ActualOddGradeOrthogonality (actualForm_oddGrade_orthogonal)
open MixedIntertwiner (fixedGrade normalizedCoefficient)
open OriginalFourMChargeCoset (originalI originalI_homogeneous)
open SourceBPZ.OriginalSourcePairing (sourcePairing sourcePairing_vacuum)
open OriginalOrbifoldField (Carrier vacuumState Y_fixed_ncoeff_apply Y_twisted_ncoeff_apply)
open OriginalOrbifoldConformal (L)
open OriginalOrbifoldLowSpectrum (eigenspace_zero_eq_vacuum)
open OriginalOrbifoldVertexAlgebra (originalVertexAlgebra)
open StateFieldResidueReconstruction (integerBinomial epsilon)
open private weight_two_vacuum_pairing from D5.S3.VertexAlgebra.TwistedGround.MixedJacobi
open private sourceGradePairingEquiv sourceGradePairingEquiv_evaluation from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMContraction

local notation "D" => leechData

private theorem hu : IsUnit leechData.G.det := leech_spec.2.1
private theorem hD : Matrix.PosDef (leechData.G.map (Int.cast : ℤ → ℝ)) := leech_spec.2.2.1
private theorem h24 : leechData.rank = 24 := leech_spec.1

local notation "X" => paritySpace D hu (-1)

/-- The weight-two subspace of the actual integral twisted sector. -/
abbrev weightTwo : Submodule ℂ (ActualTensor D hu) := parityMinusEnergyTwo D hu

/-- Inclusion of weight two into the original negative twisted sector. -/
def intoTwisted : weightTwo →ₗ[ℂ] X :=
  Submodule.inclusion inf_le_left

private theorem tensor_energy (u : weightTwo) :
    actualTensorL0 D hu u.val = (2 : ℂ) • u.val :=
  Module.End.mem_eigenspace_iff.mp u.property.2

/-- The actual vacuum regarded as a vector of the fixed grade-zero line. -/
def vacuumInFixedGrade : fixedGrade D 0 :=
  ⟨vacuum D, ⟨by rw [grade_zero D hD]; exact Submodule.mem_span_singleton_self _,
    (fixedVacuum D).property⟩⟩

private def weightTwoCoefficient :
    weightTwo →ₗ[ℂ] weightTwo →ₗ[ℂ] Module.Dual ℂ (fixedGrade D 0) :=
  (((normalizedCoefficient D hu 3).comp intoTwisted).compl₂ intoTwisted).compr₂
    (DirectSum.component ℂ ℤ (fun n => Module.Dual ℂ (fixedGrade D n)) 0)

/-- Evaluate the actual normalized mode-three functional on the original vacuum. -/
def vacuumCoefficient : LinearMap.BilinForm ℂ weightTwo :=
  weightTwoCoefficient.compr₂ (Module.Dual.eval ℂ (fixedGrade D 0) vacuumInFixedGrade)

/-- The scalar in the ordered weight-two pairing is (1). -/
theorem vacuumCoefficient_eq :
    vacuumCoefficient = (actualForm D hu).flip.comp weightTwo.subtype weightTwo.subtype := by
  apply LinearMap.ext
  intro u
  apply LinearMap.ext
  intro v
  exact weight_two_vacuum_pairing D hu h24 (intoTwisted u) (intoTwisted v)
    (tensor_energy u) (tensor_energy v) vacuumInFixedGrade rfl

/-- The original mode-three coefficient, realized by the original inverse
grade pairing in the fixed grade-zero line. -/
def vacuumChannel : weightTwo →ₗ[ℂ] weightTwo →ₗ[ℂ] fixedGrade D 0 :=
  weightTwoCoefficient.compr₂ (sourceGradePairingEquiv D hu hD 0).symm.toLinearMap

/-- The realized bilinear mode is the scalar coefficient times the original vacuum. -/
theorem vacuumChannel_eq :
    vacuumChannel =
      vacuumCoefficient.compr₂
        (LinearMap.toSpanSingleton ℂ (fixedGrade D 0) vacuumInFixedGrade) := by
  apply LinearMap.ext
  intro u
  apply LinearMap.ext
  intro v
  let z := vacuumChannel u v
  have hz : sourcePairing D z.val (vacuum D) = vacuumCoefficient u v :=
    sourceGradePairingEquiv_evaluation D hu hD 0 (weightTwoCoefficient u v) vacuumInFixedGrade
  have hgrade : z.val ∈ Submodule.span ℂ {vacuum D} := grade_zero D hD ▸ z.property.1
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hgrade
  have hscalar : c = vacuumCoefficient u v := by
    rw [← hc, map_smul, LinearMap.smul_apply, sourcePairing_vacuum, smul_eq_mul, mul_one] at hz
    exact hz
  apply Subtype.ext
  change z.val = vacuumCoefficient u v • vacuum D
  rw [← hscalar, hc]

/-- Both radicals vanish. Orthogonality extends each weight-two annihilator
to the whole tensor basis, where the original tensor form detects it. -/
theorem vacuumCoefficient_nondegenerate : vacuumCoefficient.Nondegenerate := by
  let b := actualAmbientBasis D hu
  have gradeOne : actualGrade D hu 1 = weightTwo :=
    actual_grade_one_eq_parity_minus_energy_two D hu h24
  have extend (f : ActualTensor D hu →ₗ[ℂ] ℂ) (h₁ : ∀ w : weightTwo, f w.val = 0)
      (hoff : ∀ i, oddWeight D i.1 ≠ 1 → f (b i) = 0) : ∀ x, f x = 0 := by
    have hzero : f = 0 := by
      apply b.ext
      intro i
      rw [LinearMap.zero_apply]
      by_cases hi : oddWeight D i.1 = 1
      · exact h₁ ⟨b i, gradeOne ▸ actualGradeVector_mem D hu 1 (⟨i.1, hi⟩, i.2)⟩
      · exact hoff i hi
    rw [hzero]
    exact LinearMap.zero_apply
  have energyOne (u : weightTwo) :
      actualTensorL0 D hu u.val = ((leechData.rank : ℂ) / 16 + (1 : ℂ) / 2) • u.val := by
    rw [tensor_energy u, h24]
    norm_num
  rw [vacuumCoefficient_eq]
  constructor
  · intro u h
    apply Subtype.ext
    apply (actualForm_nondegenerate D hu).2
    apply extend ((actualForm D hu).flip u.val) h
    intro i hi
    exact actualForm_oddGrade_orthogonal D hu (oddWeight D i.1) 1 (b i) u.val
      (by simpa only [Int.cast_natCast] using actual_basis_eigenvalue D hu i.1 i.2)
      (by simpa only [Int.cast_one] using energyOne u) (by exact_mod_cast hi)
  · intro v h
    apply Subtype.ext
    apply (actualForm_nondegenerate D hu).1
    apply extend (actualForm D hu v.val) h
    intro i hi
    exact actualForm_oddGrade_orthogonal D hu 1 (oddWeight D i.1) v.val (b i)
      (by simpa only [Int.cast_one] using energyOne v)
      (by simpa only [Int.cast_natCast] using actual_basis_eigenvalue D hu i.1 i.2)
      (by exact_mod_cast hi.symm)

/-- The actual coefficient identifies twisted weight two with its full linear dual. -/
def vacuumCoefficientDual : weightTwo ≃ₗ[ℂ] Module.Dual ℂ weightTwo := by
  letI : FiniteDimensional ℂ weightTwo := by
    change FiniteDimensional ℂ (parityMinusEnergyTwo D hu)
    rw [← actual_grade_one_eq_parity_minus_energy_two D hu h24]
    infer_instance
  exact vacuumCoefficient.toDual vacuumCoefficient_nondegenerate

/-- The twisted-twisted block of the original vertex field has values in the
fixed sector and is given by the original modes at every integer index. -/
theorem stateField_twisted_twisted (n : ℤ) (u v : X) :
    (((originalVertexAlgebra D hu hD h24).stateField (0, u))[[n]]) (0, v) =
      (originalI D hu hD n u v, 0) := by
  dsimp only [originalVertexAlgebra]
  rw [Y_twisted_ncoeff_apply, map_zero]

/-- Mode three of the original vertex field on twisted weight two is the
computed fixed vacuum coefficient, in the full conformal weight-zero eigenspace. -/
theorem stateField_modeThree (u v : weightTwo) :
    let A := originalVertexAlgebra D hu hD h24
    let out := ((A.stateField (0, intoTwisted u))[[3]]) (0, intoTwisted v)
    out = vacuumCoefficient u v • A.vacuum ∧ out ∈ (L D hu hD 0).eigenspace 0 := by
  dsimp only
  rw [stateField_twisted_twisted]
  have hI : originalI D hu hD 3 (intoTwisted u) (intoTwisted v) =
      Submodule.inclusion (show fixedGrade D 0 ≤ fixedSpace D from inf_le_right)
        (vacuumChannel u v) :=
    originalI_homogeneous D hu hD h24 2 2 3 (intoTwisted u) (intoTwisted v)
      (tensor_energy u) (tensor_energy v)
  rw [hI, vacuumChannel_eq, LinearMap.compr₂_apply]
  have hout : ((Submodule.inclusion (show fixedGrade D 0 ≤ fixedSpace D from inf_le_right)
      (LinearMap.toSpanSingleton ℂ (fixedGrade D 0) vacuumInFixedGrade (vacuumCoefficient u v))),
      0) = vacuumCoefficient u v • vacuumState D hu := by
    apply Prod.ext <;> apply Subtype.ext
    · rfl
    · change 0 = vacuumCoefficient u v • (0 : ActualTensor D hu)
      rw [smul_zero]
  rw [hout, eigenspace_zero_eq_vacuum D hu hD h24]
  exact ⟨rfl, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)⟩

/-- The fixed-sector projection of orbifold Borcherds on one fixed and
two twisted states. The fixed-state actions are the original actions on
the respective sectors and the twisted-twisted coefficient is the original
realized mode in every integer degree. -/
theorem projected_mixed_borcherds (a : FixedCarrier D) (u v : X) (p q r : ℤ) :
    let ρ := fun (b : FixedCarrier D) (n : ℤ) => (fixedParitySlice D hu (-1) b)[[n]]
    (∑ᶠ i : ℕ, integerBinomial p i •
      originalI D hu hD (p + q - i) (ρ a (r + i) u) v) =
    ∑ᶠ i : ℕ, ((-1 : ℂ)^i * integerBinomial r i) •
      (fixedMode D a (p + r - i) (originalI D hu hD (q + i) u v) -
        epsilon r • originalI D hu hD (q + r - i) u (ρ a (p + i) v)) := by
  let A := originalVertexAlgebra D hu hD h24
  obtain ⟨hl, hf, hs, hb⟩ := A.borcherds (a, 0) (0, u) (0, v) p q r
  simp only [smul_sub] at hb
  let proj := LinearMap.fst ℂ (FixedCarrier D) X
  have h := congrArg proj hb
  have hright := map_finsum proj (hf.sub hs)
  simp only [Pi.sub_apply] at hright
  rw [map_finsum proj hl, hright] at h
  simpa only [A, originalVertexAlgebra, proj, Y_fixed_ncoeff_apply, Y_twisted_ncoeff_apply,
    map_zero, LinearMap.zero_apply, map_smul, map_sub, smul_sub, LinearMap.fst_apply, Prod.fst_smul,
    Prod.fst_sub] using h

#print axioms vacuumCoefficient_eq
#print axioms vacuumChannel_eq
#print axioms vacuumCoefficient_nondegenerate
#print axioms vacuumCoefficientDual
#print axioms stateField_twisted_twisted
#print axioms stateField_modeThree
#print axioms projected_mixed_borcherds

end D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldVacuumChannel
