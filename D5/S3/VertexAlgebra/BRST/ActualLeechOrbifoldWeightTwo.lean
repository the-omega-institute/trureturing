/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldWeightTwo
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldWeightTwo
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The conformal weight-two space of the assembled Leech orbifold. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldMatter
import D5.S3.VertexAlgebra.Lattice.LeechLowSpectrum
import D5.S3.VertexAlgebra.Lattice.InvolutionRootlessLowGrades
import D5.S3.VertexAlgebra.HalfFock.NormFourFirstGradeSpectrum
import Batteries.Tactic.OpenPrivate

/-! The assembled weight-two eigenspace splits into the fixed and twisted sectors. -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldWeightTwo

open ActualLeechHyperbolic (leechData leechCoordinates leech_spec)
open ActualLeechOrbifoldMatter (Orbifold leechUnit leechPosDef mode mode_apply)
open LatticeGeneratingFieldLocality (Carrier Charge bilinear)
open LatticeInvolution (fixedSpace)
open LatticeSugawaraCurrents (gramComplex sugawaraMode)
open HalfFockSpectralFiberSource (actualInverse actualInverse_left)
open LatticeHalfFockChargedTensorCoefficients (ActualTensor)
open LatticeHalfFockGradedTrace
  (actualTensorL0 actualGrade ActualGradeIndex actualGradeBasis
    actual_rank24_grade_one_finrank_98304)
open Lattice.RootlessLowGrades (NormFour normFour_finite)
open Lattice.InvolutionRootlessLowGrades
  (NormFourOrbit FixedTwoIndex actualFixedEnergyTwoBasis actual_theta_fixed_rootless_low_spectrum)
open HalfFock.NormFourFirstGradeSpectrum
  (parityMinusEnergyTwo actual_grade_one_eq_parity_minus_energy_two)
open private no_roots from D5.S3.VertexAlgebra.Lattice.LeechLowSpectrum

private theorem leech_rootless : ∀ a : Charge leechData, bilinear leechData a a ≠ 2 :=
  no_roots leechCoordinates leech_spec.2.2.2

/-- The shell count on the charge data used by the assembled field. -/
theorem leech_norm_four_card : Nat.card (NormFour leechData) = 196560 :=
  (Nat.card_congr (Lattice.LeechLowSpectrum.normFourEquiv leechData leechCoordinates
    leech_spec.2.2.2)).trans
    D5.S3.Arith.Lattices.Golay.LeechMinimalCount.shortest_vectors_card

abbrev FixedWeightTwo : Submodule ℂ (Carrier leechData) :=
  fixedSpace leechData ⊓ (sugawaraMode leechData (gramComplex leechData)⁻¹ 0).eigenspace (2 : ℂ)

abbrev TwistedWeightTwo : Submodule ℂ (ActualTensor leechData leechUnit) :=
  parityMinusEnergyTwo leechData leechUnit

abbrev WeightTwo : Submodule ℂ Orbifold :=
  (mode 0).eigenspace (2 : ℂ)

private theorem actualInverse_eq_canonical :
    actualInverse leechData = (gramComplex leechData)⁻¹ :=
  (Matrix.inv_eq_left_inv (actualInverse_left leechData leechUnit)).symm

/-- The assembled zero mode has weight two exactly when both native
components obey their respective weight-two equations. -/
theorem mem_weight_two_iff (x : Orbifold) :
    x ∈ WeightTwo ↔ x.1.val ∈ FixedWeightTwo ∧ x.2.val ∈ TwistedWeightTwo := by
  have h := mode_apply 0 x
  have hf : (mode 0 x).1.val =
      sugawaraMode leechData (gramComplex leechData)⁻¹ 0 x.1.val := by
    rw [← actualInverse_eq_canonical]
    exact congrArg Prod.fst h
  have ht : (mode 0 x).2.val = actualTensorL0 leechData leechUnit x.2.val :=
    congrArg Prod.snd h
  constructor
  · intro hx
    have he : mode 0 x = (2 : ℂ) • x := Module.End.mem_eigenspace_iff.mp hx
    refine ⟨⟨x.1.property, Module.End.mem_eigenspace_iff.mpr ?_⟩,
      ⟨x.2.property, Module.End.mem_eigenspace_iff.mpr ?_⟩⟩
    · exact hf.symm.trans (congrArg (fun y : Orbifold => y.1.val) he)
    · exact ht.symm.trans (congrArg (fun y : Orbifold => y.2.val) he)
  · rintro ⟨hfixed, htwisted⟩
    apply Module.End.mem_eigenspace_iff.mpr
    apply Prod.ext
    · apply Subtype.ext
      exact hf.trans (Module.End.mem_eigenspace_iff.mp hfixed.2)
    · apply Subtype.ext
      exact ht.trans (Module.End.mem_eigenspace_iff.mp htwisted.2)

/-- Splitting and assembling the actual weight-two vectors are inverse
linear maps on the two literal sectors. -/
def weightTwoEquiv : WeightTwo ≃ₗ[ℂ] (FixedWeightTwo × TwistedWeightTwo) where
  toFun x :=
    let hx := (mem_weight_two_iff x.val).mp x.property
    (⟨x.val.1.val, hx.1⟩, ⟨x.val.2.val, hx.2⟩)
  invFun x :=
    let y : Orbifold := (⟨x.1.val, x.1.property.1⟩, ⟨x.2.val, x.2.property.1⟩)
    ⟨y, (mem_weight_two_iff y).mpr ⟨x.1.property, x.2.property⟩⟩
  left_inv _ := Subtype.ext (Prod.ext (Subtype.ext rfl) (Subtype.ext rfl))
  right_inv _ := Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)
  map_add' _ _ := Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)
  map_smul' _ _ := Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)

/-- Neutral oscillator pairs and opposite-charge orbits in the fixed sector. -/
def fixedWeightTwoBasis : Module.Basis (FixedTwoIndex leechData) ℂ FixedWeightTwo :=
  actualFixedEnergyTwoBasis leechData leechPosDef leech_rootless

private theorem twisted_grade_one_eq :
    actualGrade leechData leechUnit 1 = TwistedWeightTwo :=
  actual_grade_one_eq_parity_minus_energy_two leechData leechUnit leech_spec.1

/-- The native grade-one tensor basis in the negative twisted sector. -/
def twistedWeightTwoBasis :
    Module.Basis (ActualGradeIndex leechData leechUnit 1) ℂ TwistedWeightTwo :=
  (actualGradeBasis leechData leechUnit 1).map (LinearEquiv.ofEq _ _ twisted_grade_one_eq)

instance fixedWeightTwo_finite : FiniteDimensional ℂ FixedWeightTwo := by
  let : Finite (NormFour leechData) := normFour_finite leechData leechPosDef
  let : Finite (NormFourOrbit leechData) := Quotient.finite _
  exact Module.Finite.of_basis fixedWeightTwoBasis

instance twistedWeightTwo_finite : FiniteDimensional ℂ TwistedWeightTwo :=
  Module.Finite.of_basis twistedWeightTwoBasis

instance weightTwo_finite : FiniteDimensional ℂ WeightTwo :=
  Module.Finite.of_surjective weightTwoEquiv.symm.toLinearMap weightTwoEquiv.symm.surjective

theorem fixed_weight_two_finrank : Module.finrank ℂ FixedWeightTwo = 98580 := by
  calc
    Module.finrank ℂ FixedWeightTwo =
        Nat.choose (leechData.rank + 1) 2 + Nat.card (NormFour leechData) / 2 :=
      (actual_theta_fixed_rootless_low_spectrum leechData leechPosDef leech_rootless).2.2
    _ = 98580 := by
      rw [leech_norm_four_card, leech_spec.1]
      norm_num [Nat.choose]

theorem twisted_weight_two_finrank : Module.finrank ℂ TwistedWeightTwo = 98304 := by
  rw [← twisted_grade_one_eq]
  exact (actual_rank24_grade_one_finrank_98304 leechData leechUnit leech_spec.1).2.1

/-- The conformal weight-two multiplicity of the literal assembled field. -/
theorem weight_two_finrank : Module.finrank ℂ ((mode 0).eigenspace (2 : ℂ)) = 196884 := by
  change Module.finrank ℂ WeightTwo = _
  rw [weightTwoEquiv.finrank_eq, Module.finrank_prod,
    fixed_weight_two_finrank, twisted_weight_two_finrank]

end D5.S3.VertexAlgebra.ActualLeechOrbifoldWeightTwo
