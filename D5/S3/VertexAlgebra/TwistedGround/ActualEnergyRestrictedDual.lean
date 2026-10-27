/- GID: D5/S3/VertexAlgebra/TwistedGround/ActualEnergyRestrictedDual
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/ActualEnergyRestrictedDual
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original corrected coefficients have finite energy support in full grade duals. -/

import D5.S3.VertexAlgebra.HalfFock.ActualEnergyCovariance
import D5.S3.VertexAlgebra.TwistedGround.ActualOddGradeOrthogonality
import D5.S3.VertexAlgebra.TwistedGround.CorrectedDualCoefficient

/-!
These are the full algebraic duals of the existing integer source grades.
Finite energy support does not assert finite charge support, finite grade
dimension, or a finite number of charges at one energy. In particular the
original isotropic charge counterexample remains compatible with this file.
The chosen actual form and its ordered slots are retained throughout.

The coefficient is a RAW reversed coefficient, not a normalized intertwiner.
L1, phases, translation, Jacobi and fusion are not supplied by this result.
The declarations below concern the original raw algebraic coefficient, with the stated hypotheses.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators DirectSum

namespace D5.S3.VertexAlgebra.TwistedGround.ActualEnergyRestrictedDual

open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockCorrectedField LatticeHalfFockGradedTrace LatticePositiveEnergy
open ActualChargedAdjoint ActualOddGradeOrthogonality
open HalfFock.ActualEnergyCovariance

/-- Direct consumption of the unchanged signed b076 orthogonality theorem.
The zero-mode law supplies the output eigenvector hypothesis. -/
theorem correctedDualCoefficient_energy_selection (D : LatticeData)
    (hu : IsUnit D.G.det) (h M N e : ℤ) (a : Carrier D) (ha : a ∈ grade D h)
    (x y : ActualTensor D hu)
    (hx : actualTensorL0 D hu x = ((D.rank : ℂ) / 16 + (M : ℂ) / 2) • x)
    (hy : actualTensorL0 D hu y = ((D.rank : ℂ) / 16 + (N : ℂ) / 2) • y)
    (hne : e + 2 * h ≠ N - M) :
    correctedDualCoefficient D hu e x y a = 0 := by
  exact actualForm_oddGrade_orthogonal D hu (M + e + 2 * h) N
    ((correctedField D hu a).coeff e x) y
    (correctedField_signed_output D hu h M e a ha x hx) hy (by omega)

/-- Both input linearities are derived using the two ordered slots of the
original form. This map is consumed by finite expansion and by the lift. -/
private def fullCoefficientBilinear (D : LatticeData) (hu : IsUnit D.G.det) (e : ℤ) :
    ActualTensor D hu →ₗ[ℂ] ActualTensor D hu →ₗ[ℂ] Module.Dual ℂ (Carrier D) where
  toFun x :=
    { toFun := fun y => correctedDualCoefficient D hu e x y
      map_add' := by
        intro y z
        apply LinearMap.ext
        intro a
        exact (actualForm D hu ((correctedField D hu a).coeff e x)).map_add y z
      map_smul' := by
        intro c y
        apply LinearMap.ext
        intro a
        exact (actualForm D hu ((correctedField D hu a).coeff e x)).map_smul c y }
  map_add' x z := by
    apply LinearMap.ext
    intro y
    apply LinearMap.ext
    intro a
    change actualForm D hu ((correctedField D hu a).coeff e (x + z)) y = _
    rw [map_add]
    exact LinearMap.BilinForm.add_left _ _ _
  map_smul' c x := by
    apply LinearMap.ext
    intro y
    apply LinearMap.ext
    intro a
    change actualForm D hu ((correctedField D hu a).coeff e (c • x)) y = _
    rw [map_smul]
    exact LinearMap.BilinForm.smul_left _ _ _

private theorem coefficient_zero_of_basis_pairs (D : LatticeData)
    (hu : IsUnit D.G.det) (e : ℤ) (x y : ActualTensor D hu) (a : Carrier D)
    (hpairs : ∀ i ∈ ((actualAmbientBasis D hu).repr x).support,
      ∀ j ∈ ((actualAmbientBasis D hu).repr y).support,
        correctedDualCoefficient D hu e (actualAmbientBasis D hu i)
          (actualAmbientBasis D hu j) a = 0) :
    correctedDualCoefficient D hu e x y a = 0 := by
  classical
  let b := actualAmbientBasis D hu
  let B := fullCoefficientBilinear D hu e
  change B x y a = 0
  rw [← b.linearCombination_repr x]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum,
    LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
  apply Finset.sum_eq_zero
  intro i hi
  apply smul_eq_zero.mpr
  right
  rw [← b.linearCombination_repr y]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum,
    LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
  apply Finset.sum_eq_zero
  intro j hj
  rw [show B (b i) (b j) a = 0 from hpairs i hi j hj, smul_zero]

/-- The finite signed energies occurring in one actual tensor. -/
def inputOddEnergies (D : LatticeData) (hu : IsUnit D.G.det)
    (x : ActualTensor D hu) : Finset ℤ := by
  classical
  exact ((actualAmbientBasis D hu).repr x).support.image
    (fun i => (oddWeight D i.1 : ℤ))

/-- A finite cover, not a claim that all these grades survive. Integer division
is used only to form the cover; selection first proves exact even divisibility. -/
def coefficientEnergyCover (D : LatticeData) (hu : IsUnit D.G.det) (e : ℤ)
    (x y : ActualTensor D hu) : Finset ℤ := by
  classical
  exact ((inputOddEnergies D hu x).product (inputOddEnergies D hu y)).image
    (fun MN => (MN.2 - MN.1 - e) / 2)

/-- Every source in an excluded full grade is annihilated, including grades
with infinitely many charge coordinates. -/
theorem correctedDualCoefficient_off_energy_cover (D : LatticeData)
    (hu : IsUnit D.G.det) (e : ℤ) (x y : ActualTensor D hu) (h : ℤ)
    (hout : h ∉ coefficientEnergyCover D hu e x y)
    (a : Carrier D) (ha : a ∈ grade D h) :
    correctedDualCoefficient D hu e x y a = 0 := by
  classical
  apply coefficient_zero_of_basis_pairs D hu e x y a
  intro i hi j hj
  apply correctedDualCoefficient_energy_selection D hu h
    (oddWeight D i.1 : ℤ) (oddWeight D j.1 : ℤ) e a ha
    (actualAmbientBasis D hu i) (actualAmbientBasis D hu j)
    (by simpa only [Int.cast_natCast] using actual_basis_eigenvalue D hu i.1 i.2)
    (by simpa only [Int.cast_natCast] using actual_basis_eigenvalue D hu j.1 j.2)
  intro he
  apply hout
  apply Finset.mem_image.mpr
  refine ⟨((oddWeight D i.1 : ℤ), (oddWeight D j.1 : ℤ)), ?_, ?_⟩
  · apply Finset.mem_product.mpr
    exact ⟨Finset.mem_image.mpr ⟨i, hi, rfl⟩,
      Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩
  · change ((oddWeight D j.1 : ℤ) - (oddWeight D i.1 : ℤ) - e) / 2 = h
    have hdiv : (oddWeight D j.1 : ℤ) - (oddWeight D i.1 : ℤ) - e = 2 * h := by
      omega
    rw [hdiv]
    omega

/-- The entire grade restriction, not a selected finite set of coordinates. -/
theorem correctedDualCoefficient_restrict_eq_zero (D : LatticeData)
    (hu : IsUnit D.G.det) (e : ℤ) (x y : ActualTensor D hu) (h : ℤ)
    (hout : h ∉ coefficientEnergyCover D hu e x y) :
    (grade D h).dualRestrict (correctedDualCoefficient D hu e x y) = 0 := by
  apply LinearMap.ext
  intro a
  exact correctedDualCoefficient_off_energy_cover D hu e x y h hout a a.property

/-- Each summand is the FULL algebraic dual; no finite basis is chosen here. -/
abbrev EnergyRestrictedDual (D : LatticeData) :=
  ⨁ h : ℤ, Module.Dual ℂ (grade D h)

/-- Every coordinate is the restriction of the existing full functional.
The preceding mathematical support theorem justifies the finite constructor. -/
def energyCoefficient (D : LatticeData) (hu : IsUnit D.G.det) (e : ℤ)
    (x y : ActualTensor D hu) : EnergyRestrictedDual D := by
  classical
  exact DFinsupp.mk (coefficientEnergyCover D hu e x y)
    (fun h => (grade D h.val).dualRestrict (correctedDualCoefficient D hu e x y))

/-- Exact specification for EVERY integer grade, including excluded grades. -/
theorem energyCoefficient_coordinate (D : LatticeData) (hu : IsUnit D.G.det)
    (e : ℤ) (x y : ActualTensor D hu) (h : ℤ) :
    energyCoefficient D hu e x y h =
      (grade D h).dualRestrict (correctedDualCoefficient D hu e x y) := by
  classical
  by_cases hh : h ∈ coefficientEnergyCover D hu e x y
  · exact DFinsupp.mk_of_mem hh
  · rw [energyCoefficient, DFinsupp.mk_of_notMem hh]
    exact (correctedDualCoefficient_restrict_eq_zero D hu e x y h hh).symm

/-- Evaluation uses the existing internal source-energy decomposition. -/
def energyDualRealization (D : LatticeData) (v : EnergyRestrictedDual D) :
    Module.Dual ℂ (Carrier D) :=
  (DFinsupp.lsum ℂ (fun h => v h)).comp (carrierEnergyDecomposition D).toLinearMap

/-- The lift reconstructs the SAME original functional on all sources. -/
theorem energyCoefficient_realization (D : LatticeData) (hu : IsUnit D.G.det)
    (e : ℤ) (x y : ActualTensor D hu) :
    energyDualRealization D (energyCoefficient D hu e x y) =
      correctedDualCoefficient D hu e x y := by
  classical
  have hs : (DFinsupp.lsum ℂ (fun h => energyCoefficient D hu e x y h)) =
      (correctedDualCoefficient D hu e x y).comp
        (DirectSum.coeLinearMap (grade D)) := by
    apply DFinsupp.lhom_ext
    intro h a
    rw [DFinsupp.lsum_single, energyCoefficient_coordinate]
    change correctedDualCoefficient D hu e x y a =
      correctedDualCoefficient D hu e x y
        (DirectSum.coeLinearMap (grade D) (DFinsupp.single h a))
    rw [DirectSum.single_eq_lof (R := ℂ), DirectSum.coeLinearMap_lof]
  apply LinearMap.ext
  intro a
  change (DFinsupp.lsum ℂ (fun h => energyCoefficient D hu e x y h))
      (carrierEnergyDecomposition D a) = correctedDualCoefficient D hu e x y a
  rw [hs]
  change correctedDualCoefficient D hu e x y
      ((carrierEnergyDecomposition D).symm (carrierEnergyDecomposition D a)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The actual coefficient consumer is linear in both ordered tensor inputs.
Coordinate extensionality discharges the changing finite covers. -/
def energyCoefficientBilinear (D : LatticeData) (hu : IsUnit D.G.det) (e : ℤ) :
    ActualTensor D hu →ₗ[ℂ] ActualTensor D hu →ₗ[ℂ] EnergyRestrictedDual D where
  toFun x :=
    { toFun := energyCoefficient D hu e x
      map_add' := by
        intro y z
        apply DFinsupp.ext
        intro h
        apply LinearMap.ext
        intro a
        simp only [DirectSum.add_apply, energyCoefficient_coordinate,
          Submodule.dualRestrict_apply, LinearMap.add_apply]
        exact LinearMap.congr_fun
          ((fullCoefficientBilinear D hu e x).map_add y z) a
      map_smul' := by
        intro c y
        apply DFinsupp.ext
        intro h
        apply LinearMap.ext
        intro a
        simp only [DirectSum.smul_apply, energyCoefficient_coordinate,
          Submodule.dualRestrict_apply, LinearMap.smul_apply, RingHom.id_apply]
        exact LinearMap.congr_fun
          ((fullCoefficientBilinear D hu e x).map_smul c y) a }
  map_add' x z := by
    apply LinearMap.ext
    intro y
    apply DFinsupp.ext
    intro h
    apply LinearMap.ext
    intro a
    change energyCoefficient D hu e (x + z) y h a =
      energyCoefficient D hu e x y h a + energyCoefficient D hu e z y h a
    simp only [energyCoefficient_coordinate, Submodule.dualRestrict_apply]
    exact LinearMap.congr_fun
      (LinearMap.congr_fun ((fullCoefficientBilinear D hu e).map_add x z) y) a
  map_smul' c x := by
    apply LinearMap.ext
    intro y
    apply DFinsupp.ext
    intro h
    apply LinearMap.ext
    intro a
    change energyCoefficient D hu e (c • x) y h a =
      c • energyCoefficient D hu e x y h a
    simp only [energyCoefficient_coordinate, Submodule.dualRestrict_apply]
    exact LinearMap.congr_fun
      (LinearMap.congr_fun ((fullCoefficientBilinear D hu e).map_smul c x) y) a

/-- A safe finite upper bound for the second input's odd energies; it is zero
when the second input is zero. -/
def maxOddWeight (D : LatticeData) (hu : IsUnit D.G.det)
    (y : ActualTensor D hu) : ℕ := by
  classical
  exact ((actualAmbientBasis D hu).repr y).support.sup (fun j => oddWeight D j.1)

/-- Homogeneous raw reversal has r >= M-N when h >= 0. This statement
needs only the stated source-energy inequality, not positive Gram. -/
theorem reversed_coefficient_zero_of_lt_difference (D : LatticeData)
    (hu : IsUnit D.G.det) (h M N r : ℤ) (hh : 0 ≤ h)
    (a : Carrier D) (ha : a ∈ grade D h) (x y : ActualTensor D hu)
    (hx : actualTensorL0 D hu x = ((D.rank : ℂ) / 16 + (M : ℂ) / 2) • x)
    (hy : actualTensorL0 D hu y = ((D.rank : ℂ) / 16 + (N : ℂ) / 2) • y)
    (hr : r < M - N) : correctedDualCoefficient D hu (-r) x y a = 0 := by
  exact correctedDualCoefficient_energy_selection D hu h M N (-r) a ha x y hx hy
    (by omega)

/-- Positive Gram is used ONLY here, to control every source energy.
The conclusion is zero as the original FULL functional. -/
theorem reversed_full_coefficient_zero (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (x y : ActualTensor D hu) (r : ℤ) (hr : r < -(maxOddWeight D hu y : ℤ)) :
    correctedDualCoefficient D hu (-r) x y = 0 := by
  classical
  apply (carrierBasis D).ext
  intro a
  change correctedDualCoefficient D hu (-r) x y (carrierBasis D a) = 0
  apply coefficient_zero_of_basis_pairs D hu (-r) x y (carrierBasis D a)
  intro i hi j hj
  have ha : carrierBasis D a ∈ grade D (energy D a) := by
    rw [grade_eq_span]
    exact Submodule.subset_span ⟨a, rfl, rfl⟩
  have hh : 0 ≤ energy D a := by
    have hc := chargeEnergy_nonneg D hD a.1
    change 0 ≤ chargeEnergy D a.1 + (oscillatorEnergy a.2 : ℤ)
    omega
  have hN : oddWeight D j.1 ≤ maxOddWeight D hu y := by
    change oddWeight D j.1 ≤
      ((actualAmbientBasis D hu).repr y).support.sup (fun j => oddWeight D j.1)
    exact Finset.le_sup (f := fun k : OddMonomial D ×
      LatticeTwistedGroundRealization.Half (groundRank D hu) => oddWeight D k.1) hj
  apply reversed_coefficient_zero_of_lt_difference D hu (energy D a)
    (oddWeight D i.1 : ℤ) (oddWeight D j.1 : ℤ) r hh (carrierBasis D a) ha
    (actualAmbientBasis D hu i) (actualAmbientBasis D hu j)
    (by simpa only [Int.cast_natCast] using actual_basis_eigenvalue D hu i.1 i.2)
    (by simpa only [Int.cast_natCast] using actual_basis_eigenvalue D hu j.1 j.2)
  omega

/-- Exact coordinates lift the positive-Gram lower bound to the full-grade
restricted dual, without claiming a generic indefinite truncation. -/
theorem reversed_energy_coefficient_zero (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (x y : ActualTensor D hu) (r : ℤ) (hr : r < -(maxOddWeight D hu y : ℤ)) :
    energyCoefficientBilinear D hu (-r) x y = 0 := by
  change energyCoefficient D hu (-r) x y = 0
  apply DFinsupp.ext
  intro h
  rw [energyCoefficient_coordinate, reversed_full_coefficient_zero D hu hD x y r hr]
  exact map_zero _


#print axioms correctedDualCoefficient_energy_selection

#print axioms correctedDualCoefficient_off_energy_cover

#print axioms correctedDualCoefficient_restrict_eq_zero

#print axioms energyCoefficient_coordinate

#print axioms energyCoefficient_realization

#print axioms reversed_coefficient_zero_of_lt_difference

#print axioms reversed_full_coefficient_zero

#print axioms reversed_energy_coefficient_zero

end D5.S3.VertexAlgebra.TwistedGround.ActualEnergyRestrictedDual
