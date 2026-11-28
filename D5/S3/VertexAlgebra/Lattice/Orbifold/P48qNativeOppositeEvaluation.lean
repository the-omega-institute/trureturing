/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeOppositeEvaluation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeOppositeEvaluation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual fixed-source states representing the BPZ-inverted twisted coefficients. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeOppositeGrade
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedSourceBPZ

/-! The nondegenerate BPZ pairing represents the coordinate-inverted right
insertion in each actual fixed grade. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeOppositeEvaluation

open scoped BigOperators
open HalfFockSpectralFiberSource (actualInverse actualInverse_left actualInverse_right)
open LatticePositiveEnergy (grade grade_finiteDimensional grade_zero actualL0_eigen_iff_grade)
open LatticeSugawaraCurrents (sugawaraMode)
open P48qFixedSourceBPZ (fixedGrade fixedGradeForm fixedGradeForm_nondegenerate)
open P48qGramPositivity (nebeGram_posDef)
open P48qNativeConformalSector (fixedStates sector fixedField fixedOmega fixedVacuum)
open P48qNativeFixedRightInsertion (rightInsertion sectorTranslation)
open P48qNativeOppositeGrade (invertedCoeff_grade_of_ne_zero)
open P48qNativeOppositeVacuum
  (gradeProjection invertedCoeff invertedCoeff_translation ground groundFunctional
    invertedCoeff_ground_vacuum)
open P48qTwistedChargeAction (lattice)
open P48qTwistedStateEnergy (totalLZero)
open SourceBPZ.OriginalSourcePairing (sourcePairing sourcePairing_vacuum)
open SourceBPZ.SourcePairingLaws (sourcePairing_grade)
open StateField.BorcherdsPermutations (dividedTranslation)
open private gram_det_unit from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qConformalVectorDecomposition
open private rightMode from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeFixedRightJacobi
open private inversionTerm from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeOppositeVacuum

noncomputable section

private def invertedCoeffLinear (s : Fin 3) (h : ℤ) (w : ℂ) (u : sector s)
    (f : Module.Dual ℂ (totalLZero.eigenspace w)) (k : ℤ) : Module.Dual ℂ fixedStates :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * ((h : ℂ) / 9)) •
    ∑ j ∈ Finset.range (((h - 16) / 9).toNat + 1),
      f.comp ((gradeProjection w).comp ((sector s).subtype.comp
        (rightMode s (k - (j : ℤ) - 1)
          (dividedTranslation (HVertexOperator.coeff (fixedField s fixedOmega) (-3)) j u))))

private theorem invertedCoeffLinear_apply (s : Fin 3) (h : ℤ) (w : ℂ) (u : sector s)
    (f : Module.Dual ℂ (totalLZero.eigenspace w)) (a : fixedStates) (k : ℤ) :
    invertedCoeffLinear s h w u f k a = invertedCoeff s h w u f a k := by
  simp only [invertedCoeffLinear, invertedCoeff, LinearMap.smul_apply, smul_eq_mul,
    LinearMap.sum_apply, LinearMap.comp_apply, Submodule.subtype_apply]
  apply congrArg (Complex.exp ((Real.pi : ℂ) * Complex.I * ((h : ℂ) / 9)) * ·)
  apply Finset.sum_congr rfl
  intro j _
  change f (gradeProjection w ((rightInsertion s _ a).coeff (-(k - (j : ℤ) - 1) - 1)).val) =
    inversionTerm s w u f a k j
  rw [show -(k - (j : ℤ) - 1) - 1 = (j : ℤ) - k by omega]
  rfl

private theorem fixedGrade_finiteDimensional (d : ℤ) : FiniteDimensional ℂ (fixedGrade d) := by
  let := grade_finiteDimensional lattice nebeGram_posDef d
  have h : fixedGrade d ≤ grade lattice d := inf_le_right
  exact FiniteDimensional.of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)

attribute [local instance] fixedGrade_finiteDimensional

private def fixedGradeInclusion (d : ℤ) : fixedGrade d →ₗ[ℂ] fixedStates :=
  Submodule.inclusion inf_le_left

/-- The fixed grade component of the native opposite evaluation at index `k`. -/
def evaluation (s : Fin 3) (h : ℤ) (w : ℂ) (u : sector s)
    (f : Module.Dual ℂ (totalLZero.eigenspace w)) (k d : ℤ) : fixedGrade d :=
  ((fixedGradeForm d).toDual (fixedGradeForm_nondegenerate d)).symm
    ((invertedCoeffLinear s h w u f k).comp (fixedGradeInclusion d))

/-- Pairing the evaluation state with a homogeneous fixed input recovers the
coefficient of the actual coordinate-inverted right insertion. -/
theorem evaluation_pairing (s : Fin 3) (h : ℤ) (w : ℂ) (u : sector s)
    (f : Module.Dual ℂ (totalLZero.eigenspace w)) (k d : ℤ) (a : fixedGrade d) :
    fixedGradeForm d (evaluation s h w u f k d) a =
      invertedCoeff s h w u f ⟨a.val, a.property.1⟩ k := by
  unfold evaluation
  rw [LinearMap.BilinForm.apply_toDual_symm_apply]
  exact invertedCoeffLinear_apply s h w u f _ k

/-- In the ambient BPZ pairing, a fixed test state reads the represented
coefficient on the same grade and gives zero on all other grades. -/
theorem evaluation_sourcePairing (s : Fin 3) (h : ℤ) (w : ℂ) (u : sector s)
    (f : Module.Dual ℂ (totalLZero.eigenspace w)) (k d e : ℤ) (a : fixedGrade e) :
    sourcePairing lattice (evaluation s h w u f k d).val a.val =
      if d = e then invertedCoeff s h w u f ⟨a.val, a.property.1⟩ k else 0 := by
  by_cases hde : d = e
  · subst e
    rw [if_pos rfl]
    exact evaluation_pairing s h w u f k d a
  · rw [if_neg hde]
    exact sourcePairing_grade lattice d e hde _ _ (evaluation s h w u f k d).property.2 a.property.2

/-- A nonmatching conformal grade has zero opposite evaluation. -/
theorem evaluation_eq_zero_of_grade_ne (s : Fin 3) (h : ℤ) (w : ℂ) (u : sector s)
    (hu : totalLZero u.val = ((h : ℂ) / 9) • u.val)
    (f : Module.Dual ℂ (totalLZero.eigenspace w)) (k d : ℤ)
    (hne : w ≠ (h : ℂ) / 9 + (d : ℂ) - (k : ℂ)) :
    evaluation s h w u f k d = 0 := by
  apply (fixedGradeForm_nondegenerate d).1
  intro a
  rw [evaluation_pairing]
  by_contra hcoeff
  have ha : sugawaraMode lattice (actualInverse lattice) 0 a.val = (d : ℂ) • a.val :=
    (actualL0_eigen_iff_grade lattice (actualInverse lattice)
      (actualInverse_left lattice gram_det_unit) (actualInverse_right lattice gram_det_unit)
      d a.val).mpr a.property.2
  exact hne (invertedCoeff_grade_of_ne_zero s h w (d : ℂ) u hu f
    (fixedGradeInclusion d a) ha k hcoeff).1

/-- Translating the twisted input differentiates the opposite evaluation
with the physical exponents of the coordinate inversion. -/
theorem evaluation_translation (s : Fin 3) (h : ℤ) (w : ℂ) (u : sector s)
    (hu : totalLZero u.val = ((h : ℂ) / 9) • u.val)
    (f : Module.Dual ℂ (totalLZero.eigenspace w)) (k d : ℤ) :
    evaluation s (h + 9) w (sectorTranslation s u) f k d =
      (((k - 1 : ℤ) : ℂ) - 2 * (h : ℂ) / 9) • evaluation s h w u f (k - 1) d := by
  apply sub_eq_zero.mp
  apply (fixedGradeForm_nondegenerate d).1
  intro a
  simp only [map_sub, LinearMap.sub_apply, LinearMap.BilinForm.smul_left,
    evaluation_pairing, invertedCoeff_translation s h w u hu, sub_self]

private def fixedVacuumGrade : fixedGrade 0 :=
  ⟨fixedVacuum.val, fixedVacuum.property, by
    change LatticeAllStateField.vacuum lattice ∈ grade lattice 0
    rw [grade_zero lattice nebeGram_posDef]
    exact Submodule.mem_span_singleton_self _⟩

/-- The degree-zero ground evaluation is the actual fixed vacuum with its
coordinate-inversion normalization. -/
theorem evaluation_ground_vacuum :
    (evaluation 0 16 (16 / 9) ground groundFunctional 0 0).val =
      Complex.exp (16 * (Real.pi : ℂ) * Complex.I / 9) • fixedVacuum.val := by
  let v := evaluation 0 16 (16 / 9) ground groundFunctional 0 0
  have hv : v.val ∈ grade lattice 0 := v.property.2
  rw [grade_zero lattice nebeGram_posDef, Submodule.mem_span_singleton] at hv
  obtain ⟨c, hc⟩ := hv
  change c • fixedVacuum.val = v.val at hc
  have hp := evaluation_pairing 0 16 (16 / 9) ground groundFunctional 0 0 fixedVacuumGrade
  change sourcePairing lattice v.val fixedVacuum.val =
    invertedCoeff 0 16 (16 / 9) ground groundFunctional fixedVacuum 0 at hp
  rw [← hc, LinearMap.BilinForm.smul_left] at hp
  have hunit : sourcePairing lattice fixedVacuum.val fixedVacuum.val = 1 :=
    sourcePairing_vacuum lattice
  rw [hunit, mul_one, invertedCoeff_ground_vacuum.1 0, if_pos rfl] at hp
  exact hc.symm.trans (congrArg (· • fixedVacuum.val) hp)

/-- The native ground evaluation has a nonzero fixed source coefficient. -/
theorem evaluation_ground_ne_zero :
    evaluation 0 16 (16 / 9) ground groundFunctional 0 0 ≠ 0 := by
  intro hz
  have hp := evaluation_pairing 0 16 (16 / 9) ground groundFunctional 0 0 fixedVacuumGrade
  rw [hz, map_zero, LinearMap.zero_apply] at hp
  exact invertedCoeff_ground_vacuum.2.2 hp.symm

#print axioms evaluation_pairing
#print axioms evaluation_sourcePairing
#print axioms evaluation_eq_zero_of_grade_ne
#print axioms evaluation_translation
#print axioms evaluation_ground_vacuum
#print axioms evaluation_ground_ne_zero

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeOppositeEvaluation
