/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeOppositeEvaluation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeOppositeEvaluation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual fixed-source states representing the BPZ-inverted twisted coefficients. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeOppositeGrade
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeFixedInvertedIterate
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedSourceBPZ
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeRestrictedDualPairing
import D5.S3.VertexAlgebra.SourceBPZ.AllStateTranspose

/-! The nondegenerate BPZ pairing represents the coordinate-inverted right
insertion in each actual fixed grade. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeOppositeEvaluation

open scoped BigOperators DirectSum VertexOperator
open HalfFockSpectralFiberSource (actualInverse actualInverse_left actualInverse_right)
open LatticeActualConformalWard (omega_product)
open LatticeHalfFockFiniteCorrection (sourceWeight)
open LatticePositiveEnergy (grade grade_finiteDimensional grade_zero actualL0_eigen_iff_grade
  gradeProjection_mem stateEnergies sum_gradeProjections)
open LatticeSugawaraCurrents (sugawaraMode)
open P48qConformalVectorDecomposition (actualInverse_eq_complexInverse)
open P48qFixedSourceBPZ (fixedGrade fixedGradeForm fixedGradeForm_nondegenerate)
open P48qGramPositivity (nebeGram_posDef)
open P48qNativeConformalSector
  (fixedStates sector fixedField fixedField_coeff_val fixedOmega fixedProduct fixedVacuum)
open P48qNativeDualCoefficients (bpzTerm)
open P48qNativeDualLinearField (dualField dualField_homogeneous)
open P48qNativeFixedInvertedIterate
  (fixedSourceLOne sectorLOne sectorLOne_divided_inverted_iterate)
open P48qNativeFixedRightInsertion (rightInsertion sectorTranslation)
open P48qNativeOppositeGrade
  (fixedMode_weight fixedMode_eq_zero_of_below_minimum invertedCoeff_grade_of_ne_zero)
open P48qNativeOppositeVacuum
  (gradeProjection invertedCoeff invertedCoeff_translation ground groundFunctional
    invertedCoeff_ground_vacuum)
open P48qNativeRestrictedDualField (ActualGrade GradeDual coeff_lof
  gradedPairing gradedPairing_lof_grade gradedPairing_lof_grade_of_ne
  gradedPairing_dualField_coeff oppositeField_coeff shiftedWeight stateDecompose)
open P48qThirdTwistedField (State)
open P48qTwistedChargeAction (lattice)
open P48qTwistedStateEnergy (totalLZero)
open SourceBPZ.AllStateTranspose (sourcePairing_allState)
open SourceBPZ.OriginalSourcePairing (sourcePairing sourcePairing_vacuum)
open SourceBPZ.SourcePairingLaws (sourcePairing_grade)
open StateField.BorcherdsPermutations (dividedTranslation)
open StateFieldResidueReconstruction (integerBinomial)
open private gram_det_unit from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qConformalVectorDecomposition
open private fixedProjection fixedProjection_eq_self fixedProjection_fixed lift_fixed
  mem_fixedStates_iff sourceLZero_fixedProjection from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeConformalSector
open private rightMode sourceMode from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeFixedRightJacobi
open private gradeProjection_eq_zero gradeProjection_self inversionTerm
  inversionTerm_eq_zero_of_le rightInsertionEval rightInsertionEval_apply from
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

local notation "C" => HVertexOperator.coeff
local notation "L₀" => sugawaraMode lattice (actualInverse lattice) 0
local notation "L₁" => sugawaraMode lattice (actualInverse lattice) 1

/-- The paired opposite coefficient of a normalized fixed-mode iterate is the
finite divided-power expansion of the actual right-insertion coefficient. -/
theorem invertedCoeff_iterate_coeff (s : Fin 3) (a : fixedStates) (u : sector s)
    (e h : ℤ) (ha : L₀ a.val = (e : ℂ) • a.val)
    (m : ℤ) (w : ℂ) (f : Module.Dual ℂ (totalLZero.eigenspace w))
    (b : fixedStates) (k : ℤ) :
    let H : ℤ := h + 9 * (e - m - 1)
    invertedCoeff s H w (((fixedField s a)[[m]]) u) f b k =
      Complex.exp ((Real.pi : ℂ) * Complex.I * ((H : ℂ) / 9)) *
        ∑ r ∈ Finset.range (((H - 16) / 9).toNat + 1),
          ∑ i ∈ Finset.range (r + 1), ∑ j ∈ Finset.range (r - i + 1),
            integerBinomial (2 * e - m - (i : ℤ) - 2) (r - i - j) *
              f (gradeProjection w ((rightInsertion s
                (((fixedField s (dividedTranslation fixedSourceLOne i a))
                  [[m + (r : ℤ) - (i : ℤ) - (j : ℤ)]])
                    (dividedTranslation (sectorLOne s) j u)) b).coeff ((r : ℤ) - k)).val) := by
  intro H
  let v := ((fixedField s a)[[m]]) u
  let readout (r : ℕ) := rightInsertionEval s w f b ((r : ℤ) - k)
  unfold invertedCoeff
  apply congrArg (Complex.exp ((Real.pi : ℂ) * Complex.I * ((H : ℂ) / 9)) * ·)
  apply Finset.sum_congr rfl
  intro r _
  calc
    inversionTerm s w v f b k r = readout r (dividedTranslation (sectorLOne s) r v) := by
      rw [rightInsertionEval_apply]
      rfl
    _ = _ := by
      rw [show dividedTranslation (sectorLOne s) r v =
        dividedTranslation (sectorLOne s) r (((fixedField s a)[[m]]) u) from rfl,
        sectorLOne_divided_inverted_iterate s a u e ha m r]
      simp only [map_sum, map_smul, smul_eq_mul]
      simp only [readout, rightInsertionEval_apply]

/-- The actual inverted iterate has no terms beyond the cutoff determined
by its homogeneous output grade. -/
theorem invertedCoeff_iterate_term_eq_zero_of_le (s : Fin 3) (a : fixedStates) (u : sector s)
    (e h : ℤ) (ha : L₀ a.val = (e : ℂ) • a.val)
    (hu : totalLZero u.val = ((h : ℂ) / 9) • u.val)
    (m : ℤ) (w : ℂ) (f : Module.Dual ℂ (totalLZero.eigenspace w))
    (b : fixedStates) (k : ℤ) (r : ℕ)
    (hr : ((h + 9 * (e - m - 1) - 16) / 9).toNat + 1 ≤ r) :
    f (gradeProjection w ((rightInsertion s
      (dividedTranslation (sectorLOne s) r (((fixedField s a)[[m]]) u)) b).coeff
        ((r : ℤ) - k)).val) = 0 :=
  inversionTerm_eq_zero_of_le s (h + 9 * (e - m - 1)) w _
    (fixedMode_weight s a u e h ha hu m) f b k r hr

/-- The outer iterate modes vanish uniformly past the minimum actual twisted
weight, so the Borcherds iterate channel has a finite cutoff. -/
theorem invertedCoeff_iterate_cutoff (s : Fin 3) (a : fixedStates) (u : sector s)
    (e h : ℤ) (ha : L₀ a.val = (e : ℂ) • a.val)
    (hu : totalLZero u.val = ((h : ℂ) / 9) • u.val)
    (m : ℤ) (w : ℂ) (f : Module.Dual ℂ (totalLZero.eigenspace w))
    (b : fixedStates) (k : ℤ) (t : ℕ)
    (ht : ((h + 9 * (e - m - 1) - 16) / 9).toNat + 1 ≤ t) :
    invertedCoeff s (h + 9 * (e - (m + (t : ℤ)) - 1)) w
      (((fixedField s a)[[m + (t : ℤ)]]) u) f b k = 0 := by
  have hBelow : h + 9 * (e - (m + (t : ℤ)) - 1) < 16 := by omega
  rw [fixedMode_eq_zero_of_below_minimum s a u e h ha hu _ hBelow]
  unfold invertedCoeff
  suffices (∑ j ∈ Finset.range
      (((h + 9 * (e - (m + (t : ℤ)) - 1) - 16) / 9).toNat + 1),
      inversionTerm s w 0 f b k j) = 0 by rw [this, mul_zero]
  apply Finset.sum_eq_zero
  intro j _
  simp only [inversionTerm, ← rightInsertionEval_apply, map_zero]

private theorem sourceGrade_weight (d : ℤ) (a : fixedGrade d) :
    L₀ a.val = (d : ℂ) • a.val :=
  (actualL0_eigen_iff_grade lattice (actualInverse lattice)
    (actualInverse_left lattice gram_det_unit) (actualInverse_right lattice gram_det_unit)
    d a.val).mpr a.property.2

-- Fixed vectors split into actual homogeneous fixed vectors by averaging each
-- grade component. Grade selection then reads the pairing on all fixed tests.
private theorem evaluation_pairing_fixed (s : Fin 3) (h : ℤ) (w : ℂ) (u : sector s)
    (hu : totalLZero u.val = ((h : ℂ) / 9) • u.val)
    (f : Module.Dual ℂ (totalLZero.eigenspace w)) (k d : ℤ)
    (hw : w = (h : ℂ) / 9 + (d : ℂ) - (k : ℂ)) (b : fixedStates) :
    sourcePairing lattice (evaluation s h w u f k d).val b.val =
      invertedCoeff s h w u f b k := by
  classical
  let component (e : ℤ) : fixedGrade e := by
    let p := LatticePositiveEnergy.gradeProjection lattice e b.val
    have hp : L₀ p = (e : ℂ) • p :=
      (actualL0_eigen_iff_grade lattice (actualInverse lattice)
        (actualInverse_left lattice gram_det_unit) (actualInverse_right lattice gram_det_unit)
        e p).mpr (gradeProjection_mem lattice e b.val)
    refine ⟨fixedProjection p, (mem_fixedStates_iff _).mpr (fixedProjection_fixed p), ?_⟩
    apply (actualL0_eigen_iff_grade lattice (actualInverse lattice)
      (actualInverse_left lattice gram_det_unit) (actualInverse_right lattice gram_det_unit)
      e _).mp
    rw [sourceLZero_fixedProjection, hp, map_smul]
  have hb : (∑ e ∈ stateEnergies lattice b.val, fixedGradeInclusion e (component e)) = b := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum, component, fixedGradeInclusion, Submodule.coe_inclusion,
      map_sum, fixedProjection_eq_self _ (lift_fixed b)] using
      congrArg fixedProjection (sum_gradeProjections lattice b.val)
  rw [← invertedCoeffLinear_apply, ← hb]
  simp only [Submodule.coe_sum, map_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [invertedCoeffLinear_apply]
  change sourcePairing lattice (evaluation s h w u f k d).val (component e).val = _
  rw [evaluation_sourcePairing]
  by_cases he : d = e
  · subst e
    simp only [ite_true]
    rfl
  · rw [ite_eq_right he]
    by_contra hne
    have hgrade := (invertedCoeff_grade_of_ne_zero s h w (e : ℂ) u hu f
      (fixedGradeInclusion e (component e)) (sourceGrade_weight e (component e)) k
      (Ne.symm hne)).1
    have hde : (d : ℂ) = (e : ℂ) := by linear_combination hgrade - hw
    exact he (Int.cast_injective hde)

/-- The actual source `L(1) = ω₂` restricted to the cubic fixed subspace. -/
def sourceLOneOnFixed : Module.End ℂ fixedStates :=
  sourceMode 2 fixedOmega

private theorem sourceLOneOnFixed_pow_val (j : ℕ) (a : fixedStates) :
    ((sourceLOneOnFixed ^ j) a).val = (L₁ ^ j) a.val := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
      change LatticeAllStateReconstruction.mu lattice
        (LatticeActualConformalState.omega lattice (actualInverse lattice)) 2
        ((sourceLOneOnFixed ^ j) a).val = _
      rw [omega_product, ih]
      rfl

/-- The output product of HLZ (3.96), on the actual cubic fixed carrier.
The signed BPZ shift on the source test precedes the inverted right insertion. -/
theorem output_product_pairing (s : Fin 3) (h : ℤ) (w : ℂ) (u : sector s)
    (hu : totalLZero u.val = ((h : ℂ) / 9) • u.val)
    (f : Module.Dual ℂ (totalLZero.eigenspace w)) (k d m : ℤ)
    (hw : w = (h : ℂ) / 9 + (d : ℂ) - (k : ℂ))
    (e : ℤ) (a : fixedGrade e) (b : fixedStates) :
    sourcePairing lattice
      (fixedProduct (fixedGradeInclusion e a)
        (fixedGradeInclusion d (evaluation s h w u f k d)) m).val b.val =
      (-1 : ℂ) ^ e * ∑ i ∈ Finset.range (a.val.support.sup
        (fun α => MvPolynomial.weightedTotalDegree (sourceWeight lattice) (a.val α)) + 1),
        (i.factorial : ℂ)⁻¹ * (Complex.exp ((Real.pi : ℂ) * Complex.I * ((h : ℂ) / 9)) *
          ∑ j ∈ Finset.range (((h - 16) / 9).toNat + 1),
            f (gradeProjection w ((rightInsertion s
              (dividedTranslation (C (fixedField s fixedOmega) (-3)) j u)
              (fixedProduct ((sourceLOneOnFixed ^ i) (fixedGradeInclusion e a)) b
                (2 * e - (i : ℤ) - m - 2))).coeff ((j : ℤ) - k)).val)) := by
  change sourcePairing lattice (((LatticeAllStateField.Y lattice a.val)[[m]])
    (evaluation s h w u f k d).val) b.val = _
  rw [sourcePairing_allState lattice gram_det_unit e m a.val a.property.2,
    ← actualInverse_eq_complexInverse]
  apply congrArg ((-1 : ℂ) ^ e * ·)
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg ((i.factorial : ℂ)⁻¹ * ·)
  let test := fixedProduct ((sourceLOneOnFixed ^ i) (fixedGradeInclusion e a)) b
    (2 * e - (i : ℤ) - m - 2)
  have htest : test.val = ((LatticeAllStateField.Y lattice ((L₁ ^ i) a.val))
      [[2 * e - (i : ℤ) - m - 2]]) b.val := by
    change ((LatticeAllStateField.Y lattice
      (((sourceLOneOnFixed ^ i) (fixedGradeInclusion e a)).val))
      [[2 * e - (i : ℤ) - m - 2]]) b.val = _
    rw [sourceLOneOnFixed_pow_val]
    rfl
  rw [← htest, evaluation_pairing_fixed s h w u hu f k d hw test]
  rfl

private theorem gradedPairing_lof_projection (w : ℝ) (f : GradeDual w) (v : State) :
    gradedPairing (DirectSum.lof ℂ ℝ GradeDual w f) v = f (gradeProjection (w : ℂ) v) := by
  let assemble := DirectSum.coeLinearMap (fun t : ℝ => totalLZero.eigenspace (t : ℂ))
  have hAssemble : assemble (stateDecompose v) = v := stateDecompose.symm_apply_apply v
  have h : (gradedPairing (DirectSum.lof ℂ ℝ GradeDual w f)).comp assemble =
      (f.comp (gradeProjection (w : ℂ))).comp assemble := by
    apply DirectSum.linearMap_ext
    intro t
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, assemble, DirectSum.coeLinearMap_lof]
    by_cases htw : t = w
    · subst t
      rw [gradedPairing_lof_grade, gradeProjection_self]
    · rw [gradedPairing_lof_grade_of_ne htw,
        gradeProjection_eq_zero (Module.End.mem_eigenspace_iff.mp x.property)
          (fun he => htw (Complex.ofReal_injective he.symm)), map_zero]
  simpa only [LinearMap.comp_apply, hAssemble] using
    LinearMap.congr_fun h (stateDecompose v)

/-- The dual product of HLZ (3.97) on a single actual input grade. The dual
mode has cubic-cover exponent `3*l`. Its BPZ transpose acts on the value of
the inverted right insertion by integral fixed-module modes. -/
theorem dual_product_pairing (s : Fin 3) (h : ℤ) (w : ℝ) (u : sector s)
    (f : GradeDual w) (k l d : ℤ) (e : ℕ) (a : fixedGrade (e : ℤ)) (b : fixedGrade d) :
    let w' := shiftedWeight w e (3 * l)
    let g := C (dualField a.val) (3 * l) (DirectSum.lof ℂ ℝ GradeDual w f)
    fixedGradeForm d (evaluation s h (w' : ℂ) u (g w') k d) b =
      Complex.exp ((Real.pi : ℂ) * Complex.I * ((h : ℂ) / 9)) *
        ∑ j ∈ Finset.range (((h - 16) / 9).toNat + 1),
          ((-1 : ℂ) ^ e * ∑ i ∈ Finset.range (e + 1),
            (i.factorial : ℂ)⁻¹ * f (gradeProjection (w : ℂ)
              (C (fixedField s ((sourceLOneOnFixed ^ i) (fixedGradeInclusion (e : ℤ) a)))
                (-l - 2 * (e : ℤ) + (i : ℤ))
                ((rightInsertion s (dividedTranslation (C (fixedField s fixedOmega) (-3)) j u)
                  (fixedGradeInclusion d b)).coeff ((j : ℤ) - k))).val)) := by
  intro w' g
  have ha : L₀ a.val = (e : ℂ) • a.val := by
    simpa only [Int.cast_natCast] using sourceGrade_weight (e : ℤ) a
  have hg : g = DirectSum.lof ℂ ℝ GradeDual w' (g w') := by
    dsimp only [g, w']
    rw [dualField_homogeneous a.val e ha, oppositeField_coeff, coeff_lof, DirectSum.lof_apply]
  rw [evaluation_pairing, invertedCoeff]
  apply congrArg (Complex.exp ((Real.pi : ℂ) * Complex.I * ((h : ℂ) / 9)) * ·)
  apply Finset.sum_congr rfl
  intro j _
  let v := (rightInsertion s (dividedTranslation (C (fixedField s fixedOmega) (-3)) j u)
    (fixedGradeInclusion d b)).coeff ((j : ℤ) - k)
  change g w' (gradeProjection (w' : ℂ) v.val) = _
  rw [← gradedPairing_lof_projection, ← hg]
  change gradedPairing (C (dualField a.val) (3 * l) (DirectSum.lof ℂ ℝ GradeDual w f)) v.val = _
  rw [gradedPairing_dualField_coeff a.val e ha]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply congrArg ((-1 : ℂ) ^ e * ·)
  apply Finset.sum_congr rfl
  intro i _
  rw [gradedPairing_lof_projection, fixedField_coeff_val, sourceLOneOnFixed_pow_val]
  have hi : -(3 * l) - 6 * (e : ℤ) + 3 * (i : ℤ) =
      3 * (-l - 2 * (e : ℤ) + (i : ℤ)) := by ring
  change (i.factorial : ℂ)⁻¹ * f (gradeProjection (w : ℂ)
    (bpzTerm a.val e (3 * l) i v.val)) =
    (i.factorial : ℂ)⁻¹ * f (gradeProjection (w : ℂ)
      (C (P48qAllJetWickField.nativeField ((L₁ ^ i) a.val))
        (3 * (-l - 2 * (e : ℤ) + (i : ℤ))) v.val))
  rw [bpzTerm, hi]

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
#print axioms output_product_pairing
#print axioms dual_product_pairing
#print axioms evaluation_translation
#print axioms evaluation_ground_vacuum
#print axioms evaluation_ground_ne_zero

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeOppositeEvaluation
