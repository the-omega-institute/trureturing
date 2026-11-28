/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeOppositeEvaluation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeOppositeEvaluation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual fixed-source states representing the BPZ-inverted twisted coefficients. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeOppositeGrade
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeFixedInvertedIterate
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeDualIteratePairing
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
  carrierCoeffEquiv chargeEnergy_nonneg energy gradeProjection_mem mem_grade_iff
  stateEnergies sum_gradeProjections)
open LatticeSugawaraCurrents (sugawaraMode)
open P48qConformalVectorDecomposition (actualInverse_eq_complexInverse)
open P48qFixedSourceBPZ (fixedGrade fixedGradeForm fixedGradeForm_nondegenerate)
open P48qGramPositivity (nebeGram_posDef)
open P48qNativeConformalSector
  (fixedStates sector fixedField fixedField_coeff_val fixedOmega fixedProduct fixedVacuum)
open P48qNativeDualCoefficients (bpzTerm sourceLOne_pow_eq_zero_of_lt)
open P48qNativeDualIteratePairing (sum_range_iterate_simplex_reindex)
open P48qNativeDualLinearField (dualField dualField_homogeneous)
open P48qNativeFixedInvertedIterate
  (fixedSourceLOne sectorLOne sectorLOne_divided_inverted_iterate)
open P48qNativeFixedRightInsertion (rightInsertion sectorTranslation)
open P48qNativeFixedRightJacobi (rightInsertion_borcherds)
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
open P48qTwistedStateEnergy (totalLZero totalLZero_minimum)
open SourceBPZ.AllStateTranspose (sourcePairing_allState)
open SourceBPZ.OriginalSourcePairing (sourcePairing sourcePairing_vacuum)
open SourceBPZ.SourcePairingLaws (sourcePairing_grade)
open StateField.BorcherdsPermutations (dividedTranslation)
open StateFieldResidueReconstruction (epsilon integerBinomial)
open SourceMobius (sectorL1_degree_bound sugawara_pow_single)
open private gram_det_unit from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qConformalVectorDecomposition
open private restrictedDualJacobi_iterate_reindex from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeDualIteratePairing
open private fixedSourceLOne_pow_val from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeFixedInvertedIterate
open private sourceLOne_pow_weight from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeSourceMobius
open private fixedProjection fixedProjection_eq_self fixedProjection_fixed lift_fixed
  mem_fixedStates_iff sourceLZero_fixedProjection from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeConformalSector
open private rightMode sourceMode from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeFixedRightJacobi
open private dividedConformal_weight gradeProjection_eq_zero gradeProjection_self inversionTerm
  inversionTerm_eq_zero_of_le rightInsertionEval rightInsertionEval_apply from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeOppositeVacuum
open private actualGrade_eq_zero_of_lt from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeRestrictedDualField
open private finsum_range support_subset_range epsilon_add sign_square from
  D5.S3.VertexAlgebra.StateField.BorcherdsPermutations

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

private theorem invertedCoeff_zero_input (s : Fin 3) (h : ℤ) (w : ℂ)
    (f : Module.Dual ℂ (totalLZero.eigenspace w)) (b : fixedStates) (k : ℤ) :
    invertedCoeff s h w 0 f b k = 0 := by
  simp only [invertedCoeff, inversionTerm, ← rightInsertionEval_apply, map_zero,
    Finset.sum_const_zero, mul_zero]

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
  rw [fixedMode_eq_zero_of_below_minimum s a u e h ha hu _ hBelow, invertedCoeff_zero_input]

private theorem lowered_iterate_eq_zero (s : Fin 3) (a : fixedStates) (u : sector s)
    (e h : ℤ) (ha : L₀ a.val = (e : ℂ) • a.val)
    (hu : totalLZero u.val = ((h : ℂ) / 9) • u.val)
    (r : ℤ) (i l n : ℕ)
    (hBelow : h - 9 * (l : ℤ) + 9 * (e - (i : ℤ) - (r + (n : ℤ)) - 1) < 16) :
    ((fixedField s (dividedTranslation fixedSourceLOne i a))[[r + (n : ℤ)]])
      (dividedTranslation (sectorLOne s) l u) = 0 := by
  let aDiv := dividedTranslation fixedSourceLOne
  let uDiv := dividedTranslation (sectorLOne s)
  have haDiv : L₀ (aDiv i a).val = ((e - (i : ℤ) : ℤ) : ℂ) • (aDiv i a).val := by
    simp only [aDiv, dividedTranslation, LinearMap.smul_apply, Submodule.coe_smul,
      fixedSourceLOne_pow_val, map_smul, sourceLOne_pow_weight a.val _ ha i,
      Int.cast_sub, Int.cast_natCast, smul_smul]
    rw [mul_comm]
  have huDiv : totalLZero (uDiv l u).val =
      (((h - 9 * (l : ℤ) : ℤ) : ℂ) / 9) • (uDiv l u).val := by
    have hWeight := dividedConformal_weight s 1 u ((h : ℂ) / 9) hu l
    have hScalar : (h : ℂ) / 9 - (l : ℂ) * ((1 : ℤ) : ℂ) =
        (((h - 9 * (l : ℤ) : ℤ) : ℂ) / 9) := by push_cast; ring
    rw [hScalar] at hWeight
    exact hWeight
  exact fixedMode_eq_zero_of_below_minimum s (aDiv i a) (uDiv l u)
    (e - (i : ℤ)) (h - 9 * (l : ℤ)) haDiv huDiv (r + (n : ℤ)) hBelow

set_option maxHeartbeats 3000000 in
/-- The outer opposite iterate, paired with a fixed test state, equals the
paired native right-insertion iterate. With mode origin `2h/9`, the
coefficient indexed by `-p-q+2e-2r-3-j` has physical mode
`2h/9 + p+q-j` on the input of weight `(h+9(e-r-j-1))/9`.
The cutoff is empty when the first intermediate weight is below `16/9`. -/
theorem invertedCoeff_iterate_sum_pairing (s : Fin 3) (a : fixedStates) (u : sector s)
    (e h : ℤ) (ha : L₀ a.val = (e : ℂ) • a.val)
    (hu : totalLZero u.val = ((h : ℂ) / 9) • u.val)
    (p q r : ℤ) (w : ℂ) (f : Module.Dual ℂ (totalLZero.eigenspace w)) (b : fixedStates) :
    let H₀ : ℤ := h + 9 * (e - r - 1)
    let K : ℕ := ((H₀ - 16) / 9 + 1).toNat
    let pNative (i : ℕ) : ℤ := 2 * e - r - (i : ℤ) - 2 - p
    let qNative (l : ℕ) : ℤ := -q - r - (l : ℤ) - 2
    let aDiv := dividedTranslation fixedSourceLOne
    let uDiv := dividedTranslation (sectorLOne s)
    let R (m : ℤ) (v : sector s) (c : fixedStates) :=
      (rightInsertion s v c).coeff (-m - 1)
    (∑ᶠ j : ℕ, integerBinomial p j *
      invertedCoeff s (h + 9 * (e - (r + (j : ℤ)) - 1)) w
        (((fixedField s a)[[r + (j : ℤ)]]) u) f b
        (-p - q + 2 * e - 2 * r - 3 - (j : ℤ))) =
      Complex.exp ((Real.pi : ℂ) * Complex.I * ((H₀ : ℂ) / 9)) *
        ∑ i ∈ Finset.range K, ∑ l ∈ Finset.range (K - i),
          f (gradeProjection w (∑ᶠ n : ℕ, integerBinomial (pNative i) n •
            R (pNative i + qNative l - (n : ℤ))
              (((fixedField s (aDiv i a))[[r + (n : ℤ)]]) (uDiv l u)) b).val) := by
  classical
  intro H₀ K pNative qNative aDiv uDiv R
  let H (j : ℕ) : ℤ := h + 9 * (e - (r + (j : ℤ)) - 1)
  let k (j : ℕ) : ℤ := -p - q + 2 * e - 2 * r - 3 - (j : ℤ)
  let phase := Complex.exp ((Real.pi : ℂ) * Complex.I * ((H₀ : ℂ) / 9))
  let B (i : ℕ) : ℤ := 2 * e - r - (i : ℤ) - 2
  let readout := f.comp ((gradeProjection w).comp (sector s).subtype)
  let native (i l n : ℕ) : sector s :=
    R (pNative i + qNative l - (n : ℤ))
      (((fixedField s (aDiv i a))[[r + (n : ℤ)]]) (uDiv l u)) b
  let F (i l n : ℕ) : ℂ := readout (native i l n)
  let G (i l j v : ℕ) : ℂ := integerBinomial p j *
    ((-1 : ℂ) ^ j * (integerBinomial (B i - (j : ℤ)) v * F i l (j + v)))
  have hCutoff (n : ℕ) (hn : K ≤ n) : H₀ - 9 * (n : ℤ) < 16 := by
    dsimp only [K] at hn
    omega
  have hOuterTail (j : ℕ) (hj : K ≤ j) :
      integerBinomial p j *
        invertedCoeff s (H j) w (((fixedField s a)[[r + (j : ℤ)]]) u) f b (k j) = 0 := by
    have hBelow : H j < 16 := by
      have hlt := hCutoff j hj
      dsimp only [H, H₀] at hlt ⊢
      omega
    rw [fixedMode_eq_zero_of_below_minimum s a u e h ha hu _ hBelow,
      invertedCoeff_zero_input, mul_zero]
  have castChoose (z : ℤ) (n : ℕ) : integerBinomial z n = Ring.choose (z : ℂ) n :=
    Ring.map_choose (Int.castRingHom ℂ) z n
  have hPhase (j : ℕ) :
      Complex.exp ((Real.pi : ℂ) * Complex.I * ((H j : ℂ) / 9)) =
        phase * (-1 : ℂ) ^ j := by
    have hH : H j = H₀ - 9 * (j : ℤ) := by dsimp only [H, H₀]; omega
    simp only [hH, show ((Real.pi : ℂ) * Complex.I * (((H₀ - 9 * (j : ℤ) : ℤ) : ℂ) / 9)) =
      (Real.pi : ℂ) * Complex.I * ((H₀ : ℂ) / 9) +
        (j : ℂ) * -((Real.pi : ℂ) * Complex.I) by
      push_cast
      ring,
      Complex.exp_add, Complex.exp_nat_mul, Complex.exp_neg_pi_mul_I, phase]
  have hExpand (j : ℕ) (hj : j < K) :
      integerBinomial p j *
        invertedCoeff s (H j) w (((fixedField s a)[[r + (j : ℤ)]]) u) f b (k j) =
        phase * ∑ t ∈ Finset.range (K - j), ∑ i ∈ Finset.range (t + 1),
          ∑ l ∈ Finset.range (t - i + 1), G i l j (t - i - l) := by
    have hRange : ((H j - 16) / 9).toNat + 1 = K - j := by
      dsimp only [H, H₀, K] at hj ⊢
      omega
    have hc := invertedCoeff_iterate_coeff s a u e h ha (r + (j : ℤ)) w f b (k j)
    dsimp only at hc
    change invertedCoeff s (H j) w (((fixedField s a)[[r + (j : ℤ)]]) u) f b (k j) =
      Complex.exp ((Real.pi : ℂ) * Complex.I * ((H j : ℂ) / 9)) *
      ∑ t ∈ Finset.range (((H j - 16) / 9).toNat + 1), _ at hc
    rw [hc, hRange, hPhase]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro l hl
    have hi' := Finset.mem_range.mp hi
    have hl' := Finset.mem_range.mp hl
    have hMode : r + (j : ℤ) + (t : ℤ) - (i : ℤ) - (l : ℤ) =
        r + ((j + (t - i - l) : ℕ) : ℤ) := by omega
    have hCoeff : (t : ℤ) - k j =
        -(pNative i + qNative l - ((j + (t - i - l) : ℕ) : ℤ)) - 1 := by
      dsimp only [k, pNative, qNative]
      omega
    have hTop : 2 * e - (r + (j : ℤ)) - (i : ℤ) - 2 = B i - (j : ℤ) := by
      dsimp only [B]
      omega
    simp only [G, F, native, R, readout, aDiv, uDiv, LinearMap.comp_apply,
      Submodule.subtype_apply, hMode, hCoeff, hTop]
    ring
  have hTail (i l n : ℕ) (hn : K - i - l ≤ n) : native i l n = 0 := by
    have hBelow : h - 9 * (l : ℤ) + 9 * (e - (i : ℤ) - (r + (n : ℤ)) - 1) < 16 := by
      have hlt := hCutoff (i + l + n) (by omega)
      dsimp only [H₀] at hlt
      omega
    have hz := lowered_iterate_eq_zero s a u e h ha hu r i l n hBelow
    change rightMode s (pNative i + qNative l - (n : ℤ))
      (((fixedField s (aDiv i a))[[r + (n : ℤ)]]) (uDiv l u)) b = 0
    change ((fixedField s (aDiv i a))[[r + (n : ℤ)]]) (uDiv l u) = 0 at hz
    rw [hz, map_zero, LinearMap.zero_apply]
  change (∑ᶠ j : ℕ, integerBinomial p j *
    invertedCoeff s (H j) w (((fixedField s a)[[r + (j : ℤ)]]) u) f b (k j)) =
      phase * ∑ i ∈ Finset.range K, ∑ l ∈ Finset.range (K - i),
        readout (∑ᶠ n : ℕ, integerBinomial (pNative i) n • native i l n)
  rw [finsum_range hOuterTail]
  calc
    _ = phase * (∑ j ∈ Finset.range K, ∑ t ∈ Finset.range (K - j),
          ∑ i ∈ Finset.range (t + 1), ∑ l ∈ Finset.range (t - i + 1),
            G i l j (t - i - l)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j hj => hExpand j (Finset.mem_range.mp hj))
    _ = phase * (∑ i ∈ Finset.range K, ∑ l ∈ Finset.range (K - i),
          ∑ j ∈ Finset.range (K - i - l), ∑ v ∈ Finset.range (K - i - l - j),
            G i l j v) := by rw [sum_range_iterate_simplex_reindex K G]
    _ = _ := by
      apply congrArg (phase * ·)
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro l _
      rw [finsum_range (N := K - i - l) (fun n hn => by rw [hTail i l n hn, smul_zero])]
      simp only [map_sum, map_smul, smul_eq_mul]
      have hTop : ((B i : ℤ) : ℂ) - (p : ℂ) = (pNative i : ℂ) := by
        change _ = ((B i - p : ℤ) : ℂ)
        exact (Int.cast_sub (B i) p).symm
      have hReindex :=
        restrictedDualJacobi_iterate_reindex (p : ℂ) (B i : ℂ) (K - i - l) (F i l)
      rw [hTop] at hReindex
      simpa only [G, F, castChoose, Int.cast_sub, Int.cast_natCast, smul_eq_mul,
        Finset.mul_sum, mul_assoc] using hReindex

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

/-- At the common output grade, the paired sum of the actual opposite
evaluation states equals the divided-power native right-insertion iterate. -/
theorem evaluation_iterate_sum_pairing (s : Fin 3) (a : fixedStates) (u : sector s)
    (e h : ℤ) (ha : L₀ a.val = (e : ℂ) • a.val)
    (hu : totalLZero u.val = ((h : ℂ) / 9) • u.val)
    (p q r d : ℤ) (w : ℂ) (f : Module.Dual ℂ (totalLZero.eigenspace w))
    (hw : w = (h : ℂ) / 9 + (d : ℂ) + (p : ℂ) + (q : ℂ) - (e : ℂ) + (r : ℂ) + 2)
    (b : fixedStates) :
    let H₀ : ℤ := h + 9 * (e - r - 1)
    let K : ℕ := ((H₀ - 16) / 9 + 1).toNat
    let pNative (i : ℕ) : ℤ := 2 * e - r - (i : ℤ) - 2 - p
    let qNative (l : ℕ) : ℤ := -q - r - (l : ℤ) - 2
    let R (m : ℤ) (v : sector s) (c : fixedStates) :=
      (rightInsertion s v c).coeff (-m - 1)
    (∑ᶠ j : ℕ, integerBinomial p j *
      sourcePairing lattice
        (evaluation s (h + 9 * (e - (r + (j : ℤ)) - 1)) w
          (((fixedField s a)[[r + (j : ℤ)]]) u) f
          (-p - q + 2 * e - 2 * r - 3 - (j : ℤ)) d).val b.val) =
      Complex.exp ((Real.pi : ℂ) * Complex.I * ((H₀ : ℂ) / 9)) *
        ∑ i ∈ Finset.range K, ∑ l ∈ Finset.range (K - i),
          f (gradeProjection w (∑ᶠ n : ℕ, integerBinomial (pNative i) n •
            R (pNative i + qNative l - (n : ℤ))
              (((fixedField s (dividedTranslation fixedSourceLOne i a))[[r + (n : ℤ)]])
                (dividedTranslation (sectorLOne s) l u)) b).val) := by
  intro H₀ K pNative qNative R
  have hPair (j : ℕ) :
      sourcePairing lattice
        (evaluation s (h + 9 * (e - (r + (j : ℤ)) - 1)) w
          (((fixedField s a)[[r + (j : ℤ)]]) u) f
          (-p - q + 2 * e - 2 * r - 3 - (j : ℤ)) d).val b.val =
      invertedCoeff s (h + 9 * (e - (r + (j : ℤ)) - 1)) w
        (((fixedField s a)[[r + (j : ℤ)]]) u) f b (-p - q + 2 * e - 2 * r - 3 - (j : ℤ)) := by
    apply evaluation_pairing_fixed
    · exact fixedMode_weight s a u e h ha hu _
    · rw [hw]
      push_cast
      ring
  simp_rw [hPair]
  exact invertedCoeff_iterate_sum_pairing s a u e h ha hu p q r w f b

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

private def sourceLoweringCutoff (e : ℤ) (a : fixedGrade e) : ℕ :=
  a.val.support.sup (fun α => MvPolynomial.weightedTotalDegree (sourceWeight lattice) (a.val α)) + 1

private theorem sourceLowering_eq_zero (e : ℤ) (a : fixedGrade e) (i : ℕ)
    (hi : sourceLoweringCutoff e a ≤ i) :
    dividedTranslation fixedSourceLOne i (fixedGradeInclusion e a) = 0 := by
  have hpow : (L₁ ^ i) a.val = 0 := by
    rw [← Finsupp.sum_single a.val]
    change (L₁ ^ i) (∑ α ∈ a.val.support, Finsupp.single α (a.val α)) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro α hα
    rw [sugawara_pow_single lattice (actualInverse lattice)
      (actualInverse_left lattice gram_det_unit) (actualInverse_right lattice gram_det_unit)]
    have hdeg : MvPolynomial.weightedTotalDegree (sourceWeight lattice) (a.val α) + 1 ≤ i :=
      (Nat.add_le_add_right
        (Finset.le_sup (f := fun α =>
          MvPolynomial.weightedTotalDegree (sourceWeight lattice) (a.val α)) hα) 1).trans hi
    rw [Module.End.pow_map_zero_of_le hdeg (sectorL1_degree_bound lattice α (a.val α)),
      Finsupp.single_zero]
  apply Subtype.ext
  simp only [dividedTranslation, LinearMap.smul_apply, Submodule.coe_smul,
    fixedSourceLOne_pow_val, fixedGradeInclusion, Submodule.coe_inclusion,
    hpow, smul_zero, Submodule.coe_zero]

private theorem sectorLowering_eq_zero (s : Fin 3) (h : ℤ) (u : sector s)
    (hu : totalLZero u.val = ((h : ℂ) / 9) • u.val)
    (l : ℕ) (hl : ((h - 16) / 9).toNat + 1 ≤ l) :
    dividedTranslation (sectorLOne s) l u = 0 := by
  let v := dividedTranslation (sectorLOne s) l u
  have hInt : h - 16 < 9 * (l : ℤ) := by omega
  have hReal : (h : ℝ) - 16 < 9 * (l : ℝ) := by exact_mod_cast hInt
  have he : totalLZero v.val = (((h : ℝ) / 9 - (l : ℝ) : ℝ) : ℂ) • v.val := by
    simp only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_intCast,
      Complex.ofReal_natCast, Complex.ofReal_ofNat]
    rw [← mul_one (l : ℂ), ← Int.cast_one]
    exact dividedConformal_weight s 1 u ((h : ℂ) / 9) hu l
  by_contra hv
  have hmin := totalLZero_minimum.2 ⟨v.val, (fun hz => hv (Subtype.ext hz)), he⟩
  linarith

private theorem fixedProduct_zero_left (b : fixedStates) (n : ℤ) : fixedProduct 0 b n = 0 :=
  LinearMap.map_zero₂ (sourceMode n) b

private theorem fixedGrade_eq_zero_of_lt {d : ℤ} (hd : d < 0) (v : fixedGrade d) : v = 0 := by
  apply Subtype.ext
  apply (carrierCoeffEquiv lattice).injective
  apply Finsupp.ext
  intro x
  rw [Submodule.coe_zero, map_zero, Finsupp.zero_apply]
  change (v.val x.1).coeff x.2 = 0
  apply (mem_grade_iff lattice d v.val).mp v.property.2 x
  have hx := chargeEnergy_nonneg lattice nebeGram_posDef x.1
  dsimp only [energy]
  omega

set_option maxHeartbeats 8000000 in
-- Comparing both products requires elaborating the reflected mode indices at each cutoff.
/-- The homogeneous mixed Jacobi identity for the actual opposite evaluation,
paired with a homogeneous fixed test state. The dual mode uses the integral
index on the base coordinate, with its coefficient on the cubic cover. -/
theorem evaluation_mixedJacobi_pairing (s : Fin 3) (e : ℤ) (a : fixedGrade e)
    (h : ℤ) (u : sector s) (hu : totalLZero u.val = ((h : ℂ) / 9) • u.val)
    (w : ℝ) (f : GradeDual w) (p q r d : ℤ) (b : fixedGrade d)
    (hw : (w : ℂ) = (h : ℂ) / 9 + (d : ℂ) + (p : ℂ) + (q : ℂ) -
      (e : ℂ) + (r : ℂ) + 2) :
    let A := fixedGradeInclusion e a
    let output (j : ℕ) :=
      let m : ℤ := p + r - (j : ℤ)
      let g : ℤ := d - e + m + 1
      sourcePairing lattice
        (fixedProduct A (fixedGradeInclusion g
          (evaluation s h (w : ℂ) u f (-q - (j : ℤ) - 1) g)) m).val b.val
    let dual (j : ℕ) :=
      let m : ℤ := -(p + (j : ℤ)) - 1
      let w' := shiftedWeight w e.toNat (3 * m)
      let g := C (dualField a.val) (3 * m) (DirectSum.lof ℂ ℝ GradeDual w f)
      fixedGradeForm d (evaluation s h (w' : ℂ) u (g w') (-q - r + (j : ℤ) - 1) d) b
    let weight (j : ℕ) := (-1 : ℂ) ^ j * integerBinomial r j
    (∑ᶠ j : ℕ, integerBinomial p j *
      sourcePairing lattice
        (evaluation s (h + 9 * (e - (r + (j : ℤ)) - 1)) (w : ℂ)
          (((fixedField s A)[[r + (j : ℤ)]]) u) f
          (-p - q + 2 * e - 2 * r - 3 - (j : ℤ)) d).val b.val) =
      (∑ᶠ j : ℕ, weight j * output j) - epsilon r * (∑ᶠ j : ℕ, weight j * dual j) := by
  classical
  by_cases he : 0 ≤ e
  swap
  · have ha0 := fixedGrade_eq_zero_of_lt (lt_of_not_ge he) a
    subst a
    intro A output dual weight
    have hA : A = 0 := map_zero (fixedGradeInclusion e)
    have hOut (j : ℕ) : output j = 0 := by
      dsimp only [output]
      rw [hA, fixedProduct_zero_left, Submodule.coe_zero, map_zero, LinearMap.zero_apply]
    have hDual (j : ℕ) : dual j = 0 := by
      simp [dual, evaluation_pairing, invertedCoeff, inversionTerm]
    have hIter (j : ℕ) :
        sourcePairing lattice
          (evaluation s (h + 9 * (e - (r + (j : ℤ)) - 1)) (w : ℂ)
            (((fixedField s A)[[r + (j : ℤ)]]) u) f
            (-p - q + 2 * e - 2 * r - 3 - (j : ℤ)) d).val b.val = 0 := by
      rw [hA]
      simp only [map_zero, Pi.zero_apply, LinearMap.zero_apply]
      change fixedGradeForm d (evaluation s _ (w : ℂ) 0 f _ d) b = 0
      rw [evaluation_pairing, invertedCoeff_zero_input]
    simp only [hIter, hOut, hDual, mul_zero, finsum_zero, sub_zero]
  lift e to ℕ using he
  intro A output dual weight
  simp only [Int.cast_natCast] at hw
  let B := fixedGradeInclusion d b
  let H₀ : ℤ := h + 9 * ((e : ℤ) - r - 1)
  let K : ℕ := ((H₀ - 16) / 9 + 1).toNat
  let I := max K (max (sourceLoweringCutoff (e : ℤ) a) (e + 1))
  let U := ((h - 16) / 9).toNat + 1
  let J := max K U
  let pNative (i : ℕ) : ℤ := 2 * (e : ℤ) - r - (i : ℤ) - 2 - p
  let qNative (l : ℕ) : ℤ := -q - r - (l : ℤ) - 2
  let R (m : ℤ) (v : sector s) (c : fixedStates) :=
    (rightInsertion s v c).coeff (-m - 1)
  let F := (f.comp (gradeProjection (w : ℂ))).comp (sector s).subtype
  let aDiv (i : ℕ) := dividedTranslation fixedSourceLOne i A
  let uDiv (l : ℕ) := dividedTranslation (sectorLOne s) l u
  let iter (i l n : ℕ) : sector s :=
    integerBinomial (pNative i) n •
      R (pNative i + qNative l - (n : ℤ)) (((fixedField s (aDiv i))[[r + (n : ℤ)]]) (uDiv l)) B
  let first (i l j : ℕ) : sector s :=
    weight j • ((fixedField s (aDiv i))[[pNative i + r - (j : ℤ)]])
      (R (qNative l + (j : ℤ)) (uDiv l) B)
  let second (i l j : ℕ) : sector s :=
    weight j • (epsilon r •
      R (qNative l + r - (j : ℤ)) (uDiv l) (fixedProduct (aDiv i) B (pNative i + (j : ℤ))))
  let phase := Complex.exp ((Real.pi : ℂ) * Complex.I * ((h : ℂ) / 9))
  let phaseIter := Complex.exp ((Real.pi : ℂ) * Complex.I * ((H₀ : ℂ) / 9))
  have ha : L₀ A.val = ((e : ℤ) : ℂ) • A.val := sourceGrade_weight (e : ℤ) a
  have hKI : K ≤ I := le_max_left _ _
  have hKJ : K ≤ J := le_max_left _ _
  have hUI : sourceLoweringCutoff (e : ℤ) a ≤ I :=
    (le_max_left _ _).trans (le_max_right _ _)
  have heI : e + 1 ≤ I := (le_max_right _ _).trans (le_max_right _ _)
  have hUJ : U ≤ J := le_max_right _ _
  have hRead (v : sector s) : F v = f (gradeProjection (w : ℂ) v.val) := rfl
  have hR (m : ℤ) (v : sector s) (c : fixedStates) : R m v c = rightMode s m v c := rfl
  have hAPow (i : ℕ) :
      aDiv i = (i.factorial : ℂ)⁻¹ • (sourceLOneOnFixed ^ i) A := rfl
  have hAWeight (i : ℕ) (hi : e + 1 ≤ i) : aDiv i = 0 := by
    have hz := sourceLOne_pow_eq_zero_of_lt a.val e
      (by simpa only [A, fixedGradeInclusion, Submodule.coe_inclusion, Int.cast_natCast] using ha)
      i (by omega)
    apply Subtype.ext
    simp only [aDiv, dividedTranslation, LinearMap.smul_apply, Submodule.coe_smul,
      fixedSourceLOne_pow_val, Submodule.coe_zero]
    change (i.factorial : ℂ)⁻¹ • (L₁ ^ i) a.val = 0
    rw [hz, smul_zero]
  have hU (l : ℕ) (hl : U ≤ l) : uDiv l = 0 := sectorLowering_eq_zero s h u hu l hl
  have hProdZero (i l j : ℕ) (hz : aDiv i = 0 ∨ uDiv l = 0) :
      first i l j = 0 ∧ second i l j = 0 := by
    rcases hz with hai | hul
    · simp only [first, second, hai, fixedProduct_zero_left, hR, map_zero, Pi.zero_apply,
        LinearMap.zero_apply, smul_zero, and_self]
    · simp only [first, second, hul, hR, map_zero, LinearMap.zero_apply, smul_zero, and_self]
  have hNative (i l : ℕ) :
      Function.HasFiniteSupport (first i l) ∧ Function.HasFiniteSupport (second i l) ∧
      F (∑ᶠ n : ℕ, iter i l n) =
        (∑ᶠ j : ℕ, F (first i l j)) - (∑ᶠ j : ℕ, F (second i l j)) := by
    obtain ⟨_, hf, hs, hsum⟩ :=
      rightInsertion_borcherds s (aDiv i) B (uDiv l) (pNative i) (qNative l) r
    change Function.HasFiniteSupport (first i l) at hf
    change Function.HasFiniteSupport (second i l) at hs
    refine ⟨hf, hs, ?_⟩
    have hsum' : (∑ᶠ n : ℕ, iter i l n) =
        ∑ᶠ j : ℕ, (first i l j - second i l j) := by
      simpa only [iter, first, second, smul_sub] using hsum
    rw [hsum', finsum_sub_distrib hf hs, map_sub, map_finsum F hf, map_finsum F hs]
  have hIterZero (i l : ℕ) (hil : K ≤ i + l) : F (∑ᶠ n : ℕ, iter i l n) = 0 := by
    rw [finsum_eq_zero_of_forall_eq_zero, map_zero]
    intro n
    have hBelow : h - 9 * (l : ℤ) +
        9 * ((e : ℤ) - (i : ℤ) - (r + (n : ℤ)) - 1) < 16 := by
      dsimp only [K, H₀] at hil
      omega
    have hz := lowered_iterate_eq_zero s A u (e : ℤ) h ha hu r i l n hBelow
    change ((fixedField s (aDiv i))[[r + (n : ℤ)]]) (uDiv l) = 0 at hz
    simp only [iter, hz, hR, map_zero, LinearMap.zero_apply, smul_zero]
  have hTriangle :
      (∑ i ∈ Finset.range K, ∑ l ∈ Finset.range (K - i), F (∑ᶠ n : ℕ, iter i l n)) =
        ∑ i ∈ Finset.range I, ∑ l ∈ Finset.range J, F (∑ᶠ n : ℕ, iter i l n) := by
    calc
      _ = ∑ i ∈ Finset.range K, ∑ l ∈ Finset.range J, F (∑ᶠ n : ℕ, iter i l n) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_subset (Finset.range_mono ((Nat.sub_le K i).trans hKJ))
        intro l _ hl
        exact hIterZero i l (by simp only [Finset.mem_range, not_lt] at hl; omega)
      _ = _ := by
        apply Finset.sum_subset (Finset.range_mono hKI)
        intro i _ hi
        apply Finset.sum_eq_zero
        intro l _
        exact hIterZero i l (by simp only [Finset.mem_range, not_lt] at hi; omega)
  let cells := (Finset.range I) ×ˢ (Finset.range J)
  let firstSum := ∑ i ∈ Finset.range I, ∑ l ∈ Finset.range J, ∑ᶠ j : ℕ, F (first i l j)
  let secondSum := ∑ i ∈ Finset.range I, ∑ l ∈ Finset.range J, ∑ᶠ j : ℕ, F (second i l j)
  have hFirstSum :
      (∑ᶠ j : ℕ, ∑ i ∈ Finset.range I, ∑ l ∈ Finset.range J, F (first i l j)) = firstSum := by
    have hFinite (c : ℕ × ℕ) : Function.HasFiniteSupport (fun j => F (first c.1 c.2 j)) :=
      (hNative c.1 c.2).1.subset (by
        intro j hj hz
        apply hj
        change F (first c.1 c.2 j) = 0
        rw [show first c.1 c.2 j = 0 from hz, map_zero])
    simpa only [firstSum, cells, Finset.sum_product] using
      (finsum_sum_comm cells (fun j c => F (first c.1 c.2 j)) (fun c _ => hFinite c))
  have hSecondSum :
      (∑ᶠ j : ℕ, ∑ i ∈ Finset.range I, ∑ l ∈ Finset.range J, F (second i l j)) = secondSum := by
    have hFinite (c : ℕ × ℕ) : Function.HasFiniteSupport (fun j => F (second c.1 c.2 j)) :=
      (hNative c.1 c.2).2.1.subset (by
        intro j hj hz
        apply hj
        change F (second c.1 c.2 j) = 0
        rw [show second c.1 c.2 j = 0 from hz, map_zero])
    simpa only [secondSum, cells, Finset.sum_product] using
      (finsum_sum_comm cells (fun j c => F (second c.1 c.2 j)) (fun c _ => hFinite c))
  have hPadProduct (term : ℕ → ℕ → ℂ) (N : ℕ) (hN : N ≤ I)
      (hA : ∀ i l, N ≤ i → term i l = 0) (hB : ∀ i l, U ≤ l → term i l = 0) :
      (∑ i ∈ Finset.range N, ∑ l ∈ Finset.range U, term i l) =
        ∑ i ∈ Finset.range I, ∑ l ∈ Finset.range J, term i l := by
    calc
      _ = ∑ i ∈ Finset.range N, ∑ l ∈ Finset.range J, term i l := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_subset (Finset.range_mono hUJ)
        intro l _ hl
        exact hB i l (by simpa only [Finset.mem_range, not_lt] using hl)
      _ = _ := by
        apply Finset.sum_subset (Finset.range_mono hN)
        intro i _ hi
        exact Finset.sum_eq_zero (fun l _ =>
          hA i l (by simpa only [Finset.mem_range, not_lt] using hi))
  have hOutput (j : ℕ) : weight j * output j =
      (phase * epsilon (e : ℤ) * epsilon r) *
        ∑ i ∈ Finset.range I, ∑ l ∈ Finset.range J, F (second i l j) := by
    let m : ℤ := p + r - (j : ℤ)
    let g : ℤ := d - (e : ℤ) + m + 1
    let k : ℤ := -q - (j : ℤ) - 1
    have hWeight : (w : ℂ) = (h : ℂ) / 9 + (g : ℂ) - (k : ℂ) := by
      rw [hw]
      dsimp only [g, m, k]
      push_cast
      ring
    change weight j * sourcePairing lattice
      (fixedProduct A (fixedGradeInclusion g (evaluation s h (w : ℂ) u f k g)) m).val B.val = _
    rw [output_product_pairing s h (w : ℂ) u hu f k g m hWeight (e : ℤ) a B,
      ← hPadProduct (fun i l => F (second i l j)) (sourceLoweringCutoff (e : ℤ) a) hUI
        (fun i l hi => by rw [(hProdZero i l j (Or.inl (sourceLowering_eq_zero (e : ℤ) a i hi))).2,
          map_zero])
        (fun i l hl => by rw [(hProdZero i l j (Or.inr (hU l hl))).2, map_zero])]
    simp only [sourceLoweringCutoff, U, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro l _
    have hm : 2 * (e : ℤ) - (i : ℤ) - m - 2 = pNative i + (j : ℤ) := by
      dsimp only [m, pNative]
      omega
    have hk : -(qNative l + r - (j : ℤ)) - 1 = (l : ℤ) - k := by
      dsimp only [qNative, k]
      omega
    let c := fixedProduct ((sourceLOneOnFixed ^ i) A) B (pNative i + (j : ℤ))
    have hc : fixedProduct (aDiv i) B (pNative i + (j : ℤ)) = (i.factorial : ℂ)⁻¹ • c := by
      rw [hAPow]
      change sourceMode _ _ B = (i.factorial : ℂ)⁻¹ • sourceMode _ _ B
      rw [map_smul, LinearMap.smul_apply]
    rw [hm]
    simp only [second, hR, hc, map_smul, smul_eq_mul]
    simp only [hRead]
    change weight j * ((-1 : ℂ) ^ (e : ℤ) *
      ((i.factorial : ℂ)⁻¹ * (phase * f (gradeProjection (w : ℂ)
        ((rightInsertion s (uDiv l) c).coeff ((l : ℤ) - k)).val)))) =
      phase * epsilon (e : ℤ) * epsilon r *
        (weight j * (epsilon r * ((i.factorial : ℂ)⁻¹ * f (gradeProjection (w : ℂ)
          ((rightInsertion s (uDiv l) c).coeff (-(qNative l + r - (j : ℤ)) - 1)).val))))
    rw [hk, ← epsilon]
    linear_combination -(phase * epsilon (e : ℤ) * weight j * (i.factorial : ℂ)⁻¹ *
      f (gradeProjection (w : ℂ) ((rightInsertion s (uDiv l) c).coeff ((l : ℤ) - k)).val)) *
        sign_square r
  have hDual (j : ℕ) : weight j * dual j =
      (phase * epsilon (e : ℤ)) *
        ∑ i ∈ Finset.range I, ∑ l ∈ Finset.range J, F (first i l j) := by
    let m : ℤ := -(p + (j : ℤ)) - 1
    let k : ℤ := -q - r + (j : ℤ) - 1
    let w' := shiftedWeight w e (3 * m)
    let g := C (dualField a.val) (3 * m) (DirectSum.lof ℂ ℝ GradeDual w f)
    change weight j * fixedGradeForm d (evaluation s h (w' : ℂ) u (g w') k d) b = _
    rw [dual_product_pairing s h w u f k m d e a b,
      ← hPadProduct (fun i l => F (first i l j)) (e + 1) heI
        (fun i l hi => by rw [(hProdZero i l j (Or.inl (hAWeight i hi))).1, map_zero])
        (fun i l hl => by rw [(hProdZero i l j (Or.inr (hU l hl))).1, map_zero])]
    simp only [U, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro l _
    have hm : -m - 2 * (e : ℤ) + (i : ℤ) = -(pNative i + r - (j : ℤ)) - 1 := by
      dsimp only [m, pNative]
      omega
    have hk : -(qNative l + (j : ℤ)) - 1 = (l : ℤ) - k := by
      dsimp only [qNative, k]
      omega
    rw [hm]
    simp only [first, hAPow, map_smul, Pi.smul_apply, LinearMap.smul_apply, smul_eq_mul]
    simp only [hRead]
    change _ = phase * epsilon (e : ℤ) *
      (weight j * ((i.factorial : ℂ)⁻¹ * f (gradeProjection (w : ℂ)
        (C (fixedField s ((sourceLOneOnFixed ^ i) A)) (-(pNative i + r - (j : ℤ)) - 1)
          (R (qNative l + (j : ℤ)) (uDiv l) B)).val)))
    have hRindex : R (qNative l + (j : ℤ)) (uDiv l) B =
        (rightInsertion s (uDiv l) B).coeff ((l : ℤ) - k) := by
      dsimp only [R]
      rw [hk]
    rw [hRindex, epsilon, zpow_natCast]
    let readout := f (gradeProjection (w : ℂ)
      (C (fixedField s ((sourceLOneOnFixed ^ i) A)) (-(pNative i + r - (j : ℤ)) - 1)
        ((rightInsertion s (uDiv l) B).coeff ((l : ℤ) - k))).val)
    change weight j * (phase * ((-1 : ℂ) ^ e * ((i.factorial : ℂ)⁻¹ * readout))) =
      phase * (-1 : ℂ) ^ e * (weight j * ((i.factorial : ℂ)⁻¹ * readout))
    ring
  have hPhase : phaseIter = -(phase * epsilon (e : ℤ) * epsilon r) := by
    have hArg : (Real.pi : ℂ) * Complex.I * ((H₀ : ℂ) / 9) =
        (Real.pi : ℂ) * Complex.I * ((h : ℂ) / 9) +
          (((e : ℤ) - r - 1 : ℤ) : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
      dsimp only [H₀]
      push_cast
      ring
    have hSign : epsilon ((e : ℤ) - r - 1) = -(epsilon (e : ℤ) * epsilon r) := by
      rw [sub_eq_add_neg (↑e : ℤ) r, sub_eq_add_neg, epsilon_add, epsilon_add]
      have hr : epsilon (-r) = epsilon r := by
        rw [epsilon, zpow_neg, ← inv_zpow]
        norm_num [epsilon]
      rw [hr, show epsilon (-1) = -1 by norm_num [epsilon], mul_neg, mul_one]
    rw [show phaseIter = Complex.exp ((Real.pi : ℂ) * Complex.I * ((H₀ : ℂ) / 9)) from rfl,
      hArg, Complex.exp_add, Complex.exp_int_mul, Complex.exp_pi_mul_I, ← epsilon, hSign]
    change phase * -(epsilon (e : ℤ) * epsilon r) = _
    ring
  have hIter := evaluation_iterate_sum_pairing s A u (e : ℤ) h ha hu p q r d (w : ℂ) f
    (by simpa only [Int.cast_natCast] using hw) B
  change _ = phaseIter *
    (∑ i ∈ Finset.range K, ∑ l ∈ Finset.range (K - i), F (∑ᶠ n : ℕ, iter i l n)) at hIter
  change (∑ᶠ j : ℕ, integerBinomial p j *
    sourcePairing lattice
      (evaluation s (h + 9 * ((e : ℤ) - (r + (j : ℤ)) - 1)) (w : ℂ)
        (((fixedField s A)[[r + (j : ℤ)]]) u) f
        (-p - q + 2 * (e : ℤ) - 2 * r - 3 - (j : ℤ)) d).val B.val) =
    (∑ᶠ j : ℕ, weight j * output j) - epsilon r * (∑ᶠ j : ℕ, weight j * dual j)
  have hNativeRead (i l : ℕ) :
      F (∑ᶠ n : ℕ, iter i l n) =
        (∑ᶠ j : ℕ, F (first i l j)) - (∑ᶠ j : ℕ, F (second i l j)) := (hNative i l).2.2
  rw [hIter, hTriangle]
  simp_rw [hNativeRead, Finset.sum_sub_distrib]
  have hOutSum : (∑ᶠ j : ℕ, weight j * output j) =
      phase * epsilon (e : ℤ) * epsilon r * secondSum := by
    simp_rw [hOutput]
    rw [← mul_finsum, hSecondSum]
  have hDualSum : (∑ᶠ j : ℕ, weight j * dual j) =
      phase * epsilon (e : ℤ) * firstSum := by
    simp_rw [hDual]
    rw [← mul_finsum, hFirstSum]
  change phaseIter * (firstSum - secondSum) = _
  rw [hPhase, hOutSum, hDualSum]
  ring

private def fixedProductOnGrade {e g d : ℤ} (a : fixedGrade e) (v : fixedGrade g)
    (m : ℤ) (hd : e + g - m - 1 = d) : fixedGrade d := by
  let product := fixedProduct (fixedGradeInclusion e a) (fixedGradeInclusion g v) m
  refine ⟨product.val, product.property, ?_⟩
  apply (actualL0_eigen_iff_grade lattice (actualInverse lattice)
    (actualInverse_left lattice gram_det_unit) (actualInverse_right lattice gram_det_unit)
    d product.val).mp
  rw [← hd, Int.cast_sub, Int.cast_sub, Int.cast_add, Int.cast_one]
  exact LatticeActualConformalEnergy.fused_eigenstate_energy lattice (actualInverse lattice)
    (actualInverse_left lattice gram_det_unit) (actualInverse_right lattice gram_det_unit)
    a.val v.val (e : ℂ) (g : ℂ) (sourceGrade_weight e a) (sourceGrade_weight g v) m

private def mixedIterateCoeff (s : Fin 3) (e : ℤ) (a : fixedGrade e)
    (h : ℤ) (u : sector s) (w : ℝ) (f : GradeDual w) (p q r d : ℤ) (j : ℕ) : fixedGrade d :=
  evaluation s (h + 9 * (e - (r + (j : ℤ)) - 1)) (w : ℂ)
    (((fixedField s (fixedGradeInclusion e a))[[r + (j : ℤ)]]) u) f
    (-p - q + 2 * e - 2 * r - 3 - (j : ℤ)) d

private def mixedOutputCoeff (s : Fin 3) (e : ℤ) (a : fixedGrade e)
    (h : ℤ) (u : sector s) (w : ℝ) (f : GradeDual w) (p q r d : ℤ) (j : ℕ) : fixedGrade d :=
  let m : ℤ := p + r - (j : ℤ)
  let g : ℤ := d - e + m + 1
  fixedProductOnGrade a (evaluation s h (w : ℂ) u f (-q - (j : ℤ) - 1) g) m (by
    dsimp only [g]
    omega)

private def mixedDualCoeff (s : Fin 3) (e : ℤ) (a : fixedGrade e)
    (h : ℤ) (u : sector s) (w : ℝ) (f : GradeDual w) (p q r d : ℤ) (j : ℕ) : fixedGrade d :=
  let m : ℤ := -(p + (j : ℤ)) - 1
  let w' := shiftedWeight w e.toNat (3 * m)
  let g := C (dualField a.val) (3 * m) (DirectSum.lof ℂ ℝ GradeDual w f)
  evaluation s h (w' : ℂ) u (g w') (-q - r + (j : ℤ) - 1) d

private theorem mixedIterateCoeff_finite (s : Fin 3) (e : ℤ) (a : fixedGrade e)
    (h : ℤ) (u : sector s) (hu : totalLZero u.val = ((h : ℂ) / 9) • u.val)
    (w : ℝ) (f : GradeDual w) (p q r d : ℤ) :
    Function.HasFiniteSupport (mixedIterateCoeff s e a h u w f p q r d) := by
  let N := ((h + 9 * (e - r - 1) - 16) / 9).toNat + 1
  apply (Finset.range N).finite_toSet.subset
  apply support_subset_range
  intro j hj
  apply (fixedGradeForm_nondegenerate d).1
  intro b
  rw [mixedIterateCoeff, evaluation_pairing]
  exact invertedCoeff_iterate_cutoff s (fixedGradeInclusion e a) u e h
    (sourceGrade_weight e a) hu r (w : ℂ) f ⟨b.val, b.property.1⟩ _ j hj

private theorem mixedOutputCoeff_finite (s : Fin 3) (e : ℤ) (a : fixedGrade e)
    (h : ℤ) (u : sector s) (w : ℝ) (f : GradeDual w) (p q r d : ℤ) :
    Function.HasFiniteSupport (mixedOutputCoeff s e a h u w f p q r d) := by
  let N := (d - e + p + r + 1).toNat + 1
  apply (Finset.range N).finite_toSet.subset
  apply support_subset_range
  intro j hj
  let m : ℤ := p + r - (j : ℤ)
  let g : ℤ := d - e + m + 1
  have hg : g < 0 := by
    dsimp only [N, g, m] at hj ⊢
    omega
  let v := evaluation s h (w : ℂ) u f (-q - (j : ℤ) - 1) g
  have hv := fixedGrade_eq_zero_of_lt hg v
  apply Subtype.ext
  change (sourceMode m (fixedGradeInclusion e a) (fixedGradeInclusion g v)).val = 0
  rw [hv, map_zero, map_zero, Submodule.coe_zero]

private theorem mixedDualCoeff_finite (s : Fin 3) (e : ℤ) (a : fixedGrade e)
    (h : ℤ) (u : sector s) (w : ℝ) (f : GradeDual w) (p q r d : ℤ) :
    Function.HasFiniteSupport (mixedDualCoeff s e a h u w f p q r d) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (w + (e.toNat : ℝ) - (p : ℝ) - 1 - 16 / 9)
  apply (Finset.range N).finite_toSet.subset
  apply support_subset_range
  intro j hj
  let m : ℤ := -(p + (j : ℤ)) - 1
  let w' := shiftedWeight w e.toNat (3 * m)
  have hBelow : w' < 16 / 9 := by
    have hj' : (N : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    dsimp only [w', shiftedWeight, m]
    push_cast
    linarith
  let f' : GradeDual w' := (C (dualField a.val) (3 * m) (DirectSum.lof ℂ ℝ GradeDual w f)) w'
  have hf' : f' = 0 := by
    apply LinearMap.ext
    intro x
    rw [actualGrade_eq_zero_of_lt hBelow x, map_zero, LinearMap.zero_apply]
  apply (fixedGradeForm_nondegenerate d).1
  intro b
  change fixedGradeForm d (evaluation s h (w' : ℂ) u f' (-q - r + (j : ℤ) - 1) d) b = 0
  rw [evaluation_pairing, hf']
  simp only [invertedCoeff, inversionTerm, LinearMap.zero_apply, Finset.sum_const_zero, mul_zero]

private theorem fixedGradeForm_finsum {d : ℤ} (b : fixedGrade d)
    (c : ℕ → ℂ) (v : ℕ → fixedGrade d) (hv : Function.HasFiniteSupport v) :
    (fixedGradeForm d).flip b (∑ᶠ j : ℕ, c j • v j) =
      ∑ᶠ j : ℕ, c j * (fixedGradeForm d).flip b (v j) := by
  calc
    _ = ∑ᶠ j : ℕ, (fixedGradeForm d).flip b (c j • v j) :=
      map_finsum ((fixedGradeForm d).flip b) (hv.subset (Function.support_smul_subset_right c v))
    _ = _ := by simp only [map_smul, smul_eq_mul]

/-- The homogeneous mixed Jacobi identity in the actual fixed source grade.
Each of the three coefficient families has finite support before binomial weighting. -/
theorem evaluation_mixedJacobi (s : Fin 3) (e : ℤ) (a : fixedGrade e)
    (h : ℤ) (u : sector s) (hu : totalLZero u.val = ((h : ℂ) / 9) • u.val)
    (w : ℝ) (f : GradeDual w) (p q r d : ℤ)
    (hw : (w : ℂ) = (h : ℂ) / 9 + (d : ℂ) + (p : ℂ) + (q : ℂ) -
      (e : ℂ) + (r : ℂ) + 2) :
    let iterate := mixedIterateCoeff s e a h u w f p q r d
    let output := mixedOutputCoeff s e a h u w f p q r d
    let dual := mixedDualCoeff s e a h u w f p q r d
    let weight (j : ℕ) := (-1 : ℂ) ^ j * integerBinomial r j
    Function.HasFiniteSupport iterate ∧ Function.HasFiniteSupport output ∧
      Function.HasFiniteSupport dual ∧
      (∑ᶠ j : ℕ, integerBinomial p j • iterate j) =
        (∑ᶠ j : ℕ, weight j • output j) - epsilon r • (∑ᶠ j : ℕ, weight j • dual j) := by
  intro iterate output dual weight
  have hi : Function.HasFiniteSupport iterate := mixedIterateCoeff_finite s e a h u hu w f p q r d
  have ho : Function.HasFiniteSupport output := mixedOutputCoeff_finite s e a h u w f p q r d
  have hd : Function.HasFiniteSupport dual := mixedDualCoeff_finite s e a h u w f p q r d
  refine ⟨hi, ho, hd, sub_eq_zero.mp ?_⟩
  apply (fixedGradeForm_nondegenerate d).1
  intro b
  change (fixedGradeForm d).flip b
    ((∑ᶠ j : ℕ, integerBinomial p j • iterate j) -
      ((∑ᶠ j : ℕ, weight j • output j) - epsilon r • (∑ᶠ j : ℕ, weight j • dual j))) = 0
  rw [map_sub, map_sub, map_smul, smul_eq_mul, fixedGradeForm_finsum b (integerBinomial p) iterate hi,
    fixedGradeForm_finsum b weight output ho, fixedGradeForm_finsum b weight dual hd]
  exact sub_eq_zero.mpr (evaluation_mixedJacobi_pairing s e a h u hu w f p q r d b hw)

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
#print axioms invertedCoeff_iterate_sum_pairing
#print axioms evaluation_iterate_sum_pairing
#print axioms evaluation_mixedJacobi_pairing
#print axioms evaluation_mixedJacobi
#print axioms evaluation_translation
#print axioms evaluation_ground_vacuum
#print axioms evaluation_ground_ne_zero

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeOppositeEvaluation
