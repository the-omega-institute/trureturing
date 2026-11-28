/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/NativeFusion/P48qOppositeVertexLaws
   generality: I
   mirror-B: none(waiver:no-B-plane-mirror-for-source-module)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Mixed Jacobi and translation of the actual native BPZ opposite vertex series. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.NativeFusion.P48qOppositeVertex

/-! The fixed, twisted and restricted-dual fields give the three mixed
Jacobi families of the rational opposite vertex operator. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.NativeFusion

open scoped BigOperators DirectSum VertexOperator
open HalfFockSpectralFiberSource (actualInverse actualInverse_left actualInverse_right)
open LatticePositiveEnergy (actualL0_eigen_iff_grade gradeProjection gradeProjection_mem
  stateEnergies sum_gradeProjections)
open LatticeSugawaraCurrents (sugawaraMode)
open P48qFixedSourceBPZ (fixedGrade)
open P48qNativeConformalSector (fixedStates sector fixedField fixedOmega fixedProduct)
open P48qNativeDualLinearField (dualField dualField_homogeneous)
open P48qNativeFixedRightInsertion (sectorTranslation)
open P48qNativeOppositeEvaluation (evaluation evaluation_mixedJacobi evaluation_translation)
open P48qNativeOppositeGrade (fixedMode_weight)
open P48qNativeOppositeVacuum (exponent)
open P48qNativeRestrictedDualField (GradeDual RestrictedDual shiftedWeight coeff_lof
  oppositeField_coeff)
open P48qTwistedChargeAction (lattice)
open P48qTwistedStateEnergy (totalLZero)
open StateFieldResidueReconstruction (epsilon integerBinomial)
open private fixedGradeInclusion fixedGrade_eq_zero_of_lt sourceGrade_weight fixedProduct_zero_left
  mixedIterateCoeff mixedOutputCoeff mixedDualCoeff from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeOppositeEvaluation
open private conformalMode_weight from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeOppositeVacuum
open private sourceMode sectorMode from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeFixedRightJacobi
open private gram_det_unit from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qConformalVectorDecomposition
open private fixedProjection fixedProjection_eq_self fixedProjection_fixed lift_fixed
  mem_fixedStates_iff sourceLZero_fixedProjection from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeConformalSector

noncomputable section

local notation "C" => HVertexOperator.coeff

private def actualIterateCoeff (s : Fin 3) (e : ℤ) (a : fixedGrade e)
    (u : sector s) (w : ℝ) (f : GradeDual w) (p r : ℤ) (Q : ℚ) (j : ℕ) : fixedStates :=
  C (oppositeVertex s (((fixedField s (fixedGradeInclusion e a))[[r + (j : ℤ)]]) u))
    (-(p : ℚ) - Q - 1 + (j : ℚ)) (DirectSum.lof ℂ ℝ GradeDual w f)

private def actualOutputCoeff (s : Fin 3) (e : ℤ) (a : fixedGrade e)
    (u : sector s) (w : ℝ) (f : GradeDual w) (p r : ℤ) (Q : ℚ) (j : ℕ) : fixedStates :=
  fixedProduct (fixedGradeInclusion e a)
    (C (oppositeVertex s u) (-(Q : ℚ) - (j : ℚ) - 1)
      (DirectSum.lof ℂ ℝ GradeDual w f)) (p + r - (j : ℤ))

private def actualDualCoeff (s : Fin 3) (e : ℤ) (a : fixedGrade e)
    (u : sector s) (w : ℝ) (f : GradeDual w) (p r : ℤ) (Q : ℚ) (j : ℕ) : fixedStates :=
  C (oppositeVertex s u) (-(Q : ℚ) - (r : ℚ) + (j : ℚ) - 1)
    (C (dualField a.val) (3 * (-(p + (j : ℤ)) - 1))
      (DirectSum.lof ℂ ℝ GradeDual w f))

set_option maxHeartbeats 2000000 in
-- Match the dependent evaluation grade after the fixed-field iterate.
private theorem homogeneous_iterate_coeff_eq (s : Fin 3) (e : ℤ) (a : fixedGrade e)
    (h : ℤ) (u : sector s) (hu : totalLZero u.val = ((h : ℂ) / 9) • u.val)
    (w : ℝ) (f : GradeDual w) (p q r d : ℤ) (Q : ℚ)
    (hQ : Q = (q : ℚ) + 2 * (h : ℚ) / 9)
    (hw : (w : ℂ) = (h : ℂ) / 9 + (d : ℂ) + (p : ℂ) + (q : ℂ) -
      (e : ℂ) + (r : ℂ) + 2) (j : ℕ) :
    actualIterateCoeff s e a u w f p r Q j =
      fixedGradeInclusion d (mixedIterateCoeff s e a h u w f p q r d j) := by
  let H : ℤ := h + 9 * (e - (r + (j : ℤ)) - 1)
  let k : ℤ := -p - q + 2 * e - 2 * r - 3 - (j : ℤ)
  let v := ((fixedField s (fixedGradeInclusion e a))[[r + (j : ℤ)]]) u
  have hu' : totalLZero v.val = ((H : ℂ) / 9) • v.val :=
    fixedMode_weight s (fixedGradeInclusion e a) u e h (sourceGrade_weight e a) hu _
  have hw' : (w : ℂ) = (H : ℂ) / 9 + (d : ℂ) - (k : ℂ) := by
    dsimp only [H, k]
    push_cast
    linear_combination hw
  have hx : (-(p : ℚ) - Q - 1 + (j : ℚ)) = exponent H k := by
    dsimp only [exponent, H, k]
    rw [hQ]
    push_cast
    ring
  change C (oppositeVertex s v) _ _ = fixedGradeInclusion d (evaluation s H (w : ℂ) v f k d)
  rw [hx]
  exact oppositeVertex_coeff_of_grade s H v hu' w f k d hw'

set_option maxHeartbeats 2000000 in
-- Match the coefficient through two fixed-grade inclusions.
private theorem homogeneous_output_coeff_eq (s : Fin 3) (e : ℤ) (a : fixedGrade e)
    (h : ℤ) (u : sector s) (hu : totalLZero u.val = ((h : ℂ) / 9) • u.val)
    (w : ℝ) (f : GradeDual w) (p q r d : ℤ) (Q : ℚ)
    (hQ : Q = (q : ℚ) + 2 * (h : ℚ) / 9)
    (hw : (w : ℂ) = (h : ℂ) / 9 + (d : ℂ) + (p : ℂ) + (q : ℂ) -
      (e : ℂ) + (r : ℂ) + 2) (j : ℕ) :
    actualOutputCoeff s e a u w f p r Q j =
      fixedGradeInclusion d (mixedOutputCoeff s e a h u w f p q r d j) := by
  let m : ℤ := p + r - (j : ℤ)
  let g : ℤ := d - e + m + 1
  have hw' : (w : ℂ) = (h : ℂ) / 9 + (g : ℂ) -
      ((-q - (j : ℤ) - 1 : ℤ) : ℂ) := by
    dsimp only [g, m]
    push_cast
    linear_combination hw
  have hx : (-(Q : ℚ) - (j : ℚ) - 1) = exponent h (-q - (j : ℤ) - 1) := by
    dsimp only [exponent]
    rw [hQ]
    push_cast
    ring
  have hc := oppositeVertex_coeff_of_grade s h u hu w f (-q - (j : ℤ) - 1) g hw'
  rw [actualOutputCoeff, hx, hc]
  change fixedProduct (fixedGradeInclusion e a)
      (fixedGradeInclusion g (evaluation s h (w : ℂ) u f (-q - (j : ℤ) - 1) g)) m = _
  rfl

private theorem dual_coeff_lof (e : ℤ) (a : fixedGrade e) (he : 0 ≤ e) (w : ℝ) (f : GradeDual w)
    (k : ℤ) :
    let w' := shiftedWeight w e.toNat k
    let g := C (dualField a.val) k (DirectSum.lof ℂ ℝ GradeDual w f)
    g = DirectSum.lof ℂ ℝ GradeDual w' (g w') := by
  dsimp only
  have heCast : (e.toNat : ℂ) = (e : ℂ) := by
    exact_mod_cast Int.toNat_of_nonneg he
  have ha : sugawaraMode lattice (actualInverse lattice) 0 a.val = (e.toNat : ℂ) • a.val := by
    rw [heCast]
    exact sourceGrade_weight e a
  rw [dualField_homogeneous a.val e.toNat ha, oppositeField_coeff, coeff_lof,
    DirectSum.lof_apply]

set_option maxHeartbeats 2000000 in
-- Recover the coefficient after transport along the shifted dual grade.
private theorem homogeneous_dual_coeff_eq (s : Fin 3) (e : ℤ) (a : fixedGrade e)
    (h : ℤ) (u : sector s) (hu : totalLZero u.val = ((h : ℂ) / 9) • u.val)
    (w : ℝ) (f : GradeDual w) (p q r d : ℤ) (Q : ℚ) (he : 0 ≤ e)
    (hQ : Q = (q : ℚ) + 2 * (h : ℚ) / 9)
    (hw : (w : ℂ) = (h : ℂ) / 9 + (d : ℂ) + (p : ℂ) + (q : ℂ) -
      (e : ℂ) + (r : ℂ) + 2) (j : ℕ) :
    actualDualCoeff s e a u w f p r Q j =
      fixedGradeInclusion d (mixedDualCoeff s e a h u w f p q r d j) := by
  let m : ℤ := -(p + (j : ℤ)) - 1
  let w' := shiftedWeight w e.toNat (3 * m)
  let g := C (dualField a.val) (3 * m) (DirectSum.lof ℂ ℝ GradeDual w f) w'
  have heCast : (e.toNat : ℂ) = (e : ℂ) := by
    exact_mod_cast Int.toNat_of_nonneg he
  have hg : C (dualField a.val) (3 * m) (DirectSum.lof ℂ ℝ GradeDual w f) =
      DirectSum.lof ℂ ℝ GradeDual w' g := dual_coeff_lof e a he w f (3 * m)
  have hw' : (w' : ℂ) = (h : ℂ) / 9 + (d : ℂ) -
      ((-q - r + (j : ℤ) - 1 : ℤ) : ℂ) := by
    simp only [w', shiftedWeight, m, Complex.ofReal_add, Complex.ofReal_div,
      Complex.ofReal_natCast, Complex.ofReal_intCast, Complex.ofReal_ofNat]
    push_cast
    rw [heCast]
    linear_combination hw
  have hx : (-(Q : ℚ) - (r : ℚ) + (j : ℚ) - 1) =
      exponent h (-q - r + (j : ℤ) - 1) := by
    dsimp only [exponent]
    rw [hQ]
    push_cast
    ring
  have hc := oppositeVertex_coeff_of_grade s h u hu w' g
    (-q - r + (j : ℤ) - 1) d hw'
  rw [actualDualCoeff, hx, hg, hc]
  rfl

private theorem map_weighted_finsum {d : ℤ} (c : ℕ → ℂ) (v : ℕ → fixedGrade d)
    (hv : Function.HasFiniteSupport v) :
    fixedGradeInclusion d (∑ᶠ j : ℕ, c j • v j) =
      ∑ᶠ j : ℕ, c j • fixedGradeInclusion d (v j) := by
  calc
    _ = ∑ᶠ j : ℕ, fixedGradeInclusion d (c j • v j) :=
      map_finsum (fixedGradeInclusion d) (hv.subset (Function.support_smul_subset_right c v))
    _ = _ := by simp only [map_smul]

set_option maxHeartbeats 2000000 in
-- Transport all three finite sums to the fixed source carrier.
/-- The three actual opposite-vertex coefficient families satisfy mixed Jacobi
in the physical coordinate and have finite support before binomial weighting.
The output product uses the fixed source mode and the dual input uses the
coefficient at three times its physical exponent on the cubic cover. -/
theorem oppositeVertex_mixedJacobi (s : Fin 3) (e : ℤ) (a : fixedGrade e)
    (h : ℤ) (u : sector s) (hu : totalLZero u.val = ((h : ℂ) / 9) • u.val)
    (w : ℝ) (f : GradeDual w) (p q r d : ℤ) (Q : ℚ)
    (hQ : Q = (q : ℚ) + 2 * (h : ℚ) / 9)
    (hw : (w : ℂ) = (h : ℂ) / 9 + (d : ℂ) + (p : ℂ) + (q : ℂ) -
      (e : ℂ) + (r : ℂ) + 2) :
    let A := fixedGradeInclusion e a
    let F := DirectSum.lof ℂ ℝ GradeDual w f
    let iterate (j : ℕ) :=
      C (oppositeVertex s (((fixedField s A)[[r + (j : ℤ)]]) u)) (-(p : ℚ) - Q - 1 + j) F
    let output (j : ℕ) :=
      fixedProduct A (C (oppositeVertex s u) (-Q - j - 1) F) (p + r - (j : ℤ))
    let dual (j : ℕ) :=
      C (oppositeVertex s u) (-Q - (r : ℚ) + j - 1)
        (C (dualField a.val) (3 * (-(p + (j : ℤ)) - 1)) F)
    let weight (j : ℕ) := (-1 : ℂ) ^ j * integerBinomial r j
    Function.HasFiniteSupport iterate ∧ Function.HasFiniteSupport output ∧
      Function.HasFiniteSupport dual ∧
      (∑ᶠ j : ℕ, integerBinomial p j • iterate j) =
        (∑ᶠ j : ℕ, weight j • output j) - epsilon r • (∑ᶠ j : ℕ, weight j • dual j) := by
  intro A F iterate output dual weight
  by_cases he : 0 ≤ e
  · obtain ⟨hi, ho, hd, hJacobi⟩ := evaluation_mixedJacobi s e a h u hu w f p q r d hw
    have hI (j : ℕ) : iterate j =
        fixedGradeInclusion d (mixedIterateCoeff s e a h u w f p q r d j) :=
      homogeneous_iterate_coeff_eq s e a h u hu w f p q r d Q hQ hw j
    have hO (j : ℕ) : output j =
        fixedGradeInclusion d (mixedOutputCoeff s e a h u w f p q r d j) :=
      homogeneous_output_coeff_eq s e a h u hu w f p q r d Q hQ hw j
    have hD (j : ℕ) : dual j =
        fixedGradeInclusion d (mixedDualCoeff s e a h u w f p q r d j) :=
      homogeneous_dual_coeff_eq s e a h u hu w f p q r d Q he hQ hw j
    rw [funext hI, funext hO, funext hD]
    refine ⟨hi.fun_comp (map_zero _), ho.fun_comp (map_zero _), hd.fun_comp (map_zero _), ?_⟩
    rw [← map_weighted_finsum _ _ hi, ← map_weighted_finsum _ _ ho,
      ← map_weighted_finsum _ _ hd, ← map_smul, ← map_sub]
    exact congrArg (fixedGradeInclusion d) hJacobi
  · have ha := fixedGrade_eq_zero_of_lt (lt_of_not_ge he) a
    have hA : A = 0 := by rw [show A = fixedGradeInclusion e a from rfl, ha, map_zero]
    have hI : iterate = 0 := by
      funext j
      dsimp only [iterate]
      simp only [hA, VertexOperator.ncoeff_apply, map_zero, Pi.zero_apply, LinearMap.zero_apply]
    have hO : output = 0 := by
      funext j
      dsimp only [output]
      rw [hA, fixedProduct_zero_left]
      rfl
    have hD : dual = 0 := by
      funext j
      dsimp only [dual]
      simp only [ha, Submodule.coe_zero, map_zero, Pi.zero_apply, LinearMap.zero_apply]
    simp [hI, hO, hD, Function.HasFiniteSupport]

set_option maxHeartbeats 2000000 in
-- Recover the candidate integer mode and output grade in all three channels.
/-- Without a matching integer mode and output grade, all three actual
coefficient families vanish pointwise at the given rational mode. -/
theorem oppositeVertex_mixedJacobi_off_grade (s : Fin 3) (e : ℤ) (a : fixedGrade e)
    (h : ℤ) (u : sector s) (hu : totalLZero u.val = ((h : ℂ) / 9) • u.val)
    (w : ℝ) (f : GradeDual w) (p r : ℤ) (Q : ℚ)
    (hoff : ¬ ∃ q d : ℤ, Q = (q : ℚ) + 2 * (h : ℚ) / 9 ∧
      (w : ℂ) = (h : ℂ) / 9 + (d : ℂ) + (p : ℂ) + (q : ℂ) -
        (e : ℂ) + (r : ℂ) + 2) (j : ℕ) :
    let A := fixedGradeInclusion e a
    let F := DirectSum.lof ℂ ℝ GradeDual w f
    C (oppositeVertex s (((fixedField s A)[[r + (j : ℤ)]]) u)) (-(p : ℚ) - Q - 1 + j) F = 0 ∧
      fixedProduct A (C (oppositeVertex s u) (-Q - j - 1) F) (p + r - (j : ℤ)) = 0 ∧
      C (oppositeVertex s u) (-Q - (r : ℚ) + j - 1)
        (C (dualField a.val) (3 * (-(p + (j : ℤ)) - 1)) F) = 0 := by
  intro A F
  refine ⟨?_, ?_, ?_⟩
  · let H : ℤ := h + 9 * (e - (r + (j : ℤ)) - 1)
    let v := ((fixedField s A)[[r + (j : ℤ)]]) u
    have hv : totalLZero v.val = ((H : ℂ) / 9) • v.val :=
      fixedMode_weight s A u e h (sourceGrade_weight e a) hu _
    apply oppositeVertex_coeff_eq_zero_of_no_grade s H v hv w f
    rintro ⟨k, d, hx, hw⟩
    refine hoff ⟨-p - k + 2 * e - 2 * r - 3 - (j : ℤ), d, ?_, ?_⟩
    · dsimp only [exponent, H] at hx
      push_cast at hx ⊢
      linear_combination hx
    · dsimp only [H] at hw
      push_cast at hw ⊢
      linear_combination hw
  · have hz : C (oppositeVertex s u) (-Q - j - 1) F = 0 := by
      apply oppositeVertex_coeff_eq_zero_of_no_grade s h u hu w f
      rintro ⟨k, g, hx, hw⟩
      refine hoff ⟨-k - (j : ℤ) - 1, e + g - (p + r - (j : ℤ)) - 1, ?_, ?_⟩
      · dsimp only [exponent] at hx
        push_cast at hx ⊢
        linear_combination hx
      · push_cast
        linear_combination hw
    rw [hz]
    exact map_zero (sourceMode (p + r - (j : ℤ)) A)
  · by_cases he : 0 ≤ e
    · let kDual : ℤ := 3 * (-(p + (j : ℤ)) - 1)
      rw [dual_coeff_lof e a he w f kDual]
      apply oppositeVertex_coeff_eq_zero_of_no_grade s h u hu
      rintro ⟨k, d, hx, hw⟩
      refine hoff ⟨-k - r + (j : ℤ) - 1, d, ?_, ?_⟩
      · dsimp only [exponent] at hx
        push_cast at hx ⊢
        linear_combination hx
      · have heCast : (e.toNat : ℂ) = (e : ℂ) := by
          exact_mod_cast Int.toNat_of_nonneg he
        simp only [shiftedWeight, kDual, Complex.ofReal_add, Complex.ofReal_div,
          Complex.ofReal_natCast, Complex.ofReal_intCast, Complex.ofReal_ofNat, heCast] at hw
        push_cast at hw ⊢
        linear_combination hw
    · rw [fixedGrade_eq_zero_of_lt (lt_of_not_ge he) a]
      simp only [Submodule.coe_zero, map_zero, Pi.zero_apply, LinearMap.zero_apply]

private abbrev MixedCoefficientFamilies :=
  (ℕ → fixedStates) × (ℕ → fixedStates) × (ℕ → fixedStates)

private def mixedCoefficients (s : Fin 3) (p r : ℤ) (Q : ℚ) :
    fixedStates →ₗ[ℂ] sector s →ₗ[ℂ] RestrictedDual →ₗ[ℂ] MixedCoefficientFamilies := by
  let read (x : ℚ) : sector s →ₗ[ℂ] RestrictedDual →ₗ[ℂ] fixedStates :=
    ((LinearMap.proj x).comp C).comp (oppositeVertex s)
  let dualMode (k : ℤ) : fixedStates →ₗ[ℂ] Module.End ℂ RestrictedDual :=
    ((LinearMap.proj k).comp C).comp (dualField.comp fixedStates.subtype)
  let coeffs (a : fixedStates) (u : sector s) (f : RestrictedDual) : MixedCoefficientFamilies :=
    (fun j => read (-(p : ℚ) - Q - 1 + j) (sectorMode s (r + (j : ℤ)) a u) f,
     fun j => sourceMode (p + r - (j : ℤ)) a (read (-Q - j - 1) u f),
     fun j => read (-Q - (r : ℚ) + j - 1) u (dualMode (3 * (-(p + (j : ℤ)) - 1)) a f))
  let atSource (a : fixedStates) := LinearMap.mk₂ ℂ (coeffs a)
    (by intros; simp only [coeffs, map_add, LinearMap.add_apply]; rfl)
    (by intros; simp only [coeffs, map_smul, LinearMap.smul_apply]; rfl)
    (by intros; simp only [coeffs, map_add]; rfl)
    (by intros; simp only [coeffs, map_smul]; rfl)
  refine { toFun := atSource, map_add' := ?_, map_smul' := ?_ }
  · intro a b
    apply LinearMap.ext fun u => LinearMap.ext fun f => ?_
    change coeffs (a + b) u f = coeffs a u f + coeffs b u f
    simp only [coeffs, map_add, LinearMap.add_apply]
    rfl
  · intro z a
    apply LinearMap.ext fun u => LinearMap.ext fun f => ?_
    change coeffs (z • a) u f = z • coeffs a u f
    simp only [coeffs, map_smul, LinearMap.smul_apply]
    rfl

private def weightedSum (c : ℕ → ℂ) (v : ℕ → fixedStates) : fixedStates :=
  ∑ᶠ j, c j • v j

private theorem weightedSupport (c : ℕ → ℂ) {v : ℕ → fixedStates}
    (hv : Function.HasFiniteSupport v) : Function.HasFiniteSupport (fun j => c j • v j) :=
  hv.subset (Function.support_smul_subset_right c v)

private theorem weightedSum_add (c : ℕ → ℂ) {v w : ℕ → fixedStates}
    (hv : Function.HasFiniteSupport v) (hw : Function.HasFiniteSupport w) :
    weightedSum c (v + w) = weightedSum c v + weightedSum c w := by
  simpa only [weightedSum, Pi.add_apply, smul_add] using
    finsum_add_distrib (weightedSupport c hv) (weightedSupport c hw)

private theorem weightedSum_smul (c : ℕ → ℂ) (z : ℂ) {v : ℕ → fixedStates}
    (hv : Function.HasFiniteSupport v) : weightedSum c (z • v) = z • weightedSum c v := by
  simpa only [weightedSum, Pi.smul_apply, smul_comm _ z] using
    (smul_finsum' z (weightedSupport c hv)).symm

private def mixedJacobiSubmodule (p r : ℤ) : Submodule ℂ MixedCoefficientFamilies := by
  let weight (j : ℕ) := (-1 : ℂ) ^ j * integerBinomial r j
  refine {
    carrier := {v | Function.HasFiniteSupport v.1 ∧ Function.HasFiniteSupport v.2.1 ∧
      Function.HasFiniteSupport v.2.2 ∧
        weightedSum (integerBinomial p) v.1 =
          weightedSum weight v.2.1 - epsilon r • weightedSum weight v.2.2}
    zero_mem' := by simp [weightedSum, Function.HasFiniteSupport]
    add_mem' := ?_
    smul_mem' := ?_ }
  · rintro a b ⟨ai, ao, ad, ha⟩ ⟨bi, bo, bd, hb⟩
    refine ⟨ai.add bi, ao.add bo, ad.add bd, ?_⟩
    change weightedSum (integerBinomial p) (a.1 + b.1) =
      weightedSum weight (a.2.1 + b.2.1) - epsilon r • weightedSum weight (a.2.2 + b.2.2)
    rw [weightedSum_add _ ai bi, weightedSum_add _ ao bo, weightedSum_add _ ad bd, ha, hb, smul_add]
    abel
  · rintro z a ⟨ai, ao, ad, ha⟩
    refine ⟨weightedSupport (fun _ => z) ai, weightedSupport (fun _ => z) ao,
      weightedSupport (fun _ => z) ad, ?_⟩
    change weightedSum (integerBinomial p) (z • a.1) =
      weightedSum weight (z • a.2.1) - epsilon r • weightedSum weight (z • a.2.2)
    rw [weightedSum_smul _ z ai, weightedSum_smul _ z ao, weightedSum_smul _ z ad,
      ha, smul_sub, smul_comm z (epsilon r)]

private theorem fixedGrade_span :
    Submodule.span ℂ {a : fixedStates |
      ∃ (e : ℤ) (v : fixedGrade e), fixedGradeInclusion e v = a} = ⊤ := by
  classical
  apply top_unique
  intro a _
  let component (e : ℤ) : fixedGrade e := by
    let v := gradeProjection lattice e a.val
    have hv := (actualL0_eigen_iff_grade lattice (actualInverse lattice)
      (actualInverse_left lattice gram_det_unit) (actualInverse_right lattice gram_det_unit)
      e v).mpr (gradeProjection_mem lattice e a.val)
    refine ⟨fixedProjection v, (mem_fixedStates_iff _).mpr (fixedProjection_fixed v), ?_⟩
    apply (actualL0_eigen_iff_grade lattice (actualInverse lattice)
      (actualInverse_left lattice gram_det_unit) (actualInverse_right lattice gram_det_unit) e _).mp
    rw [sourceLZero_fixedProjection, hv, map_smul]
  have hsum : (∑ e ∈ stateEnergies lattice a.val, fixedGradeInclusion e (component e)) = a := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum, component, fixedGradeInclusion, Submodule.coe_inclusion,
      map_sum, fixedProjection_eq_self _ (lift_fixed a)] using
      congrArg fixedProjection (sum_gradeProjections lattice a.val)
  rw [← hsum]
  exact Submodule.sum_mem _ fun e _ => Submodule.subset_span ⟨e, component e, rfl⟩

set_option maxHeartbeats 2000000 in
-- Match the concrete coefficient channels with the trilinear map during the span argument.
/-- The mixed coefficient Jacobi law of the actual BPZ opposite vertex operator on the
fixed source, twisted sector and restricted dual. All three families are finitely
supported before weighting, and the dual coefficient is read on the cubic cover. -/
theorem oppositeVertex_mixedJacobi_allStates (s : Fin 3) (a : fixedStates)
    (u : sector s) (f : RestrictedDual) (p r : ℤ) (Q : ℚ) :
    let iterate (j : ℕ) :=
      C (oppositeVertex s (((fixedField s a)[[r + (j : ℤ)]]) u)) (-(p : ℚ) - Q - 1 + j) f
    let output (j : ℕ) :=
      fixedProduct a (C (oppositeVertex s u) (-Q - j - 1) f) (p + r - (j : ℤ))
    let dual (j : ℕ) :=
      C (oppositeVertex s u) (-Q - (r : ℚ) + j - 1)
        (C (dualField a.val) (3 * (-(p + (j : ℤ)) - 1)) f)
    let weight (j : ℕ) := (-1 : ℂ) ^ j * integerBinomial r j
    Function.HasFiniteSupport iterate ∧ Function.HasFiniteSupport output ∧
      Function.HasFiniteSupport dual ∧
      (∑ᶠ j : ℕ, integerBinomial p j • iterate j) =
        (∑ᶠ j : ℕ, weight j • output j) - epsilon r • (∑ᶠ j : ℕ, weight j • dual j) := by
  classical
  let coeffs := mixedCoefficients s p r Q
  let law := mixedJacobiSubmodule p r
  change coeffs a u f ∈ law
  have sourceSpan : Submodule.span ℂ
      {A : fixedStates | ∃ (e : ℤ) (v : fixedGrade e), fixedGradeInclusion e v = A} ≤
        law.comap ((coeffs.flip u).flip f) := by
    apply Submodule.span_le.mpr
    rintro A ⟨e, v, rfl⟩
    have sectorSpan : Submodule.span ℂ
        {U : sector s | ∃ h : ℤ, totalLZero U.val = ((h : ℂ) / 9) • U.val} ≤
          law.comap ((coeffs (fixedGradeInclusion e v)).flip f) := by
      apply Submodule.span_le.mpr
      rintro U ⟨h, hU⟩
      change f ∈ law.comap (coeffs (fixedGradeInclusion e v) U)
      rw [← DirectSum.sum_support_of f]
      apply Submodule.sum_mem
      intro w _
      by_cases hm : ∃ q d : ℤ, Q = (q : ℚ) + 2 * (h : ℚ) / 9 ∧
          (w : ℂ) = (h : ℂ) / 9 + (d : ℂ) + (p : ℂ) + (q : ℂ) -
            (e : ℂ) + (r : ℂ) + 2
      · obtain ⟨q, d, hQ, hw⟩ := hm
        exact oppositeVertex_mixedJacobi s e v h U hU w (f w) p q r d Q hQ hw
      · have hz (j : ℕ) := oppositeVertex_mixedJacobi_off_grade s e v h U hU w (f w) p r Q hm j
        let hc := coeffs (fixedGradeInclusion e v) U (DirectSum.lof ℂ ℝ GradeDual w (f w))
        have hi : hc.1 = 0 := funext fun j => (hz j).1
        have ho : hc.2.1 = 0 := funext fun j => (hz j).2.1
        have hd : hc.2.2 = 0 := funext fun j => (hz j).2.2
        change hc ∈ law
        change Function.HasFiniteSupport hc.1 ∧ Function.HasFiniteSupport hc.2.1 ∧
          Function.HasFiniteSupport hc.2.2 ∧ _
        simp [hi, ho, hd, weightedSum, Function.HasFiniteSupport]
    rw [sector_homogeneous_span s] at sectorSpan
    exact sectorSpan (show u ∈ (⊤ : Submodule ℂ (sector s)) from Submodule.mem_top)
  rw [fixedGrade_span] at sourceSpan
  exact sourceSpan (show a ∈ (⊤ : Submodule ℂ fixedStates) from Submodule.mem_top)

set_option maxHeartbeats 2000000 in
-- Compare the dependent coefficient selections on both sides of translation.
private theorem oppositeVertex_translation_lof (s : Fin 3) (h : ℤ) (u : sector s)
    (hu : totalLZero u.val = ((h : ℂ) / 9) • u.val) (w : ℝ) (f : GradeDual w) (x : ℚ) :
    C (oppositeVertex s (sectorTranslation s u)) x (DirectSum.lof ℂ ℝ GradeDual w f) =
      ((x + 1 : ℚ) : ℂ) • C (oppositeVertex s u) (x + 1)
        (DirectSum.lof ℂ ℝ GradeDual w f) := by
  have hu' : totalLZero (sectorTranslation s u).val =
      (((h + 9 : ℤ) : ℂ) / 9) • (sectorTranslation s u).val := by
    have hWeight := conformalMode_weight s (-1) u ((h : ℂ) / 9) hu
    change totalLZero (sectorTranslation s u).val = _ • (sectorTranslation s u).val at hWeight
    convert hWeight using 2
    push_cast
    ring
  have hExponent (k : ℤ) : exponent (h + 9) k + 1 = exponent h (k - 1) := by
    simp only [exponent, Int.cast_add, Int.cast_sub, Int.cast_one, Int.cast_ofNat]
    ring
  by_cases hx : ∃ k d : ℤ, exponent (h + 9) k = x ∧
      (w : ℂ) = ((h + 9 : ℤ) : ℂ) / 9 + (d : ℂ) - (k : ℂ)
  · obtain ⟨k, d, rfl, hw⟩ := hx
    have hw' : (w : ℂ) = (h : ℂ) / 9 + (d : ℂ) - ((k - 1 : ℤ) : ℂ) := by
      push_cast at hw ⊢
      linear_combination hw
    rw [hExponent, oppositeVertex_coeff_of_grade s (h + 9) _ hu' w f k d hw,
      oppositeVertex_coeff_of_grade s h u hu w f (k - 1) d hw',
      evaluation_translation s h (w : ℂ) u hu f k d, map_smul]
    congr 1
    simp only [exponent, Rat.cast_sub, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_intCast]
  · have hx' : ¬ ∃ k d : ℤ, exponent h k = x + 1 ∧
        (w : ℂ) = (h : ℂ) / 9 + (d : ℂ) - (k : ℂ) := by
      rintro ⟨k, d, hk, hd⟩
      refine hx ⟨k + 1, d, ?_, ?_⟩
      · have h := hExponent (k + 1)
        rw [add_sub_cancel_right, hk] at h
        exact add_right_cancel h
      · push_cast
        linear_combination hd
    rw [oppositeVertex_coeff_eq_zero_of_no_grade s (h + 9) _ hu' w f x hx,
      oppositeVertex_coeff_eq_zero_of_no_grade s h u hu w f (x + 1) hx', smul_zero]

/-- Translation of the twisted input differentiates every rational coefficient
of the full opposite vertex operator. -/
theorem oppositeVertex_translation (s : Fin 3) (u : sector s) (x : ℚ) :
    C (oppositeVertex s (sectorTranslation s u)) x =
      ((x + 1 : ℚ) : ℂ) • C (oppositeVertex s u) (x + 1) := by
  let read (y : ℚ) : sector s →ₗ[ℂ] (RestrictedDual →ₗ[ℂ] fixedStates) :=
    ((LinearMap.proj y).comp C).comp (oppositeVertex s)
  let lhs := (read x).comp (sectorTranslation s)
  let rhs := ((x + 1 : ℚ) : ℂ) • read (x + 1)
  have hSpan : Submodule.span ℂ
      {v : sector s | ∃ h : ℤ, totalLZero v.val = ((h : ℂ) / 9) • v.val} ≤ lhs.eqLocus rhs := by
    apply Submodule.span_le.mpr
    rintro v ⟨h, hv⟩
    apply LinearMap.mem_eqLocus.mpr
    apply DirectSum.linearMap_ext
    intro w
    apply LinearMap.ext
    intro f
    exact oppositeVertex_translation_lof s h v hv w f x
  rw [sector_homogeneous_span s] at hSpan
  exact LinearMap.mem_eqLocus.mp (hSpan Submodule.mem_top)

#print axioms oppositeVertex_mixedJacobi
#print axioms oppositeVertex_mixedJacobi_off_grade
#print axioms oppositeVertex_mixedJacobi_allStates
#print axioms oppositeVertex_translation

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.NativeFusion
