/- GID: D5/S3/VertexAlgebra/TransverseMetric/RealAdaptedFrame
   generality: G
   mirror-B: none
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Real nonzero-charge adapted frames supply original native Lorentzian positivity. -/

import D5.S3.VertexAlgebra.TransverseMetric.LorentzianSignature
import D5.S3.QuadraticForms.HyperbolicFrame
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.TransverseMetric.RealAdaptedFrame

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
  LatticeSugawaraVirasoro
  LatticeOscillatorFockForm LatticeOscillatorFockMetric LatticeBcGhostBrstCharge
  BcGhostFockSupport OriginalQQuartetSource NativePositivity Module
open scoped BigOperators Matrix

noncomputable section

private theorem real_gram_inverses (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : H * gramComplex D = 1)
    (rightInverse : gramComplex D * H = 1) :
    (H.map Complex.re) * gramReal D = 1 ∧
      gramReal D * (H.map Complex.re) = 1 := by
  constructor
  · ext row column
    have equality := congrArg (fun matrix => (matrix row column).re) leftInverse
    simpa [Matrix.map_apply, Matrix.mul_apply, gramComplex, gramReal, Complex.mul_re,
      Matrix.one_apply, apply_ite] using equality
  · ext row column
    have equality := congrArg (fun matrix => (matrix row column).re) rightInverse
    simpa [Matrix.map_apply, Matrix.mul_apply, gramComplex, gramReal, Complex.mul_re,
      Matrix.one_apply, apply_ite] using equality

private theorem real_symmetric (D : LatticeData) :
    LinearMap.IsSymm (Matrix.toBilin' (gramReal D)) := by
  refine ⟨fun first second => ?_⟩
  simp only [Matrix.toBilin'_apply, gramReal, RingHom.id_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro firstIndex _
  apply Finset.sum_congr rfl
  intro secondIndex _
  rw [D.symmetric secondIndex firstIndex]
  ring

private theorem real_inertia (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : H * gramComplex D = 1)
    (rightInverse : gramComplex D * H = 1)
    (lorentzian : QuadraticForms.ActualSignature.signature (gramReal D).toQuadraticForm' =
      (D.rank : ℤ) - 2) :
    sigNeg (gramReal D).toQuadraticForm' = 1 ∧
      sigPos (gramReal D).toQuadraticForm' + 1 = D.rank := by
  let : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  have inverse := real_gram_inverses D H leftInverse rightInverse
  have nondegenerate : LinearMap.Nondegenerate (Matrix.toBilin' (gramReal D)) :=
    Matrix.nondegenerate_toBilin'_iff.mpr
      (Matrix.nondegenerate_of_det_ne_zero (Matrix.det_ne_zero_of_left_inverse inverse.1))
  have associated : QuadraticMap.associated (gramReal D).toQuadraticForm' =
      Matrix.toBilin' (gramReal D) :=
    QuadraticMap.associated_left_inverse ℝ (real_symmetric D).eq
  have radical : (gramReal D).toQuadraticForm'.radical = ⊥ :=
    (QuadraticMap.nondegenerate_associated_iff.mp (associated ▸ nondegenerate)).radical_eq_bot
  have count : sigPos (gramReal D).toQuadraticForm' +
      sigNeg (gramReal D).toQuadraticForm' = D.rank := by
    have total := QuadraticForm.sigPos_add_sigNeg_add_radical
      (Q := (gramReal D).toQuadraticForm')
    rw [radical] at total
    simpa only [finrank_bot, add_zero, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin] using total
  unfold QuadraticForms.ActualSignature.signature at lorentzian
  constructor <;> omega

private theorem real_null_separation {Space : Type} [AddCommGroup Space] [Module ℝ Space]
    [FiniteDimensional ℝ Space] (quadratic : QuadraticForm ℝ Space)
    (positive : 0 < sigPos quadratic)
    (negative : 0 < sigNeg quadratic)
    (functional : Space →ₗ[ℝ] ℝ) (functionalNonzero : functional ≠ 0) :
    ∃ direction : Space, quadratic direction = 0 ∧ functional direction ≠ 0 := by
  classical
  let : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  obtain ⟨weights, ⟨equivalence⟩⟩ := quadratic.equivalent_weightedSumSquares
  have equivalent : QuadraticMap.Equivalent quadratic
      (QuadraticMap.weightedSumSquares ℝ weights) := ⟨equivalence⟩
  let basis := (Pi.basisFun ℝ (Fin (finrank ℝ Space))).map equivalence.symm.toLinearEquiv
  obtain ⟨first, detected⟩ : ∃ index, functional (basis index) ≠ 0 := by
    by_contra missing
    push Not at missing
    apply functionalNonzero
    apply basis.ext
    intro index
    simpa using missing index
  have positiveWeights : 0 < {index | 0 < weights index}.ncard := by
    rwa [← QuadraticForm.sigPos_weightedSumSquares, ← equivalent.sigPos_eq]
  have negativeWeights : 0 < {index | weights index < 0}.ncard := by
    rwa [← QuadraticForm.sigNeg_weightedSumSquares, ← equivalent.sigNeg_eq]
  have square (index) : quadratic (basis index) = weights index := by
    simp only [basis, Basis.map_apply, Pi.basisFun_apply]
    change quadratic (equivalence.symm (Pi.single index 1)) = weights index
    rw [equivalence.symm.map_app]
    simp [QuadraticMap.weightedSumSquares_apply, Pi.single_apply, smul_eq_mul]
  by_cases firstZero : weights first = 0
  · exact ⟨basis first, (square first).trans firstZero, detected⟩
  obtain ⟨second, opposite⟩ : ∃ second, 0 < -weights first / weights second := by
    rcases lt_or_gt_of_ne firstZero with firstNegative | firstPositive
    · obtain ⟨second, secondPositive⟩ :=
        (Set.ncard_pos (Set.toFinite {index | 0 < weights index})).mp positiveWeights
      exact ⟨second, div_pos (neg_pos.mpr firstNegative) secondPositive⟩
    · obtain ⟨second, secondNegative⟩ :=
        (Set.ncard_pos (Set.toFinite {index | weights index < 0})).mp negativeWeights
      exact ⟨second, div_pos_of_neg_of_neg (neg_neg_of_pos firstPositive) secondNegative⟩
  have secondNonzero : weights second ≠ 0 := by
    intro vanished
    simp [vanished] at opposite
  have distinct : first ≠ second := by
    intro equality
    subst second
    rw [neg_div, div_self firstZero] at opposite
    norm_num at opposite
  let root := Real.sqrt (-weights first / weights second)
  have cancellation : root * root * weights second = -weights first := by
    rw [← pow_two, Real.sq_sqrt (le_of_lt opposite), div_mul_cancel₀ _ secondNonzero]
  have nullCombination (scalar : ℝ) :
      quadratic (basis first + scalar • basis second) =
        weights first + scalar * scalar * weights second := by
    have coordinates : basis first + scalar • basis second =
        equivalence.symm (Pi.single first 1 + scalar • Pi.single second 1) := by
      simp [basis, Basis.map_apply, Pi.basisFun_apply]
    rw [coordinates, equivalence.symm.map_app]
    simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul, Pi.add_apply,
      Pi.smul_apply]
    simp [Pi.single_apply, distinct, mul_add,
      Finset.sum_add_distrib, mul_comm, mul_left_comm]
  have plusNull : quadratic (basis first + root • basis second) = 0 := by
    rw [nullCombination, cancellation]
    ring
  have minusNull : quadratic (basis first + (-root) • basis second) = 0 := by
    rw [nullCombination]
    nlinarith [cancellation]
  by_cases plusDetected : functional (basis first + root • basis second) ≠ 0
  · exact ⟨_, plusNull, plusDetected⟩
  · refine ⟨_, minusNull, ?_⟩
    intro minusZero
    have plusZero := not_ne_iff.mp plusDetected
    simp only [map_add, map_smul, smul_eq_mul] at plusZero minusZero
    apply detected
    linarith

def embed (D : LatticeData) (vector : Fin D.rank → ℝ) : Fin D.rank → ℂ :=
  fun index => (vector index : ℂ)

private theorem pair_embed (D : LatticeData) (first second : Fin D.rank → ℝ) :
    gramPair D (embed D first) (embed D second) =
      (Matrix.toBilin' (gramReal D) first second : ℂ) := by
  classical
  simp only [gramPair, embed, Matrix.toBilin'_apply, gramReal,
    Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast]

private theorem original_real_null (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : H * gramComplex D = 1)
    (rightInverse : gramComplex D * H = 1)
    (rank : 2 ≤ D.rank) (beta : Charge D) (chargeNonzero : beta ≠ 0)
    (lorentzian : QuadraticForms.ActualSignature.signature (gramReal D).toQuadraticForm' =
      (D.rank : ℤ) - 2) :
    ∃ direction : Fin D.rank → ℝ,
      gramPair D (embed D direction) (embed D direction) = 0 ∧
        chosenP D beta (embed D direction) ≠ 0 := by
  classical
  let form := Matrix.toBilin' (gramReal D)
  let charge : Fin D.rank → ℝ := fun index => (beta index : ℝ)
  have chargeNonzeroReal : charge ≠ 0 := by
    intro vanished
    apply chargeNonzero
    funext index
    exact_mod_cast (show (beta index : ℝ) = 0 from congrFun vanished index)
  have nondegenerate : LinearMap.Nondegenerate form :=
    Matrix.nondegenerate_toBilin'_iff.mpr (Matrix.nondegenerate_of_det_ne_zero
      (Matrix.det_ne_zero_of_left_inverse (real_gram_inverses D H leftInverse rightInverse).1))
  have functionalNonzero : form.flip charge ≠ 0 := by
    intro vanished
    apply chargeNonzeroReal
    apply nondegenerate.2
    intro vector
    exact congrArg (fun linear : (Fin D.rank → ℝ) →ₗ[ℝ] ℝ => linear vector) vanished
  have inertia := real_inertia D H leftInverse rightInverse lorentzian
  obtain ⟨direction, null, detected⟩ := real_null_separation (gramReal D).toQuadraticForm'
    (by omega) (by omega) (form.flip charge) functionalNonzero
  refine ⟨direction, ?_, ?_⟩
  · rw [pair_embed]
    exact_mod_cast null
  · have embeddedCharge : complexCharge D beta = embed D charge := by
      ext index
      simp [complexCharge, embed, charge]
    unfold chosenP
    rw [embeddedCharge, pair_embed]
    exact_mod_cast detected

structure NativeFrame (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (beta : Charge D) where
  leftGramInverse : H * gramComplex D = 1
  rightGramInverse : gramComplex D * H = 1
  direction : Fin D.rank → ℝ
  rows : Matrix (Fin D.rank) (Fin D.rank) ℝ
  inverseRows : Matrix (Fin D.rank) (Fin D.rank) ℝ
  xAxis : Fin D.rank
  yAxis : Fin D.rank
  leftRealInverse : inverseRows * rows = 1
  rightRealInverse : rows * inverseRows = 1
  leftComplexInverse : inverseRows.map Complex.ofReal * rows.map Complex.ofReal = 1
  rightComplexInverse : rows.map Complex.ofReal * inverseRows.map Complex.ofReal = 1
  distinct : xAxis ≠ yAxis
  starFixed : ∀ row column, star (rows.map Complex.ofReal row column) =
    rows.map Complex.ofReal row column
  null : gramPair D (embed D direction) (embed D direction) = 0
  chosenNonzero : chosenP D beta (embed D direction) ≠ 0
  xRow : rows xAxis = direction
  yRow : embed D (rows yAxis) = adaptedPartner D beta (embed D direction)
  xRealDual : ∀ row, Matrix.toBilin' (gramReal D) (rows yAxis) (rows row) =
    if row = xAxis then 1 else 0
  yRealDual : ∀ row, Matrix.toBilin' (gramReal D) (rows xAxis) (rows row) =
    if row = yAxis then 1 else 0
  xComplexDual : ∀ row, gramPair D (rows.map Complex.ofReal yAxis)
    (rows.map Complex.ofReal row) = if row = xAxis then 1 else 0
  yComplexDual : ∀ row, gramPair D (rows.map Complex.ofReal xAxis)
    (rows.map Complex.ofReal row) = if row = yAxis then 1 else 0
  partnerPaired : gramPair D (adaptedPartner D beta (embed D direction))
    (embed D direction) = 1
  partnerNull : gramPair D (adaptedPartner D beta (embed D direction))
    (adaptedPartner D beta (embed D direction)) = 0
  chargeDecomposition : complexCharge D beta =
    chosenP D beta (embed D direction) • adaptedPartner D beta (embed D direction) +
      chosenQ D beta (embed D direction) • embed D direction
  originalMassShell : chosenH D beta = chargeQuadratic D H beta
  transversePositive : (transverseGram D (rows.map Complex.ofReal) xAxis yAxis).PosDef
  polynomialPositive : ∀ polynomial : MvPolynomial (TransverseAxis D xAxis yAxis × ℕ) ℂ,
    polynomial ≠ 0 →
    0 < (fockForm D (nativePolynomial D (rows.map Complex.ofReal) xAxis yAxis polynomial)
      (nativePolynomial D (rows.map Complex.ofReal) xAxis yAxis polynomial)).re ∧
    (fockForm D (nativePolynomial D (rows.map Complex.ofReal) xAxis yAxis polynomial)
      (nativePolynomial D (rows.map Complex.ofReal) xAxis yAxis polynomial)).im = 0
  nativePositive : ∀ (level : ℤ) (state : State D),
    state ∈ nativeTransverseEnergySpace D H (rows.map Complex.ofReal)
      (inverseRows.map Complex.ofReal) leftGramInverse rightGramInverse
      leftComplexInverse rightComplexInverse beta xAxis yAxis level →
    LatticeBcGhostBrstGhostNumber.J D state = state → state ≠ 0 →
    0 < (-LatticeBcGhostHermitianForm.F D state (C D 0 state)).re ∧
      (-LatticeBcGhostHermitianForm.F D state (C D 0 state)).im = 0

theorem exists_native_frame (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1)
    (rightGramInverse : gramComplex D * H = 1)
    (rank : 2 ≤ D.rank) (beta : Charge D) (chargeNonzero : beta ≠ 0)
    (lorentzian : QuadraticForms.ActualSignature.signature (gramReal D).toQuadraticForm' =
      (D.rank : ℤ) - 2) : Nonempty (NativeFrame D H beta) := by
  classical
  obtain ⟨direction, null, detected⟩ := original_real_null D H leftGramInverse
    rightGramInverse rank beta chargeNonzero lorentzian
  have realPair (first second : Fin D.rank → ℂ)
      (firstReal : ∀ index, star (first index) = first index)
      (secondReal : ∀ index, star (second index) = second index) :
      star (gramPair D first second) = gramPair D first second := by
    simp only [gramPair, star_sum, star_mul, firstReal, secondReal, star_intCast]
    apply Finset.sum_congr rfl
    intro firstIndex _
    apply Finset.sum_congr rfl
    intro secondIndex _
    ring
  have directionReal (index) : star (embed D direction index) = embed D direction index := by
    simp [embed]
  have chargeReal (index) : star (complexCharge D beta index) = complexCharge D beta index := by
    simp [complexCharge]
  have pReal : star (chosenP D beta (embed D direction)) =
      chosenP D beta (embed D direction) := realPair _ _ directionReal chargeReal
  have hReal : star (chosenH D beta) = chosenH D beta := by
    simp only [chosenH, star_mul, star_inv₀, star_ofNat, realPair _ _ chargeReal chargeReal]
    ring
  have partnerReal (index) : star (adaptedPartner D beta (embed D direction) index) =
      adaptedPartner D beta (embed D direction) index := by
    simp only [adaptedPartner, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, star_sub,
      star_mul, star_inv₀, star_pow, pReal, hReal, chargeReal, directionReal]
    ring
  let partner : Fin D.rank → ℝ := fun index =>
    (adaptedPartner D beta (embed D direction) index).re
  have partnerEmbed : embed D partner = adaptedPartner D beta (embed D direction) := by
    ext index
    exact Complex.conj_eq_iff_re.mp (partnerReal index)
  have relations := adaptedPartner_relations D beta (embed D direction) null detected
  have directionNull : Matrix.toBilin' (gramReal D) direction direction = 0 := by
    apply Complex.ofReal_injective
    simpa only [← pair_embed, Complex.ofReal_zero] using null
  have partnerNull : Matrix.toBilin' (gramReal D) partner partner = 0 := by
    apply Complex.ofReal_injective
    simpa only [← pair_embed, partnerEmbed, Complex.ofReal_zero] using relations.2.1
  have paired : Matrix.toBilin' (gramReal D) partner direction = 1 := by
    apply Complex.ofReal_injective
    simpa only [← pair_embed, partnerEmbed, Complex.ofReal_one] using relations.1
  obtain ⟨rows, inverseRows, xAxis, yAxis, leftReal, rightReal, distinct,
      xRow, yRow, xDual, yDual⟩ :=
    QuadraticForms.HyperbolicFrame.exists_frame_with_literal_duals
      (Matrix.toBilin' (gramReal D)) (real_symmetric D) direction partner
      directionNull partnerNull paired
  have leftComplex : inverseRows.map Complex.ofReal * rows.map Complex.ofReal = 1 := by
    ext row column
    have equation := congrArg (fun matrix => (matrix row column : ℂ)) leftReal
    simpa [Matrix.mul_apply, Matrix.map_apply, Complex.ofReal_sum,
      Complex.ofReal_mul, Matrix.one_apply, apply_ite] using equation
  have rightComplex : rows.map Complex.ofReal * inverseRows.map Complex.ofReal = 1 := by
    ext row column
    have equation := congrArg (fun matrix => (matrix row column : ℂ)) rightReal
    simpa [Matrix.mul_apply, Matrix.map_apply, Complex.ofReal_sum,
      Complex.ofReal_mul, Matrix.one_apply, apply_ite] using equation
  have realRows (row column) : star (rows.map Complex.ofReal row column) =
      rows.map Complex.ofReal row column := by simp
  have xComplexDual (row) : gramPair D (rows.map Complex.ofReal yAxis)
      (rows.map Complex.ofReal row) = if row = xAxis then 1 else 0 := by
    change gramPair D (embed D (rows yAxis)) (embed D (rows row)) = _
    rw [pair_embed, xDual]
    split_ifs <;> simp
  have yComplexDual (row) : gramPair D (rows.map Complex.ofReal xAxis)
      (rows.map Complex.ofReal row) = if row = yAxis then 1 else 0 := by
    change gramPair D (embed D (rows xAxis)) (embed D (rows row)) = _
    rw [pair_embed, yDual]
    split_ifs <;> simp
  refine ⟨{
    leftGramInverse := leftGramInverse
    rightGramInverse := rightGramInverse
    direction := direction
    rows := rows
    inverseRows := inverseRows
    xAxis := xAxis
    yAxis := yAxis
    leftRealInverse := leftReal
    rightRealInverse := rightReal
    leftComplexInverse := leftComplex
    rightComplexInverse := rightComplex
    distinct := distinct
    starFixed := realRows
    null := null
    chosenNonzero := detected
    xRow := xRow
    yRow := (congrArg (embed D) yRow).trans partnerEmbed
    xRealDual := xDual
    yRealDual := yDual
    xComplexDual := xComplexDual
    yComplexDual := yComplexDual
    partnerPaired := relations.1
    partnerNull := relations.2.1
    chargeDecomposition := relations.2.2
    originalMassShell := chosenH_original_chargeQuadratic D H leftGramInverse rightGramInverse beta
    transversePositive := LorentzianSignature.transverseGram_posDef D _ _ leftComplex rightComplex
      xAxis yAxis distinct realRows xComplexDual yComplexDual lorentzian
    polynomialPositive := ?_
    nativePositive := ?_
  }⟩
  · exact LorentzianSignature.nativePolynomial_positive_of_lorentzian D _ _
      leftComplex rightComplex xAxis yAxis distinct realRows xComplexDual yComplexDual lorentzian
  · intro level state member degreeOne nonzero
    exact LorentzianSignature.native_degree_one_negative_C0_positive_of_lorentzian D H _ _
      leftGramInverse rightGramInverse leftComplex rightComplex beta xAxis yAxis distinct level
      realRows xComplexDual yComplexDual lorentzian state member degreeOne nonzero

#print axioms exists_native_frame

end
end D5.S3.VertexAlgebra.TransverseMetric.RealAdaptedFrame
