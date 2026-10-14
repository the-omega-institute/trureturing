import D5.S3.VertexAlgebra.BrstNullSelectionTransient

namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open Module LatticeGeneratingFieldLocality LatticeSugawaraCurrents
open scoped BigOperators Matrix

noncomputable section

def originalLongitudinalPlane (D : LatticeData)
    (nullDirection longitudinal : Fin D.rank → ℂ) : Submodule ℂ (Fin D.rank → ℂ) :=
  Submodule.span ℂ (Set.range ![nullDirection, longitudinal])

def originalTransverse (D : LatticeData)
    (nullDirection longitudinal : Fin D.rank → ℂ) : Submodule ℂ (Fin D.rank → ℂ) :=
  (originalGramForm D).orthogonal (originalLongitudinalPlane D nullDirection longitudinal)

structure OriginalAdaptedFrameData (D : LatticeData) (charge : Charge D) where
  nullDirection : Fin D.rank → ℂ
  nullSelf : gramPair D nullDirection nullDirection = 0
  coefficientNonzero : chosenP D charge nullDirection ≠ 0
  frame : Matrix (Fin D.rank) (Fin D.rank) ℂ
  inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ
  xAxis : Fin D.rank
  yAxis : Fin D.rank
  axesDistinct : xAxis ≠ yAxis
  xRow : frame xAxis = nullDirection
  yRow : frame yAxis = adaptedPartner D charge nullDirection
  leftFrameInverse : inverse * frame = 1
  rightFrameInverse : frame * inverse = 1
  xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0
  yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0
  planeDimension : Module.finrank ℂ
    (originalLongitudinalPlane D nullDirection (adaptedPartner D charge nullDirection)) = 2
  transverseDimension : Module.finrank ℂ
    (originalTransverse D nullDirection (adaptedPartner D charge nullDirection)) = 24
  planeNondegenerate : ((originalGramForm D).restrict
    (originalLongitudinalPlane D nullDirection (adaptedPartner D charge nullDirection))).Nondegenerate
  planeTransverseComplement : IsCompl
    (originalLongitudinalPlane D nullDirection (adaptedPartner D charge nullDirection))
    (originalTransverse D nullDirection (adaptedPartner D charge nullDirection))
  transverseNondegenerate : ((originalGramForm D).restrict
    (originalTransverse D nullDirection (adaptedPartner D charge nullDirection))).Nondegenerate
  transverseBasis : Basis (Fin 24) ℂ
    (originalTransverse D nullDirection (adaptedPartner D charge nullDirection))
  transverseRow : Fin 24 → Fin D.rank
  transverseRowInjective : Function.Injective transverseRow
  transverseRowExact : ∀ row, row ≠ xAxis ∧ row ≠ yAxis ↔ ∃ index, transverseRow index = row
  transverseRowVector : ∀ index,
    frame (transverseRow index) = (transverseBasis index : Fin D.rank → ℂ)
  transverseGramDeterminant :
    (LinearMap.BilinForm.toMatrix transverseBasis ((originalGramForm D).restrict
      (originalTransverse D nullDirection (adaptedPartner D charge nullDirection)))).det ≠ 0

theorem original_nonzero_charge_adapted_frame_exists (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1)
    (rightGramInverse : gramComplex D * H = 1)
    (criticalRank : D.rank = 26) (charge : Charge D) (chargeNonzero : charge ≠ 0) :
    Nonempty (OriginalAdaptedFrameData D charge) := by
  classical
  obtain ⟨nullDirection, nullSelf, coefficientNonzero⟩ :=
    original_nonzero_charge_null_selection D H leftGramInverse rightGramInverse
      (by omega) charge chargeNonzero
  let longitudinal := adaptedPartner D charge nullDirection
  obtain ⟨dual, longitudinalNull, _⟩ :=
    adaptedPartner_relations D charge nullDirection nullSelf coefficientNonzero
  change gramPair D longitudinal nullDirection = 1 at dual
  change gramPair D longitudinal longitudinal = 0 at longitudinalNull
  have forwardDual : gramPair D nullDirection longitudinal = 1 := by
    rw [gramPair_symm]
    exact dual
  let form := originalGramForm D
  let plane := originalLongitudinalPlane D nullDirection longitudinal
  let transverse := originalTransverse D nullDirection longitudinal
  have formNondegenerate : form.Nondegenerate :=
    originalGramForm_nondegenerate D H leftGramInverse rightGramInverse
  have formSymmetric : LinearMap.IsSymm form :=
    (LinearMap.BilinForm.isSymm_iff).mp (originalGramForm_symmetric D)
  have pairIndependent : LinearIndependent ℂ ![nullDirection, longitudinal] := by
    apply linearIndependent_fin2.mpr
    constructor
    · change longitudinal ≠ 0
      intro longitudinalZero
      have impossible : (0 : ℂ) = 1 := by
        simpa [longitudinalZero, gramPair] using dual
      exact zero_ne_one impossible
    · intro scalar equality
      change scalar • longitudinal = nullDirection at equality
      have impossible := congrArg (gramPair D longitudinal) equality
      have zeroOne : (0 : ℂ) = 1 := by
        simpa only [gramPair_smul_right, longitudinalNull, mul_zero, dual] using impossible
      exact zero_ne_one zeroOne
  let planeBasis : Basis (Fin 2) ℂ plane := Basis.span pairIndependent
  have planeBasis_apply (index : Fin 2) :
      (planeBasis index : Fin D.rank → ℂ) = ![nullDirection, longitudinal] index :=
    congrArg Subtype.val (Basis.span_apply pairIndependent index)
  have planeGram :
      LinearMap.BilinForm.toMatrix planeBasis (form.restrict plane) = !![(0 : ℂ), 1; 1, 0] := by
    ext first second
    fin_cases first <;> fin_cases second <;>
      simp [LinearMap.BilinForm.toMatrix_apply, LinearMap.BilinForm.restrict_apply,
        planeBasis_apply, form, originalGramForm_apply,
        nullSelf, longitudinalNull, dual, forwardDual]
  have planeNondegenerate : (form.restrict plane).Nondegenerate := by
    apply (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero planeBasis).mpr
    rw [planeGram, Matrix.det_fin_two]
    norm_num
  have planeDimension : Module.finrank ℂ plane = 2 := by
    simpa using Module.finrank_eq_card_basis planeBasis
  have planeTransverseComplement : IsCompl plane transverse :=
    LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
      formSymmetric.isRefl planeNondegenerate
  have transverseDimension : Module.finrank ℂ transverse = 24 := by
    change Module.finrank ℂ (form.orthogonal plane) = 24
    rw [LinearMap.BilinForm.finrank_orthogonal formNondegenerate plane,
      Module.finrank_fin_fun ℂ, planeDimension, criticalRank]
  have transverseNondegenerate : (form.restrict transverse).Nondegenerate := by
    apply LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal form formSymmetric.isRefl
    change Disjoint (form.orthogonal plane) (form.orthogonal (form.orthogonal plane))
    rw [LinearMap.BilinForm.orthogonal_orthogonal formNondegenerate formSymmetric.isRefl plane]
    exact planeTransverseComplement.symm.disjoint
  let transverseBasis : Basis (Fin 24) ℂ transverse :=
    Module.finBasisOfFinrankEq ℂ transverse transverseDimension
  let joinedBasis : Basis (Fin 2 ⊕ Fin 24) ℂ (Fin D.rank → ℂ) :=
    (planeBasis.prod transverseBasis).map
      (Submodule.prodEquivOfIsCompl plane transverse planeTransverseComplement)
  have joinedLeft (index : Fin 2) :
      joinedBasis (Sum.inl index) = ![nullDirection, longitudinal] index := by
    simp [joinedBasis, Basis.map_apply, Basis.prod_apply,
      Submodule.coe_prodEquivOfIsCompl', planeBasis_apply]
  have joinedRight (index : Fin 24) :
      joinedBasis (Sum.inr index) = (transverseBasis index : Fin D.rank → ℂ) := by
    simp [joinedBasis, Basis.map_apply, Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']
  let axisEquiv : Fin 2 ⊕ Fin 24 ≃ Fin D.rank :=
    finSumFinEquiv.trans (finCongr (show 2 + 24 = D.rank by omega))
  let adaptedBasis := joinedBasis.reindex axisEquiv
  let standardBasis := Pi.basisFun ℂ (Fin D.rank)
  let frame : Matrix (Fin D.rank) (Fin D.rank) ℂ := (standardBasis.toMatrix adaptedBasis)ᵀ
  let inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ := (adaptedBasis.toMatrix standardBasis)ᵀ
  let xAxis := axisEquiv (Sum.inl (0 : Fin 2))
  let yAxis := axisEquiv (Sum.inl (1 : Fin 2))
  let transverseRow : Fin 24 → Fin D.rank := fun index => axisEquiv (Sum.inr index)
  have frameRow (row : Fin D.rank) : frame row = adaptedBasis row := by
    funext coordinate
    change (Pi.basisFun ℂ (Fin D.rank)).repr (adaptedBasis row) coordinate =
      adaptedBasis row coordinate
    exact Pi.basisFun_repr ℂ (Fin D.rank) (adaptedBasis row) coordinate
  have frameLeft (index : Fin 2) :
      frame (axisEquiv (Sum.inl index)) = ![nullDirection, longitudinal] index := by
    rw [frameRow]
    change joinedBasis.reindex axisEquiv (axisEquiv (Sum.inl index)) = _
    rw [Basis.reindex_apply, axisEquiv.symm_apply_apply]
    exact joinedLeft index
  have frameRight (index : Fin 24) :
      frame (transverseRow index) = (transverseBasis index : Fin D.rank → ℂ) := by
    rw [frameRow]
    change joinedBasis.reindex axisEquiv (axisEquiv (Sum.inr index)) = _
    rw [Basis.reindex_apply, axisEquiv.symm_apply_apply]
    exact joinedRight index
  have xRow : frame xAxis = nullDirection := frameLeft 0
  have yRow : frame yAxis = longitudinal := frameLeft 1
  have axesDistinct : xAxis ≠ yAxis := by
    intro equality
    have indexEquality : Sum.inl (0 : Fin 2) = Sum.inl (1 : Fin 2) := axisEquiv.injective equality
    simpa using indexEquality
  have leftFrameInverse : inverse * frame = 1 := by
    change (adaptedBasis.toMatrix standardBasis)ᵀ * (standardBasis.toMatrix adaptedBasis)ᵀ = 1
    rw [← Matrix.transpose_mul, standardBasis.toMatrix_mul_toMatrix_flip adaptedBasis,
      Matrix.transpose_one]
  have rightFrameInverse : frame * inverse = 1 := by
    change (standardBasis.toMatrix adaptedBasis)ᵀ * (adaptedBasis.toMatrix standardBasis)ᵀ = 1
    rw [← Matrix.transpose_mul, adaptedBasis.toMatrix_mul_toMatrix_flip standardBasis,
      Matrix.transpose_one]
  have nullInPlane : nullDirection ∈ plane :=
    Submodule.subset_span (Set.mem_range.mpr ⟨(0 : Fin 2), rfl⟩)
  have longitudinalInPlane : longitudinal ∈ plane :=
    Submodule.subset_span (Set.mem_range.mpr ⟨(1 : Fin 2), rfl⟩)
  have transverseNotX (index : Fin 24) : transverseRow index ≠ xAxis := by
    intro equality
    have impossible : Sum.inr index = Sum.inl (0 : Fin 2) := axisEquiv.injective equality
    cases impossible
  have transverseNotY (index : Fin 24) : transverseRow index ≠ yAxis := by
    intro equality
    have impossible : Sum.inr index = Sum.inl (1 : Fin 2) := axisEquiv.injective equality
    cases impossible
  have xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0 := by
    intro row
    obtain ⟨oldIndex, rfl⟩ := axisEquiv.surjective row
    cases oldIndex with
    | inl index =>
        fin_cases index
        · change gramPair D (frame yAxis) (frame xAxis) = if xAxis = xAxis then 1 else 0
          rw [xRow, yRow, if_pos rfl]
          exact dual
        · change gramPair D (frame yAxis) (frame yAxis) = if yAxis = xAxis then 1 else 0
          rw [yRow, if_neg axesDistinct.symm]
          exact longitudinalNull
    | inr index =>
        change gramPair D (frame yAxis) (frame (transverseRow index)) =
          if transverseRow index = xAxis then 1 else 0
        rw [yRow, frameRight, if_neg (transverseNotX index)]
        have orthogonal := (LinearMap.BilinForm.mem_orthogonal_iff.mp
          (transverseBasis index).property) longitudinal longitudinalInPlane
        simpa only [form, originalGramForm_apply] using orthogonal
  have yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0 := by
    intro row
    obtain ⟨oldIndex, rfl⟩ := axisEquiv.surjective row
    cases oldIndex with
    | inl index =>
        fin_cases index
        · change gramPair D (frame xAxis) (frame xAxis) = if xAxis = yAxis then 1 else 0
          rw [xRow, if_neg axesDistinct]
          exact nullSelf
        · change gramPair D (frame xAxis) (frame yAxis) = if yAxis = yAxis then 1 else 0
          rw [xRow, yRow, if_pos rfl]
          exact forwardDual
    | inr index =>
        change gramPair D (frame xAxis) (frame (transverseRow index)) =
          if transverseRow index = yAxis then 1 else 0
        rw [xRow, frameRight, if_neg (transverseNotY index)]
        have orthogonal := (LinearMap.BilinForm.mem_orthogonal_iff.mp
          (transverseBasis index).property) nullDirection nullInPlane
        simpa only [form, originalGramForm_apply] using orthogonal
  have transverseRowInjective : Function.Injective transverseRow :=
    axisEquiv.injective.comp Sum.inr_injective
  have transverseRowExact :
      ∀ row, row ≠ xAxis ∧ row ≠ yAxis ↔ ∃ index, transverseRow index = row := by
    intro row
    constructor
    · intro notAxes
      obtain ⟨oldIndex, rfl⟩ := axisEquiv.surjective row
      cases oldIndex with
      | inl index =>
          fin_cases index
          · exact (notAxes.1 rfl).elim
          · exact (notAxes.2 rfl).elim
      | inr index => exact ⟨index, rfl⟩
    · rintro ⟨index, rfl⟩
      exact ⟨transverseNotX index, transverseNotY index⟩
  have transverseGramDeterminant :
      (LinearMap.BilinForm.toMatrix transverseBasis (form.restrict transverse)).det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero transverseBasis).mp transverseNondegenerate
  exact ⟨{
    nullDirection := nullDirection
    nullSelf := nullSelf
    coefficientNonzero := coefficientNonzero
    frame := frame
    inverse := inverse
    xAxis := xAxis
    yAxis := yAxis
    axesDistinct := axesDistinct
    xRow := xRow
    yRow := yRow
    leftFrameInverse := leftFrameInverse
    rightFrameInverse := rightFrameInverse
    xDual := xDual
    yDual := yDual
    planeDimension := planeDimension
    transverseDimension := transverseDimension
    planeNondegenerate := planeNondegenerate
    planeTransverseComplement := planeTransverseComplement
    transverseNondegenerate := transverseNondegenerate
    transverseBasis := transverseBasis
    transverseRow := transverseRow
    transverseRowInjective := transverseRowInjective
    transverseRowExact := transverseRowExact
    transverseRowVector := frameRight
    transverseGramDeterminant := transverseGramDeterminant
  }⟩

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
