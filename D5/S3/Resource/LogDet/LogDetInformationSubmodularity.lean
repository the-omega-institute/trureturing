/- GID: D5/S3/Resource/LogDet/LogDetInformationSubmodularity
   generality: G
   mirror-B: D5/B/S3/Resource/LogDet/LogDetInformationSubmodularity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Positive matrix contributions make regularized log-determinant information submodular. -/

import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.SchurComplement

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Resource.LogDet.LogDetInformationSubmodularity

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- The regularized information operator constructed from protocol contributions. -/
def informationOperator {Protocol Index : Type*} [Fintype Index] [DecidableEq Index]
    (contribution : Protocol -> Matrix Index Index ℂ) (regularizer : ℝ)
    (selected : Finset Protocol) : Matrix Index Index ℂ :=
  (regularizer : ℂ) • 1 + ∑ protocol ∈ selected, contribution protocol

/-- Log-determinant volume relative to the regularization-only baseline. -/
def logVolumeInformation {Protocol Index : Type*} [Fintype Index] [DecidableEq Index]
    (contribution : Protocol -> Matrix Index Index ℂ) (regularizer : ℝ)
    (selected : Finset Protocol) : ℝ :=
  Real.log (informationOperator contribution regularizer selected).det.re -
    Real.log (((regularizer : ℂ) • (1 : Matrix Index Index ℂ)).det.re)

private theorem information_operator_posDef
    {Protocol Index : Type*} [Fintype Index] [DecidableEq Index]
    (contribution : Protocol -> Matrix Index Index ℂ) (regularizer : ℝ)
    (regularizerPositive : 0 < regularizer)
    (contributionNonnegative : forall protocol, (contribution protocol).PosSemidef)
    (selected : Finset Protocol) :
    (informationOperator contribution regularizer selected).PosDef := by
  apply (Matrix.PosDef.one.smul regularizerPositive).add_posSemidef
  exact Matrix.posSemidef_sum selected fun protocol _ => contributionNonnegative protocol

private theorem information_operator_mono
    {Protocol Index : Type*} [Fintype Index] [DecidableEq Index]
    (contribution : Protocol -> Matrix Index Index ℂ) (regularizer : ℝ)
    (contributionNonnegative : forall protocol, (contribution protocol).PosSemidef)
    {smaller larger : Finset Protocol} (included : smaller ⊆ larger) :
    informationOperator contribution regularizer smaller ≤
      informationOperator contribution regularizer larger := by
  have sumOrder := Finset.sum_le_sum_of_subset_of_nonneg included fun protocol _ _ =>
    (contributionNonnegative protocol).nonneg
  simpa only [informationOperator, add_comm] using
    add_le_add_left sumOrder ((regularizer : ℂ) • (1 : Matrix Index Index ℂ))

private theorem trace_log_eq_log_det
    {Index : Type*} [Fintype Index] [DecidableEq Index] [Nonempty Index]
    (matrix : Matrix Index Index ℂ) (positive : matrix.PosDef) :
    (CFC.log matrix).trace.re = Real.log matrix.det.re := by
  let hermitian := positive.isHermitian
  have traceIdentity :
      (CFC.log matrix).trace.re = ∑ i, Real.log (hermitian.eigenvalues i) := by
    change (cfc Real.log matrix).trace.re = _
    rw [hermitian.cfc_eq, Matrix.IsHermitian.cfc,
      Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
    simp
  have determinantIdentity : matrix.det.re = ∏ i, hermitian.eigenvalues i := by
    rw [hermitian.det_eq_prod_eigenvalues]
    calc
      (∏ i, (hermitian.eigenvalues i : ℂ)).re =
          ((∏ i, hermitian.eigenvalues i : ℝ) : ℂ).re := by
        congr 1
        exact (Complex.ofReal_prod (s := Finset.univ) hermitian.eigenvalues).symm
      _ = ∏ i, hermitian.eigenvalues i := Complex.ofReal_re _
  have logarithmProduct :
      Real.log (∏ i, hermitian.eigenvalues i) =
        ∑ i, Real.log (hermitian.eigenvalues i) := by
    apply Real.log_prod
    intro i _
    exact ne_of_gt (positive.eigenvalues_pos i)
  rw [traceIdentity, determinantIdentity, logarithmProduct]

private theorem real_trace_mono
    {Index : Type*} [Fintype Index]
    {left right : Matrix Index Index ℂ} (ordered : left ≤ right) :
    left.trace.re ≤ right.trace.re := by
  have differenceNonnegative : (right - left).PosSemidef := ordered
  have nonnegativeTrace := differenceNonnegative.trace_nonneg
  have realNonnegative : 0 ≤ (right - left).trace.re := nonnegativeTrace.1
  rw [Matrix.trace_sub, Complex.sub_re] at realNonnegative
  linarith

private theorem log_det_mono
    {Index : Type*} [Fintype Index] [DecidableEq Index] [Nonempty Index]
    {left right : Matrix Index Index ℂ}
    (leftPositive : left.PosDef) (rightPositive : right.PosDef)
    (ordered : left ≤ right) :
    Real.log left.det.re ≤ Real.log right.det.re := by
  letI : CStarAlgebra (Matrix Index Index ℂ) := {}
  have logOrder : CFC.log left ≤ CFC.log right :=
    CFC.log_monotoneOn leftPositive.isStrictlyPositive
      (leftPositive.isStrictlyPositive.of_le ordered) ordered
  calc
    Real.log left.det.re = (CFC.log left).trace.re :=
      (trace_log_eq_log_det left leftPositive).symm
    _ ≤ (CFC.log right).trace.re :=
      real_trace_mono logOrder
    _ = Real.log right.det.re := trace_log_eq_log_det right rightPositive

private theorem nonsing_inv_anti
    {Index : Type*} [Fintype Index] [DecidableEq Index] [Nonempty Index]
    {left right : Matrix Index Index ℂ}
    (leftPositive : left.PosDef) (ordered : left ≤ right) :
    right⁻¹ ≤ left⁻¹ := by
  letI : CStarAlgebra (Matrix Index Index ℂ) := {}
  rw [Matrix.nonsing_inv_eq_ringInverse, Matrix.nonsing_inv_eq_ringInverse]
  exact CStarAlgebra.antitoneOn_ringInverse leftPositive.isStrictlyPositive
    (leftPositive.isStrictlyPositive.of_le ordered) ordered

private theorem marginal_log_det_identity
    {Index : Type*} [Fintype Index] [DecidableEq Index] [Nonempty Index]
    (base addition : Matrix Index Index ℂ)
    (basePositive : base.PosDef) (additionNonnegative : addition.PosSemidef) :
    Real.log (base + addition).det.re - Real.log base.det.re =
      Real.log
        (1 + CFC.sqrt addition * base⁻¹ * CFC.sqrt addition).det.re := by
  let root := CFC.sqrt addition
  let marginal := 1 + root * base⁻¹ * root
  have rootSquare : root * root = addition := by
    exact CFC.sqrt_mul_sqrt_self addition additionNonnegative.nonneg
  have baseDetUnit : IsUnit base.det :=
    (Matrix.isUnit_iff_isUnit_det base).mp basePositive.isUnit
  have determinantIdentity : (base + addition).det = base.det * marginal.det := by
    simpa only [root, marginal, rootSquare] using Matrix.det_add_mul root root baseDetUnit
  have marginalPositive : marginal.PosDef := by
    apply Matrix.PosDef.one.add_posSemidef
    exact Matrix.nonneg_iff_posSemidef.mp
      (conjugate_nonneg_of_nonneg basePositive.posSemidef.inv.nonneg
        (CFC.sqrt_nonneg addition))
  have baseDetPositive := basePositive.det_pos
  have marginalDetPositive := marginalPositive.det_pos
  have determinantRealIdentity :
      (base + addition).det.re = base.det.re * marginal.det.re := by
    rw [determinantIdentity, Complex.mul_re, baseDetPositive.2.symm,
      marginalDetPositive.2.symm]
    simp
  rw [determinantRealIdentity,
    Real.log_mul (ne_of_gt baseDetPositive.1) (ne_of_gt marginalDetPositive.1)]
  ring

private theorem marginal_matrix_posDef
    {Index : Type*} [Fintype Index] [DecidableEq Index] [Nonempty Index]
    (base addition : Matrix Index Index ℂ)
    (basePositive : base.PosDef) :
    (1 + CFC.sqrt addition * base⁻¹ * CFC.sqrt addition).PosDef := by
  apply Matrix.PosDef.one.add_posSemidef
  exact Matrix.nonneg_iff_posSemidef.mp
    (conjugate_nonneg_of_nonneg basePositive.posSemidef.inv.nonneg
      (CFC.sqrt_nonneg addition))

/-- Regularized log-determinant information is monotone and has diminishing marginal returns. -/
theorem log_det_information_monotone_submodular
    {Protocol Index : Type*} [DecidableEq Protocol] [Fintype Index] [DecidableEq Index]
    (contribution : Protocol -> Matrix Index Index ℂ) (regularizer : ℝ)
    (regularizerPositive : 0 < regularizer)
    (contributionNonnegative : forall protocol, (contribution protocol).PosSemidef) :
    (forall smaller larger : Finset Protocol, smaller ⊆ larger ->
      logVolumeInformation contribution regularizer smaller ≤
        logVolumeInformation contribution regularizer larger) ∧
    (forall smaller larger : Finset Protocol, forall protocol : Protocol,
      smaller ⊆ larger ->
      logVolumeInformation contribution regularizer (smaller ∪ {protocol}) -
          logVolumeInformation contribution regularizer smaller ≥
        logVolumeInformation contribution regularizer (larger ∪ {protocol}) -
          logVolumeInformation contribution regularizer larger) := by
  classical
  cases isEmpty_or_nonempty Index with
  | inl emptyIndex =>
      letI := emptyIndex
      have zeroValue : forall selected : Finset Protocol,
          logVolumeInformation contribution regularizer selected = 0 := by
        intro selected
        have operatorZero : informationOperator contribution regularizer selected = 0 :=
          Subsingleton.elim _ _
        simp [logVolumeInformation, operatorZero]
      simp [zeroValue]
  | inr nonemptyIndex =>
    letI := nonemptyIndex
    constructor
    · intro smaller larger included
      unfold logVolumeInformation
      have smallerPositive := information_operator_posDef contribution regularizer
        regularizerPositive contributionNonnegative smaller
      have largerPositive := information_operator_posDef contribution regularizer
        regularizerPositive contributionNonnegative larger
      have ordered := information_operator_mono contribution regularizer
        contributionNonnegative included
      linarith [log_det_mono smallerPositive largerPositive ordered]
    · intro smaller larger protocol included
      by_cases protocolInLarger : protocol ∈ larger
      · by_cases protocolInSmaller : protocol ∈ smaller
        · simp only [Finset.union_eq_left.mpr
              (Finset.singleton_subset_iff.mpr protocolInSmaller),
            Finset.union_eq_left.mpr (Finset.singleton_subset_iff.mpr protocolInLarger),
            sub_self, le_refl]
        · rw [Finset.union_eq_left.mpr (Finset.singleton_subset_iff.mpr protocolInLarger)]
          have smallerSubsetInsert : smaller ⊆ smaller ∪ {protocol} := Finset.subset_union_left
          have monotoneGain := log_det_mono
            (information_operator_posDef contribution regularizer regularizerPositive
              contributionNonnegative smaller)
            (information_operator_posDef contribution regularizer regularizerPositive
              contributionNonnegative (smaller ∪ {protocol}))
            (information_operator_mono contribution regularizer contributionNonnegative
              smallerSubsetInsert)
          unfold logVolumeInformation at monotoneGain ⊢
          linarith
      · have protocolNotInSmaller : protocol ∉ smaller := fun member =>
          protocolInLarger (included member)
        let smallerOperator := informationOperator contribution regularizer smaller
        let largerOperator := informationOperator contribution regularizer larger
        let root := CFC.sqrt (contribution protocol)
        let smallerMarginal := 1 + root * smallerOperator⁻¹ * root
        let largerMarginal := 1 + root * largerOperator⁻¹ * root
        have smallerPositive := information_operator_posDef contribution regularizer
          regularizerPositive contributionNonnegative smaller
        have largerPositive := information_operator_posDef contribution regularizer
          regularizerPositive contributionNonnegative larger
        have operatorOrder := information_operator_mono contribution regularizer
          contributionNonnegative included
        have inverseOrder : largerOperator⁻¹ ≤ smallerOperator⁻¹ :=
          nonsing_inv_anti smallerPositive operatorOrder
        have marginalOrder : largerMarginal ≤ smallerMarginal := by
          dsimp only [largerMarginal, smallerMarginal]
          exact add_le_add_right
            ((CFC.sqrt_nonneg (contribution protocol)).isSelfAdjoint.conjugate_le_conjugate
              inverseOrder) 1
        have smallerMarginalPositive : smallerMarginal.PosDef := by
          exact marginal_matrix_posDef smallerOperator (contribution protocol)
            smallerPositive
        have largerMarginalPositive : largerMarginal.PosDef := by
          exact marginal_matrix_posDef largerOperator (contribution protocol)
            largerPositive
        have marginalGainOrder := log_det_mono largerMarginalPositive
          smallerMarginalPositive marginalOrder
        have smallerInsert :
            informationOperator contribution regularizer (smaller ∪ {protocol}) =
              smallerOperator + contribution protocol := by
          simp [informationOperator, smallerOperator, protocolNotInSmaller,
            add_assoc, add_comm]
        have largerInsert :
            informationOperator contribution regularizer (larger ∪ {protocol}) =
              largerOperator + contribution protocol := by
          simp [informationOperator, largerOperator, protocolInLarger,
            add_assoc, add_comm]
        have smallerGain := marginal_log_det_identity smallerOperator
          (contribution protocol) smallerPositive (contributionNonnegative protocol)
        have largerGain := marginal_log_det_identity largerOperator
          (contribution protocol) largerPositive (contributionNonnegative protocol)
        unfold logVolumeInformation
        rw [smallerInsert, largerInsert]
        dsimp only [smallerMarginal, largerMarginal, root] at marginalGainOrder
        dsimp only [smallerOperator, largerOperator] at smallerGain largerGain
        linarith

end D5.S3.Resource.LogDet.LogDetInformationSubmodularity

#print axioms
  D5.S3.Resource.LogDet.LogDetInformationSubmodularity.log_det_information_monotone_submodular
