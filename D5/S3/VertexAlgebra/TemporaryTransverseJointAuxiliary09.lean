import D5.S3.VertexAlgebra.TemporaryTransverseJointAuxiliary08
namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
  LatticeSugawaraVirasoro LatticeSugawaraConformal LatticeBcGhostBrstCharge BcGhostFockSupport
open scoped BigOperators TensorProduct

noncomputable section

def axisAuxDegree (D : LatticeData) (xAxis yAxis axis : Fin D.rank) : ℤ :=
  if axis = xAxis then 1 else if axis = yAxis then -1 else 0

def auxiliaryWeight (D : LatticeData) (xAxis yAxis : Fin D.rank) (index : Index D) : ℤ :=
  axisAuxDegree D xAxis yAxis index.1

def axisExponentCount (D : LatticeData) (axis : Fin D.rank) (powers : Index D →₀ ℕ) : ℕ :=
  powers.sum (fun index exponent => if index.1 = axis then exponent else 0)

theorem signed_weight_axis_counts (D : LatticeData) (xAxis yAxis : Fin D.rank) (distinct : xAxis ≠ yAxis)
    (powers : Index D →₀ ℕ) :
    Finsupp.weight (auxiliaryWeight D xAxis yAxis) powers =
      (axisExponentCount D xAxis powers : ℤ) - (axisExponentCount D yAxis powers : ℤ) := by
  classical
  simp only [axisExponentCount, Finsupp.weight_apply, Finsupp.sum, Nat.cast_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro index indexMember
  by_cases atX : index.1 = xAxis
  · have notY : index.1 ≠ yAxis := by rw [atX]; exact distinct
    simp [auxiliaryWeight, axisAuxDegree, atX, notY, distinct, nsmul_eq_mul]
  by_cases atY : index.1 = yAxis
  · simp [auxiliaryWeight, axisAuxDegree, atX, atY, distinct, Ne.symm distinct,
      nsmul_eq_mul]
  · simp [auxiliaryWeight, axisAuxDegree, atX, atY, nsmul_eq_mul]

def auxDiagonal (D : LatticeData) (xAxis yAxis : Fin D.rank) : Module.End ℂ (Oscillator D) :=
  (Finsupp.linearCombination ℂ (fun powers : Index D →₀ ℕ =>
      (Finsupp.weight (auxiliaryWeight D xAxis yAxis) powers : ℂ) •
        (MvPolynomial.monomial powers (1 : ℂ) : Oscillator D))).comp
    (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

def polynomialAux (D : LatticeData) (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (xAxis yAxis : Fin D.rank) : Module.End ℂ (Oscillator D) :=
  (coordinateSub D frame).toLinearMap.comp
    ((auxDiagonal D xAxis yAxis).comp (coordinateSub D inverse).toLinearMap)

def matterAux (D : LatticeData) (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (xAxis yAxis : Fin D.rank) : Module.End ℂ (Carrier D) :=
  Finsupp.mapRange.linearMap (polynomialAux D frame inverse xAxis yAxis)

def matterAuxLift (D : LatticeData) (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (xAxis yAxis : Fin D.rank) : Module.End ℂ (State D) :=
  TensorProduct.map (matterAux D frame inverse xAxis yAxis) LinearMap.id

def auxiliary (D : LatticeData) (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (xAxis yAxis : Fin D.rank) : Module.End ℂ (State D) :=
  matterAuxLift D frame inverse xAxis yAxis + LatticeBcGhostBrstGhostNumber.J D - 1

def AuxHomogeneous (D : LatticeData) (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (xAxis yAxis : Fin D.rank) (degree : ℤ) (state : State D) : Prop :=
  auxiliary D frame inverse xAxis yAxis state = (degree : ℂ) • state

theorem auxDiagonal_monomial (D : LatticeData) (xAxis yAxis : Fin D.rank)
    (powers : Index D →₀ ℕ) (scalar : ℂ) :
    auxDiagonal D xAxis yAxis (MvPolynomial.monomial powers scalar) =
      (Finsupp.weight (auxiliaryWeight D xAxis yAxis) powers : ℂ) • MvPolynomial.monomial powers scalar := by
  simp [auxDiagonal, Finsupp.lsum_single, MvPolynomial.monomial]
  ring

theorem auxDiagonal_coeff (D : LatticeData) (xAxis yAxis : Fin D.rank)
    (polynomial : Oscillator D) (powers : Index D →₀ ℕ) :
    MvPolynomial.coeff powers (auxDiagonal D xAxis yAxis polynomial) =
      (Finsupp.weight (auxiliaryWeight D xAxis yAxis) powers : ℂ) * MvPolynomial.coeff powers polynomial := by
  classical
  induction polynomial using MvPolynomial.induction_on' with
  | monomial exponents scalar =>
      rw [auxDiagonal_monomial]
      by_cases equal : exponents = powers <;> simp [MvPolynomial.coeff_monomial, equal, eq_comm]
  | add first second firstProof secondProof =>
      simp only [map_add, MvPolynomial.coeff_add, firstProof, secondProof, mul_add]

theorem auxDiagonal_multiply_X (D : LatticeData) (xAxis yAxis : Fin D.rank)
    (index : Index D) (polynomial : Oscillator D) :
    auxDiagonal D xAxis yAxis (MvPolynomial.X index * polynomial) -
      MvPolynomial.X index * auxDiagonal D xAxis yAxis polynomial =
      (auxiliaryWeight D xAxis yAxis index : ℂ) • (MvPolynomial.X index * polynomial) := by
  classical
  apply MvPolynomial.ext
  intro powers
  simp only [MvPolynomial.coeff_sub, auxDiagonal_coeff, MvPolynomial.coeff_X_mul',
    MvPolynomial.coeff_smul]
  by_cases present : index ∈ powers.support
  · have weightEquality := Finsupp.weight_sub_single_add
      (w := auxiliaryWeight D xAxis yAxis) (Finsupp.mem_support_iff.mp present)
    have scalarEquality := congrArg (Int.cast : ℤ → ℂ) weightEquality
    simp only [Int.cast_add] at scalarEquality
    simp only [if_pos present, auxDiagonal_coeff]
    rw [← scalarEquality]
    ring
  · simp [present]

theorem auxDiagonal_pderiv (D : LatticeData) (xAxis yAxis : Fin D.rank)
    (index : Index D) (polynomial : Oscillator D) :
    auxDiagonal D xAxis yAxis (MvPolynomial.pderiv index polynomial) -
      MvPolynomial.pderiv index (auxDiagonal D xAxis yAxis polynomial) =
      (-(auxiliaryWeight D xAxis yAxis index : ℂ)) • MvPolynomial.pderiv index polynomial := by
  classical
  apply MvPolynomial.ext
  intro powers
  simp only [MvPolynomial.coeff_sub, auxDiagonal_coeff, MvPolynomial.coeff_pderiv,
    MvPolynomial.coeff_smul, map_add, Finsupp.weight_single, one_nsmul, Int.cast_add]
  ring

theorem auxDiagonal_homogeneous (D : LatticeData) (xAxis yAxis : Fin D.rank)
    (polynomial : Oscillator D) (degree : ℤ)
    (homogeneous : MvPolynomial.IsWeightedHomogeneous (auxiliaryWeight D xAxis yAxis) polynomial degree) :
    auxDiagonal D xAxis yAxis polynomial = (degree : ℂ) • polynomial := by
  classical
  conv_lhs => rw [polynomial.as_sum]
  simp only [map_sum, auxDiagonal_monomial]
  have supportDegree (powers : Index D →₀ ℕ) (member : powers ∈ polynomial.support) :
      Finsupp.weight (auxiliaryWeight D xAxis yAxis) powers = degree :=
    homogeneous (MvPolynomial.mem_support_iff.mp member)
  calc
    _ = ∑ powers ∈ polynomial.support, (degree : ℂ) •
        MvPolynomial.monomial powers (MvPolynomial.coeff powers polynomial) := by
      apply Finset.sum_congr rfl
      intro powers member
      rw [supportDegree powers member]
    _ = _ := by rw [← Finset.smul_sum, ← polynomial.as_sum]

theorem polynomialAux_coordinateSub (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ) (rightFrameInverse : frame * inverse = 1)
    (xAxis yAxis : Fin D.rank) (polynomial : Oscillator D) :
    polynomialAux D frame inverse xAxis yAxis (coordinateSub D frame polynomial) =
      coordinateSub D frame (auxDiagonal D xAxis yAxis polynomial) := by
  simp only [polynomialAux, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    coordinateSub_inverse D inverse frame rightFrameInverse]

theorem matterAux_single (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (xAxis yAxis : Fin D.rank) (charge : Charge D) (polynomial : Oscillator D) :
    matterAux D frame inverse xAxis yAxis (Finsupp.single charge polynomial) =
      Finsupp.single charge (polynomialAux D frame inverse xAxis yAxis polynomial) := by
  simp [matterAux]

theorem balanced_axes (D : LatticeData) (xAxis yAxis : Fin D.rank) (distinct : xAxis ≠ yAxis)
    (coefficients : Fin D.rank → Fin D.rank → ℂ)
    (xRow : ∀ row, coefficients xAxis row = if row = yAxis then 1 else 0)
    (yRow : ∀ row, coefficients yAxis row = if row = xAxis then 1 else 0)
    (xColumn : ∀ row, coefficients row xAxis = if row = yAxis then 1 else 0)
    (yColumn : ∀ row, coefficients row yAxis = if row = xAxis then 1 else 0)
    (first second : Fin D.rank) :
    ((axisAuxDegree D xAxis yAxis first : ℂ) + (axisAuxDegree D xAxis yAxis second : ℂ)) *
      coefficients first second = 0 := by
  classical
  by_cases firstX : first = xAxis
  · subst first
    by_cases secondY : second = yAxis
    · subst second; simp [axisAuxDegree, distinct, Ne.symm distinct, xRow]
    · simp [xRow, secondY]
  by_cases firstY : first = yAxis
  · subst first
    by_cases secondX : second = xAxis
    · subst second; simp [axisAuxDegree, distinct, Ne.symm distinct, yRow]
    · simp [yRow, secondX]
  by_cases secondX : second = xAxis
  · subst second; simp [xColumn, firstY]
  by_cases secondY : second = yAxis
  · subst second; simp [yColumn, firstX]
  simp [axisAuxDegree, firstX, firstY, secondX, secondY]

theorem frameGram_aux_balance (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (xAxis yAxis : Fin D.rank) (distinct : xAxis ≠ yAxis)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (first second : Fin D.rank) :
    ((axisAuxDegree D xAxis yAxis first : ℂ) + (axisAuxDegree D xAxis yAxis second : ℂ)) *
      gramPair D (frame first) (frame second) = 0 := by
  apply balanced_axes D xAxis yAxis distinct (fun first second => gramPair D (frame first) (frame second))
    yDual xDual
  · intro row; rw [gramPair_symm, yDual]
  · intro row; rw [gramPair_symm, xDual]

theorem frameH_aux_balance (D : LatticeData)
    (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (xAxis yAxis : Fin D.rank) (distinct : xAxis ≠ yAxis)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (first second : Fin D.rank) :
    ((axisAuxDegree D xAxis yAxis first : ℂ) + (axisAuxDegree D xAxis yAxis second : ℂ)) *
      frameH D H inverse first second = 0 := by
  obtain ⟨xRow, yRow, xColumn, yColumn⟩ := frameH_longitudinal_rows_columns D H frame inverse
    leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse xAxis yAxis xDual yDual
  exact balanced_axes D xAxis yAxis distinct (frameH D H inverse) xRow yRow xColumn yColumn first second

theorem auxDiagonal_coordinateDerivative (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (xAxis yAxis : Fin D.rank) (distinct : xAxis ≠ yAxis)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (axis : Fin D.rank) (frequency : ℕ) (polynomial : Oscillator D) :
    auxDiagonal D xAxis yAxis (coordinateDerivative D frame (frame axis) frequency polynomial) -
      coordinateDerivative D frame (frame axis) frequency (auxDiagonal D xAxis yAxis polynomial) =
      (axisAuxDegree D xAxis yAxis axis : ℂ) •
        coordinateDerivative D frame (frame axis) frequency polynomial := by
  classical
  simp only [coordinateDerivative, LinearMap.sum_apply, LinearMap.smul_apply,
    Derivation.coeFn_coe, map_sum, map_smul, Finset.smul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro row rowMember
  rw [← smul_sub, auxDiagonal_pderiv]
  simp only [auxiliaryWeight, smul_smul]
  apply congrArg (fun scalar : ℂ => scalar • MvPolynomial.pderiv (row, frequency) polynomial)
  have balance := frameGram_aux_balance D frame xAxis yAxis distinct xDual yDual axis row
  linear_combination -balance

theorem original_current_aux_coordinate (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ) (rightFrameInverse : frame * inverse = 1)
    (xAxis yAxis : Fin D.rank) (distinct : xAxis ≠ yAxis)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (charge : Charge D) (axis : Fin D.rank) (mode : ℤ) (nonzeroMode : mode ≠ 0)
    (polynomial : Oscillator D) :
    polynomialAux D frame inverse xAxis yAxis
        (directionalPolynomialCurrent D (frame axis) charge mode (coordinateSub D frame polynomial)) -
      directionalPolynomialCurrent D (frame axis) charge mode
        (polynomialAux D frame inverse xAxis yAxis (coordinateSub D frame polynomial)) =
      (axisAuxDegree D xAxis yAxis axis : ℂ) •
        directionalPolynomialCurrent D (frame axis) charge mode (coordinateSub D frame polynomial) := by
  rcases lt_or_gt_of_ne nonzeroMode with negative | positive
  · let frequency : ℕ := (-mode - 1).toNat
    have modeEquality : mode = -(frequency : ℤ) - 1 := by dsimp [frequency]; omega
    simp only [modeEquality, directionalPolynomialCurrent_negative, polynomialAux_coordinateSub D frame inverse
      rightFrameInverse, ← map_sub]
    rw [auxDiagonal_multiply_X]
    exact map_smul (coordinateSub D frame) _ _
  · let frequency : ℕ := (mode - 1).toNat
    have modeEquality : mode = (frequency : ℤ) + 1 := by dsimp [frequency]; omega
    simp only [modeEquality, directionalPolynomialCurrent_positive,
      polynomialAux_coordinateSub D frame inverse rightFrameInverse]
    rw [map_smul (polynomialAux D frame inverse xAxis yAxis)]
    rw [polynomialAux_coordinateSub D frame inverse rightFrameInverse]
    rw [← smul_sub, ← map_sub,
      auxDiagonal_coordinateDerivative D frame xAxis yAxis distinct xDual yDual]
    rw [map_smul (coordinateSub D frame)]
    module

theorem matterAux_current (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (xAxis yAxis : Fin D.rank) (distinct : xAxis ≠ yAxis)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (axis : Fin D.rank) (mode : ℤ) (nonzeroMode : mode ≠ 0) :
    matterAux D frame inverse xAxis yAxis * directionalCurrent D (frame axis) mode -
      directionalCurrent D (frame axis) mode * matterAux D frame inverse xAxis yAxis =
      (axisAuxDegree D xAxis yAxis axis : ℂ) • directionalCurrent D (frame axis) mode := by
  apply Finsupp.lhom_ext
  intro charge polynomial
  have actual := original_current_aux_coordinate D frame inverse rightFrameInverse xAxis yAxis distinct
    xDual yDual charge axis mode nonzeroMode (coordinateSub D inverse polynomial)
  rw [coordinateSub_inverse D frame inverse leftFrameInverse] at actual
  simpa only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply,
    directionalCurrent_single, matterAux_single, ← Finsupp.single_sub, ← Finsupp.smul_single] using
    congrArg (Finsupp.single charge) actual

theorem auxiliary_O_commutator (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (xAxis yAxis : Fin D.rank) (distinct : xAxis ≠ yAxis)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (axis : Fin D.rank) (mode : ℤ) (nonzeroMode : mode ≠ 0) :
    auxiliary D frame inverse xAxis yAxis * O D (frame axis) mode -
      O D (frame axis) mode * auxiliary D frame inverse xAxis yAxis =
      (axisAuxDegree D xAxis yAxis axis : ℂ) • O D (frame axis) mode := by
  have lifted := congrArg (LinearMap.rTensorHom (Fock ℂ))
    (matterAux_current D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis distinct
      xDual yDual axis mode nonzeroMode)
  simp only [map_sub, map_smul, LinearMap.coe_rTensorHom, LinearMap.rTensor_mul] at lifted
  have ghostCommute : LatticeBcGhostBrstGhostNumber.J D * O D (frame axis) mode =
      O D (frame axis) mode * LatticeBcGhostBrstGhostNumber.J D := by
    apply TensorProduct.ext'
    intro matter ghost
    simp [LatticeBcGhostBrstGhostNumber.J, O, Module.End.mul_apply]
  change matterAuxLift D frame inverse xAxis yAxis * O D (frame axis) mode -
    O D (frame axis) mode * matterAuxLift D frame inverse xAxis yAxis = _ at lifted
  have o_rTensor : O D (frame axis) mode =
      LinearMap.rTensor (Fock ℂ) (directionalCurrent D (frame axis) mode) := by
    rw [O, LinearMap.rTensor_def]
  conv_rhs => rw [o_rTensor]
  calc
    _ = (matterAuxLift D frame inverse xAxis yAxis * O D (frame axis) mode -
          O D (frame axis) mode * matterAuxLift D frame inverse xAxis yAxis) +
        (LatticeBcGhostBrstGhostNumber.J D * O D (frame axis) mode -
          O D (frame axis) mode * LatticeBcGhostBrstGhostNumber.J D) := by
      unfold auxiliary
      simp only [sub_mul, mul_sub, add_mul, mul_add, one_mul, mul_one]
      abel
    _ = _ := by rw [lifted, ghostCommute, sub_self, add_zero]

theorem original_coordinate_polarized_aux_degree (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ) (rightFrameInverse : frame * inverse = 1)
    (xAxis yAxis : Fin D.rank) (charge : Charge D) (powers : Index D →₀ ℕ)
    (scalar : ℂ) (subset : Finset ℕ) :
    AuxHomogeneous D frame inverse xAxis yAxis
      (Finsupp.weight (auxiliaryWeight D xAxis yAxis) powers + epsilonCount subset +
        (thetaCount subset : ℤ) - (etaCount subset : ℤ))
      (Finsupp.single charge (coordinateSub D frame (MvPolynomial.monomial powers scalar)) ⊗ₜ[ℂ]
        downWord subset down) := by
  let state : State D :=
    Finsupp.single charge (coordinateSub D frame (MvPolynomial.monomial powers scalar)) ⊗ₜ[ℂ]
      downWord subset down
  have ghost := (original_polarized_state_sector D
    (Finsupp.single charge (coordinateSub D frame (MvPolynomial.monomial powers scalar))) subset).1
  have diagonal := auxDiagonal_homogeneous D xAxis yAxis (MvPolynomial.monomial powers scalar)
    (Finsupp.weight (auxiliaryWeight D xAxis yAxis) powers)
    (MvPolynomial.isWeightedHomogeneous_monomial (auxiliaryWeight D xAxis yAxis) powers scalar rfl)
  have matterEigen :
      matterAuxLift D frame inverse xAxis yAxis state =
        (Finsupp.weight (auxiliaryWeight D xAxis yAxis) powers : ℂ) • state := by
    simp only [state, matterAuxLift, TensorProduct.map_tmul, LinearMap.id_apply,
      matterAux_single, polynomialAux_coordinateSub D frame inverse rightFrameInverse,
      diagonal, map_smul, ← Finsupp.smul_single]
    rw [← TensorProduct.smul_tmul']
  change matterAuxLift D frame inverse xAxis yAxis state + LatticeBcGhostBrstGhostNumber.J D state - state =
    (((Finsupp.weight (auxiliaryWeight D xAxis yAxis) powers : ℤ) + epsilonCount subset +
      (thetaCount subset : ℤ) - (etaCount subset : ℤ) : ℤ) : ℂ) • state
  rw [matterEigen, ghost]
  push_cast
  module

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
