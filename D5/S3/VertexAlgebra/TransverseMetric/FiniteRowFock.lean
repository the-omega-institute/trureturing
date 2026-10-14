/- GID: D5/S3/VertexAlgebra/TransverseMetric/FiniteRowFock
   generality: G
   mirror-B: none
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Restricted real row Gram positivity for the actual oscillator pairing. -/

import D5.S3.VertexAlgebra.LatticeOscillatorFockMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.TransverseMetric.FiniteRowFock

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
  LatticeSugawaraCurrents LatticeOscillatorFockForm MvPolynomial Matrix
open scoped BigOperators Matrix

noncomputable section

def conjugatePolynomial (axisType : Type*) :
    MvPolynomial (axisType × ℕ) ℂ →ₗ⋆[ℂ] MvPolynomial (axisType × ℕ) ℂ where
  toFun := MvPolynomial.map (starRingEnd ℂ)
  map_add' := by intro left right; exact map_add _ left right
  map_smul' := by
    intro scalar polynomial
    simp [MvPolynomial.smul_eq_C_mul]

def occupationWeight (axisType : Type*) (diagonal : axisType → ℝ)
    (occupation : (axisType × ℕ) →₀ ℕ) : ℝ :=
  occupation.prod (fun coordinate count =>
    (count.factorial : ℝ) * ((coordinate.2 + 1 : ℝ) * diagonal coordinate.1) ^ count)

private theorem occupationWeight_insert (axisType : Type*) (diagonal : axisType → ℝ)
    (occupation : (axisType × ℕ) →₀ ℕ) (coordinate : (axisType × ℕ)) :
    occupationWeight axisType diagonal (occupation + Finsupp.single coordinate 1) =
      (occupation coordinate + 1 : ℝ) * ((coordinate.2 + 1 : ℝ) * diagonal coordinate.1) *
        occupationWeight axisType diagonal occupation := by
  classical
  let factor : (axisType × ℕ) → ℕ → ℝ := fun index count =>
    (count.factorial : ℝ) * ((index.2 + 1 : ℝ) * diagonal index.1) ^ count
  have factor_zero : ∀ index, factor index 0 = 1 := by intro index; simp [factor]
  have erased : (occupation + Finsupp.single coordinate 1).erase coordinate =
      occupation.erase coordinate := by
    ext index
    by_cases equal : index = coordinate <;> simp [equal]
  change (occupation + Finsupp.single coordinate 1).prod factor =
    _ * _ * occupation.prod factor
  rw [← Finsupp.mul_prod_erase' _ coordinate factor factor_zero, erased,
    ← Finsupp.mul_prod_erase' occupation coordinate factor factor_zero]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, factor, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  ring

private def diagonalBilinear (axisType : Type*) (diagonal : axisType → ℝ) :
    (MvPolynomial (axisType × ℕ) ℂ) →ₗ[ℂ] (MvPolynomial (axisType × ℕ) ℂ) →ₗ[ℂ] ℂ :=
  (basisMonomials ((axisType × ℕ)) ℂ).constr ℂ (fun occupation =>
    (occupationWeight axisType diagonal occupation : ℂ) • lcoeff ℂ occupation)

private def diagonalForm (axisType : Type*) (diagonal : axisType → ℝ) :
    (MvPolynomial (axisType × ℕ) ℂ) →ₗ⋆[ℂ] (MvPolynomial (axisType × ℕ) ℂ) →ₗ[ℂ] ℂ :=
  (diagonalBilinear axisType diagonal).comp (conjugatePolynomial axisType)

private theorem diagonalForm_monomial (axisType : Type*) (diagonal : axisType → ℝ)
    (occupation : (axisType × ℕ) →₀ ℕ) (scalar : ℂ) (polynomial : (MvPolynomial (axisType × ℕ) ℂ)) :
    diagonalForm axisType diagonal (monomial occupation scalar) polynomial =
      star scalar * (occupationWeight axisType diagonal occupation : ℂ) * coeff occupation polynomial := by
  have monomial_scalar : (monomial occupation (star scalar) : (MvPolynomial (axisType × ℕ) ℂ)) =
      star scalar • monomial occupation 1 := by simp [smul_monomial]
  change diagonalBilinear axisType diagonal
    (MvPolynomial.map (starRingEnd ℂ) (monomial occupation scalar)) polynomial = _
  rw [map_monomial]
  change diagonalBilinear axisType diagonal (monomial occupation (star scalar)) polynomial = _
  rw [monomial_scalar, map_smul, LinearMap.smul_apply]
  have basis_value := (basisMonomials ((axisType × ℕ)) ℂ).constr_basis ℂ
    (fun exponent => (occupationWeight axisType diagonal exponent : ℂ) • lcoeff ℂ exponent) occupation
  change diagonalBilinear axisType diagonal (monomial occupation 1) = _ at basis_value
  rw [basis_value]
  simp [smul_eq_mul, mul_assoc]

private theorem diagonalForm_creator (axisType : Type*) (diagonal : axisType → ℝ)
    (coordinate : (axisType × ℕ)) (left right : (MvPolynomial (axisType × ℕ) ℂ)) :
    diagonalForm axisType diagonal (X coordinate * left) right =
      diagonalForm axisType diagonal left
        (((coordinate.2 + 1 : ℂ) * (diagonal coordinate.1 : ℂ)) • pderiv coordinate right) := by
  classical
  induction left using MvPolynomial.induction_on' with
  | add first second first_induction second_induction =>
      simp [mul_add, map_add, LinearMap.add_apply, first_induction, second_induction]
  | monomial occupation scalar =>
      have insertion : X coordinate * (monomial occupation scalar : (MvPolynomial (axisType × ℕ) ℂ)) =
          monomial (occupation + Finsupp.single coordinate 1) scalar := by
        simpa [mul_comm] using
          (monomial_add_single (s := occupation) (n := coordinate) (e := 1) (a := scalar)).symm
      rw [insertion, diagonalForm_monomial, diagonalForm_monomial, occupationWeight_insert]
      simp only [coeff_smul, coeff_pderiv, Complex.real_smul, smul_eq_mul,
        Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one]
      ring

private theorem diagonalForm_vacuum (axisType : Type*) (diagonal : axisType → ℝ)
    (polynomial : (MvPolynomial (axisType × ℕ) ℂ)) :
    diagonalForm axisType diagonal 1 polynomial = constantCoeff polynomial := by
  rw [one_def, diagonalForm_monomial]
  simp [occupationWeight, constantCoeff_eq]

private theorem diagonalForm_coefficients (axisType : Type*) (diagonal : axisType → ℝ)
    (left right : (MvPolynomial (axisType × ℕ) ℂ)) :
    diagonalForm axisType diagonal left right = ∑ occupation ∈ left.support,
      star (coeff occupation left) * (occupationWeight axisType diagonal occupation : ℂ) *
        coeff occupation right := by
  conv_lhs => rw [left.as_sum]
  simp only [map_sum, LinearMap.sum_apply, diagonalForm_monomial]

private theorem diagonalForm_norm (axisType : Type*) (diagonal : axisType → ℝ)
    (polynomial : (MvPolynomial (axisType × ℕ) ℂ)) :
    diagonalForm axisType diagonal polynomial polynomial = (∑ occupation ∈ polynomial.support,
      occupationWeight axisType diagonal occupation *
        Complex.normSq (coeff occupation polynomial) : ℝ) := by
  rw [diagonalForm_coefficients]
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro occupation _
  rw [mul_comm (star _), mul_assoc]
  change (occupationWeight axisType diagonal occupation : ℂ) *
    ((starRingEnd ℂ) (coeff occupation polynomial) * coeff occupation polynomial) = _
  rw [← Complex.normSq_eq_conj_mul_self]
  simp


private theorem diagonalForm_unique (axisType : Type*) (diagonal : axisType → ℝ)
    (candidate : MvPolynomial (axisType × ℕ) ℂ →ₗ⋆[ℂ]
      MvPolynomial (axisType × ℕ) ℂ →ₗ[ℂ] ℂ)
    (vacuum : ∀ polynomial, candidate 1 polynomial = constantCoeff polynomial)
    (adjoint : ∀ (coordinate : axisType × ℕ) left right,
      candidate (X coordinate * left) right = candidate left
        (((coordinate.2 + 1 : ℂ) * (diagonal coordinate.1 : ℂ)) • pderiv coordinate right)) :
    candidate = diagonalForm axisType diagonal := by
  apply LinearMap.ext
  intro left
  apply LinearMap.ext
  intro right
  induction left using MvPolynomial.induction_on generalizing right with
  | C scalar =>
      simp [C_eq_smul_one, LinearMap.map_smulₛₗ, LinearMap.smul_apply, vacuum,
        diagonalForm_vacuum]
  | add first second first_induction second_induction =>
      simp [map_add, LinearMap.add_apply, first_induction, second_induction]
  | mul_X polynomial generator induction_hypothesis =>
      rw [mul_comm polynomial (X generator), adjoint, diagonalForm_creator]
      exact induction_hypothesis _

def rowPolynomial (D : LatticeData) {axisType : Type*} [Fintype axisType]
    (rows : Matrix axisType (Fin D.rank) ℝ) :
    MvPolynomial (axisType × ℕ) ℂ →ₐ[ℂ] Oscillator D :=
  aeval (fun coordinate => ∑ axis, (rows coordinate.1 axis : ℂ) • X (axis, coordinate.2))

def rowGram (D : LatticeData) {axisType : Type*} [Fintype axisType]
    (rows : Matrix axisType (Fin D.rank) ℝ) : Matrix axisType axisType ℝ :=
  rows * LatticeOscillatorFockMetric.gramReal D * rows.transpose

private theorem rowGram_apply (D : LatticeData) {axisType : Type*} [Fintype axisType]
    (rows : Matrix axisType (Fin D.rank) ℝ) (left right : axisType) :
    rowGram D rows left right =
      ∑ first, ∑ second, rows left first * (D.G first second : ℝ) * rows right second := by
  simp only [rowGram, Matrix.mul_apply, Matrix.transpose_apply,
    LatticeOscillatorFockMetric.gramReal, Finset.sum_mul]
  rw [Finset.sum_comm]

private def rowAnnihilator (D : LatticeData) {axisType : Type*} [Fintype axisType]
    (rows : Matrix axisType (Fin D.rank) ℝ) (coordinate : axisType × ℕ) :
    Module.End ℂ (Oscillator D) :=
  ∑ axis, (rows coordinate.1 axis : ℂ) • annihilator D (axis, coordinate.2)

private theorem rowPolynomial_constantCoeff (D : LatticeData)
    {axisType : Type*} [Fintype axisType] (rows : Matrix axisType (Fin D.rank) ℝ)
    (polynomial : MvPolynomial (axisType × ℕ) ℂ) :
    constantCoeff (rowPolynomial D rows polynomial) = constantCoeff polynomial := by
  induction polynomial using MvPolynomial.induction_on with
  | C scalar => simp [rowPolynomial]
  | add first second first_induction second_induction =>
      simp [map_add, first_induction, second_induction]
  | mul_X polynomial coordinate induction_hypothesis =>
      simp [rowPolynomial, map_sum, constantCoeff_smul]

private theorem rowAnnihilator_mul (D : LatticeData)
    {axisType : Type*} [Fintype axisType] (rows : Matrix axisType (Fin D.rank) ℝ)
    (coordinate : axisType × ℕ) (left right : Oscillator D) :
    rowAnnihilator D rows coordinate (left * right) =
      rowAnnihilator D rows coordinate left * right +
        left * rowAnnihilator D rows coordinate right := by
  simp only [rowAnnihilator, annihilator, weightedPartial, LinearMap.sum_apply,
    LinearMap.smul_apply, Derivation.coeFn_coe, pderiv_mul, smul_add,
    Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm]

private theorem rowAnnihilator_generator (D : LatticeData)
    {axisType : Type*} [Fintype axisType] (rows : Matrix axisType (Fin D.rank) ℝ)
    (left right : axisType × ℕ) :
    rowAnnihilator D rows left (rowPolynomial D rows (X right)) =
      if left.2 = right.2 then C ((left.2 + 1 : ℂ) * (rowGram D rows left.1 right.1 : ℂ))
      else 0 := by
  classical
  rcases left with ⟨leftAxis, leftFrequency⟩
  rcases right with ⟨rightAxis, rightFrequency⟩
  by_cases equal : leftFrequency = rightFrequency
  · subst rightFrequency
    simp only [rowPolynomial, aeval_X, rowAnnihilator, LinearMap.sum_apply,
      LinearMap.smul_apply, annihilator, weightedPartial, Derivation.coeFn_coe,
      map_sum, map_smul, RingHom.id_apply, pderiv_X, Pi.single_apply,
      Prod.mk.injEq, and_true]
    simp only [ite_smul, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [rowGram_apply]
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum,
      C_eq_smul_one, Finset.smul_sum, smul_smul, map_sum, if_true]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro first _
    apply Finset.sum_congr rfl
    intro second _
    simp only [smul_ite, smul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Complex.ofReal_intCast]
    congr 1
    ring
  · simp [rowPolynomial, rowAnnihilator, annihilator, weightedPartial,
      LinearMap.sum_apply, LinearMap.smul_apply, Derivation.coeFn_coe,
      pderiv_X, Pi.single_apply, Prod.mk.injEq, equal, Ne.symm equal]

private theorem rowAnnihilator_substitution (D : LatticeData)
    {axisType : Type*} [Fintype axisType] [DecidableEq axisType]
    (rows : Matrix axisType (Fin D.rank) ℝ) (diagonal : axisType → ℝ)
    (orthogonal : rowGram D rows = Matrix.diagonal diagonal)
    (coordinate : axisType × ℕ) (polynomial : MvPolynomial (axisType × ℕ) ℂ) :
    rowAnnihilator D rows coordinate (rowPolynomial D rows polynomial) =
      rowPolynomial D rows
        (((coordinate.2 + 1 : ℂ) * (diagonal coordinate.1 : ℂ)) • pderiv coordinate polynomial) := by
  classical
  induction polynomial using MvPolynomial.induction_on with
  | C scalar => simp [rowPolynomial, rowAnnihilator, annihilator, weightedPartial,
      LinearMap.sum_apply, LinearMap.smul_apply, Derivation.coeFn_coe]
  | add first second first_induction second_induction =>
      simp [map_add, first_induction, second_induction, smul_add]
  | mul_X polynomial generator induction_hypothesis =>
      rw [map_mul, rowAnnihilator_mul, induction_hypothesis, rowAnnihilator_generator,
        orthogonal]
      simp only [pderiv_mul, pderiv_X, Pi.single_apply, smul_add, map_add, map_smul,
        RingHom.id_apply, smul_mul_assoc, mul_smul_comm, map_mul, Matrix.diagonal_apply]
      rcases coordinate with ⟨axis, frequency⟩
      rcases generator with ⟨other, otherFrequency⟩
      by_cases sameAxis : axis = other <;> by_cases sameFrequency : frequency = otherFrequency
      <;> simp [sameAxis, sameFrequency, Prod.mk.injEq, eq_comm,
        MvPolynomial.smul_eq_C_mul, map_add, map_mul, mul_comm]

private theorem rowPolynomial_diagonal_pullback (D : LatticeData)
    {axisType : Type*} [Fintype axisType] [DecidableEq axisType]
    (rows : Matrix axisType (Fin D.rank) ℝ) (diagonal : axisType → ℝ)
    (orthogonal : rowGram D rows = Matrix.diagonal diagonal)
    (left right : MvPolynomial (axisType × ℕ) ℂ) :
    fockForm D (rowPolynomial D rows left) (rowPolynomial D rows right) =
      diagonalForm axisType diagonal left right := by
  classical
  let candidate : MvPolynomial (axisType × ℕ) ℂ →ₗ⋆[ℂ]
      MvPolynomial (axisType × ℕ) ℂ →ₗ[ℂ] ℂ :=
    (LinearMap.compl₂ (fockForm D) (rowPolynomial D rows).toLinearMap).comp
      (rowPolynomial D rows).toLinearMap
  have vacuum : ∀ polynomial, candidate 1 polynomial = constantCoeff polynomial := by
    intro polynomial
    change fockForm D (rowPolynomial D rows 1) (rowPolynomial D rows polynomial) = _
    rw [map_one, fockForm_vacuum_left, rowPolynomial_constantCoeff]
  have adjoint : ∀ (coordinate : axisType × ℕ) left right,
      candidate (X coordinate * left) right = candidate left
        (((coordinate.2 + 1 : ℂ) * (diagonal coordinate.1 : ℂ)) • pderiv coordinate right) := by
    intro coordinate left right
    have creator : ∀ axis, fockForm D
        (X (axis, coordinate.2) * rowPolynomial D rows left) (rowPolynomial D rows right) =
        fockForm D (rowPolynomial D rows left)
          (annihilator D (axis, coordinate.2) (rowPolynomial D rows right)) := by
      intro axis
      simpa only [neutralPolynomialMode_negative, neutralPolynomialMode_positive,
        LinearMap.mulLeft_apply, annihilator] using
        fockForm_creation_adjoint D 0 axis coordinate.2
          (rowPolynomial D rows left) (rowPolynomial D rows right)
    calc
      candidate (X coordinate * left) right =
          fockForm D (rowPolynomial D rows left)
            (rowAnnihilator D rows coordinate (rowPolynomial D rows right)) := by
        change fockForm D (rowPolynomial D rows (X coordinate * left))
          (rowPolynomial D rows right) = _
        rw [map_mul]
        have generator : rowPolynomial D rows (X coordinate) =
            ∑ axis, (rows coordinate.1 axis : ℂ) • X (axis, coordinate.2) := by
          simp [rowPolynomial]
        rw [generator]
        simp only [Finset.sum_mul, smul_mul_assoc,
          map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
          Complex.conj_ofReal, creator]
        simp only [rowAnnihilator, map_sum, LinearMap.sum_apply, LinearMap.smul_apply,
          map_smul, RingHom.id_apply]
      _ = candidate left
          (((coordinate.2 + 1 : ℂ) * (diagonal coordinate.1 : ℂ)) • pderiv coordinate right) := by
        rw [rowAnnihilator_substitution D rows diagonal orthogonal]
        rfl
  exact congrArg (fun form => form left right)
    (diagonalForm_unique axisType diagonal candidate vacuum adjoint)

def changeCoordinates {axisType : Type*} [Fintype axisType]
    (matrix : Matrix axisType axisType ℝ) :
    MvPolynomial (axisType × ℕ) ℂ →ₐ[ℂ] MvPolynomial (axisType × ℕ) ℂ :=
  aeval (fun coordinate => ∑ axis, (matrix coordinate.1 axis : ℂ) • X (axis, coordinate.2))

private theorem changeCoordinates_comp {axisType : Type*} [Fintype axisType]
    (matrix inverse : Matrix axisType axisType ℝ) :
    (changeCoordinates matrix).comp (changeCoordinates inverse) =
      changeCoordinates (inverse * matrix) := by
  classical
  apply MvPolynomial.algHom_ext
  intro coordinate
  simp only [AlgHom.comp_apply, changeCoordinates, aeval_X, map_sum, map_smul,
    Finset.smul_sum, smul_smul, Matrix.mul_apply, Complex.ofReal_sum, Complex.ofReal_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro axis _
  rw [Finset.sum_smul]

private theorem changeCoordinates_one {axisType : Type*} [Fintype axisType]
    [DecidableEq axisType] :
    changeCoordinates (1 : Matrix axisType axisType ℝ) = AlgHom.id ℂ _ := by
  apply MvPolynomial.algHom_ext
  intro coordinate
  simp [changeCoordinates, Matrix.one_apply]

private theorem rowPolynomial_comp (D : LatticeData) {axisType : Type*}
    [Fintype axisType] (rows : Matrix axisType (Fin D.rank) ℝ)
    (matrix : Matrix axisType axisType ℝ) :
    (rowPolynomial D rows).comp (changeCoordinates matrix) =
      rowPolynomial D (matrix * rows) := by
  classical
  apply MvPolynomial.algHom_ext
  intro coordinate
  simp only [AlgHom.comp_apply, changeCoordinates, rowPolynomial, aeval_X,
    map_sum, map_smul, Finset.smul_sum, smul_smul, Matrix.mul_apply,
    Complex.ofReal_sum, Complex.ofReal_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro axis _
  rw [Finset.sum_smul]

private theorem rowGram_mul (D : LatticeData) {axisType : Type*}
    [Fintype axisType] (rows : Matrix axisType (Fin D.rank) ℝ)
    (matrix : Matrix axisType axisType ℝ) :
    rowGram D (matrix * rows) = matrix * rowGram D rows * matrix.transpose := by
  simp only [rowGram, Matrix.transpose_mul, Matrix.mul_assoc]

private theorem occupationWeight_pos (axisType : Type*) (diagonal : axisType → ℝ)
    (positive : ∀ axis, 0 < diagonal axis) (occupation : (axisType × ℕ) →₀ ℕ) :
    0 < occupationWeight axisType diagonal occupation := by
  classical
  apply Finset.prod_pos
  intro coordinate _
  apply mul_pos
  · exact_mod_cast Nat.factorial_pos (occupation coordinate)
  · exact pow_pos (mul_pos (by positivity) (positive coordinate.1)) _

theorem rowPolynomial_norm (D : LatticeData) {axisType : Type*}
    [Fintype axisType] [LinearOrder axisType] [WellFoundedLT axisType]
    [LocallyFiniteOrderBot axisType]
    (rows : Matrix axisType (Fin D.rank) ℝ) (positive : (rowGram D rows).PosDef)
    (polynomial : MvPolynomial (axisType × ℕ) ℂ) :
    fockForm D (rowPolynomial D rows polynomial) (rowPolynomial D rows polynomial) =
      (∑ occupation ∈ (changeCoordinates (LDL.lower positive) polynomial).support,
        occupationWeight axisType (LDL.diagEntries positive) occupation * Complex.normSq
          (coeff occupation (changeCoordinates (LDL.lower positive) polynomial)) : ℝ) := by
  classical
  have orthogonal : rowGram D (LDL.lowerInv positive * rows) =
      Matrix.diagonal (LDL.diagEntries positive) := by
    rw [rowGram_mul]
    simpa only [LDL.diag, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (LDL.diag_eq_lowerInv_conj positive).symm
  have original : rowPolynomial D (LDL.lowerInv positive * rows)
      (changeCoordinates (LDL.lower positive) polynomial) = rowPolynomial D rows polynomial := by
    have composition := rowPolynomial_comp D (LDL.lowerInv positive * rows) (LDL.lower positive)
    rw [← Matrix.mul_assoc, LDL.lower, Matrix.inv_mul_of_invertible,
      Matrix.one_mul] at composition
    exact congrArg (fun hom => hom polynomial) composition
  rw [← original, rowPolynomial_diagonal_pullback D _ _ orthogonal, diagonalForm_norm]

theorem rowPolynomial_positive (D : LatticeData) {axisType : Type*}
    [Fintype axisType] [LinearOrder axisType] [WellFoundedLT axisType]
    [LocallyFiniteOrderBot axisType]
    (rows : Matrix axisType (Fin D.rank) ℝ) (positive : (rowGram D rows).PosDef)
    (polynomial : MvPolynomial (axisType × ℕ) ℂ) (nonzero : polynomial ≠ 0) :
    0 < (fockForm D (rowPolynomial D rows polynomial) (rowPolynomial D rows polynomial)).re := by
  classical
  rw [rowPolynomial_norm D rows positive, Complex.ofReal_re]
  have transformed_nonzero : changeCoordinates (LDL.lower positive) polynomial ≠ 0 := by
    intro zero
    have composition := changeCoordinates_comp (LDL.lowerInv positive) (LDL.lower positive)
    have inverseEq : LDL.lower positive * LDL.lowerInv positive = 1 :=
      Matrix.inv_mul_of_invertible _
    rw [inverseEq, changeCoordinates_one] at composition
    have recovery := congrArg (fun hom => hom polynomial) composition
    simp only [AlgHom.comp_apply, AlgHom.id_apply] at recovery
    rw [zero, map_zero] at recovery
    exact nonzero recovery.symm
  have diagonalPositive : ∀ axis, 0 < LDL.diagEntries positive axis := by
    have conjugate : (LDL.diag positive).PosDef := by
      rw [LDL.diag_eq_lowerInv_conj]
      exact (isUnit_of_invertible (LDL.lowerInv positive)).posDef_star_right_conjugate_iff.mpr
        positive
    intro axis
    simpa only [LDL.diag, Matrix.diagonal_apply_eq] using conjugate.diag_pos (i := axis)
  apply Finset.sum_pos
  · intro occupation member
    exact mul_pos (occupationWeight_pos axisType _ diagonalPositive occupation)
      (Complex.normSq_pos.mpr (MvPolynomial.mem_support_iff.mp member))
  · exact MvPolynomial.support_nonempty.mpr transformed_nonzero

theorem rowPolynomial_injective (D : LatticeData) {axisType : Type*}
    [Fintype axisType] [LinearOrder axisType] [WellFoundedLT axisType]
    [LocallyFiniteOrderBot axisType]
    (rows : Matrix axisType (Fin D.rank) ℝ) (positive : (rowGram D rows).PosDef) :
    Function.Injective (rowPolynomial D rows) := by
  intro left right equality
  by_contra unequal
  have nonzero : left - right ≠ 0 := sub_ne_zero.mpr unequal
  have strict := rowPolynomial_positive D rows positive (left - right) nonzero
  simp only [map_sub, equality, sub_self, map_zero, Complex.zero_re] at strict
  exact lt_irrefl 0 strict

theorem rowPolynomial_norm_real (D : LatticeData) {axisType : Type*}
    [Fintype axisType] [LinearOrder axisType] [WellFoundedLT axisType]
    [LocallyFiniteOrderBot axisType]
    (rows : Matrix axisType (Fin D.rank) ℝ) (positive : (rowGram D rows).PosDef)
    (polynomial : MvPolynomial (axisType × ℕ) ℂ) :
    (fockForm D (rowPolynomial D rows polynomial) (rowPolynomial D rows polynomial)).im = 0 := by
  rw [rowPolynomial_norm D rows positive, Complex.ofReal_im]

end
end D5.S3.VertexAlgebra.TransverseMetric.FiniteRowFock
