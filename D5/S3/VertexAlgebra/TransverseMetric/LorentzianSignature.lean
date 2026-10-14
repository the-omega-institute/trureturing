/- GID: D5/S3/VertexAlgebra/TransverseMetric/LorentzianSignature
   generality: G
   mirror-B: none
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ambient Lorentzian inertia forces the actual transverse Gram to be positive definite. -/

import D5.S3.VertexAlgebra.TransverseMetric.NativePositivity
import D5.S3.QuadraticForms.ActualSignature

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.TransverseMetric.LorentzianSignature

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
  LatticeOscillatorFockForm LatticeOscillatorFockMetric LatticeBcGhostBrstCharge
  BcGhostFockSupport OriginalQQuartetSource NativePositivity
open scoped BigOperators Matrix

noncomputable section

private theorem signature_full_posDef {V : Type} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (form : QuadraticForm ℝ V)
    (full : QuadraticForms.ActualSignature.signature form = (Module.finrank ℝ V : ℤ)) :
    form.PosDef := by
  have bound := sigPos_le_finrank form
  have positiveRank : sigPos form = Module.finrank ℝ V := by
    unfold QuadraticForms.ActualSignature.signature at full
    omega
  obtain ⟨space, rank, positive⟩ := exists_finrank_eq_sigPos_and_posDef form
  have top := Submodule.eq_top_of_finrank_eq (rank.trans positiveRank)
  intro vector nonzero
  exact positive ⟨vector, by rw [top]; trivial⟩ (by simpa using nonzero)

def axisEquiv (D : LatticeData) (xAxis yAxis : Fin D.rank) (distinct : xAxis ≠ yAxis) :
    (Unit ⊕ Unit) ⊕ TransverseAxis D xAxis yAxis ≃ Fin D.rank where
  toFun := Sum.elim (Sum.elim (fun _ => xAxis) (fun _ => yAxis)) Subtype.val
  invFun := fun axis => if first : axis = xAxis then .inl (.inl ())
    else if second : axis = yAxis then .inl (.inr ()) else .inr ⟨axis, first, second⟩
  left_inv := by
    intro axis
    rcases axis with (⟨⟩ | ⟨⟩) | axis
    · simp
    · simp [Ne.symm distinct]
    · simp [axis.2.1, axis.2.2]
  right_inv := by
    intro axis
    by_cases first : axis = xAxis
    · simp [first]
    · by_cases second : axis = yAxis <;> simp [first, second, Ne.symm distinct]

private theorem axis_sum (D : LatticeData) (xAxis yAxis : Fin D.rank)
    (distinct : xAxis ≠ yAxis) (value : Fin D.rank → ℝ) :
    ∑ axis, value axis = value xAxis + value yAxis +
      ∑ axis : TransverseAxis D xAxis yAxis, value axis.1 := by
  rw [← Equiv.sum_comp (axisEquiv D xAxis yAxis distinct)]
  simp [Fintype.sum_sum_type, axisEquiv]

theorem transverse_card (D : LatticeData) (xAxis yAxis : Fin D.rank)
    (distinct : xAxis ≠ yAxis) :
    Fintype.card (TransverseAxis D xAxis yAxis) + 2 = D.rank := by
  have count := Fintype.card_congr (axisEquiv D xAxis yAxis distinct)
  simpa [add_comm, add_left_comm, add_assoc] using count

def coordinateEquiv (D : LatticeData) (xAxis yAxis : Fin D.rank)
    (distinct : xAxis ≠ yAxis) :
    (Fin D.rank → ℝ) ≃ₗ[ℝ] (ℝ × ℝ) × (TransverseAxis D xAxis yAxis → ℝ) where
  toFun := fun vector => ((vector xAxis, vector yAxis), fun axis => vector axis.1)
  invFun := fun vector axis => if first : axis = xAxis then vector.1.1
    else if second : axis = yAxis then vector.1.2 else vector.2 ⟨axis, first, second⟩
  left_inv := by
    intro vector
    funext axis
    by_cases first : axis = xAxis
    · simp [first]
    · by_cases second : axis = yAxis <;> simp [first, second, Ne.symm distinct]
  right_inv := by
    intro vector
    ext
    · simp
    · simp [Ne.symm distinct]
    · rename_i axis
      simp [axis.2.1, axis.2.2]
  map_add' := by intro first second; rfl
  map_smul' := by intro scalar vector; rfl

def realFrame (D : LatticeData) (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    Matrix (Fin D.rank) (Fin D.rank) ℝ := fun row column => (frame row column).re

private theorem real_frame_inverse (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (realRows : ∀ row column, star (frame row column) = frame row column)
    (leftInverse : inverse * frame = 1) (rightInverse : frame * inverse = 1) :
    realFrame D inverse * realFrame D frame = 1 ∧
      realFrame D frame * realFrame D inverse = 1 := by
  have imaginary (row column : Fin D.rank) : (frame row column).im = 0 := by
    have equality := Complex.conj_eq_iff_re.mp (realRows row column)
    have := congrArg Complex.im equality
    simpa using this.symm
  constructor
  · ext row column
    have equality := congrArg (fun matrix => (matrix row column).re) leftInverse
    simpa [realFrame, Matrix.mul_apply, Complex.mul_re,
      imaginary, Matrix.one_apply, apply_ite] using equality
  · ext row column
    have equality := congrArg (fun matrix => (matrix row column).re) rightInverse
    simpa [realFrame, Matrix.mul_apply, Complex.mul_re,
      imaginary, Matrix.one_apply, apply_ite] using equality

private theorem row_gram_real (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (realRows : ∀ row column, star (frame row column) = frame row column)
    (first second : Fin D.rank) :
    (realFrame D frame * gramReal D * (realFrame D frame).transpose) first second =
      (gramPair D (frame first) (frame second)).re := by
  apply Complex.ofReal_injective
  have realEntry (row column : Fin D.rank) :
      ((frame row column).re : ℂ) = frame row column :=
    Complex.conj_eq_iff_re.mp (realRows row column)
  have pairReal : ((gramPair D (frame first) (frame second)).re : ℂ) =
      gramPair D (frame first) (frame second) := by
    apply Complex.conj_eq_iff_re.mp
    change star (gramPair D (frame first) (frame second)) = _
    simp only [gramPair, star_sum, star_mul, realRows, star_intCast]
    apply Finset.sum_congr rfl
    intro firstComponent _
    apply Finset.sum_congr rfl
    intro secondComponent _
    ring
  rw [pairReal]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, realFrame,
    gramReal, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast,
    realEntry, gramPair]
  rw [Finset.sum_comm]

private theorem quadratic_apply_sum {Axis : Type} [Fintype Axis] [DecidableEq Axis]
    (matrix : Matrix Axis Axis ℝ) (vector : Axis → ℝ) :
    matrix.toQuadraticForm' vector =
      ∑ first, ∑ second, vector first * matrix first second * vector second := by
  simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  ring

theorem ambient_equivalent_split (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : inverse * frame = 1) (rightInverse : frame * inverse = 1)
    (xAxis yAxis : Fin D.rank) (distinct : xAxis ≠ yAxis)
    (realRows : ∀ row column, star (frame row column) = frame row column)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0) :
    QuadraticMap.Equivalent (gramReal D).toQuadraticForm'
      (((2 : ℝ) • QuadraticMap.linMulLin (LinearMap.fst ℝ ℝ ℝ)
        (LinearMap.snd ℝ ℝ ℝ)).prod (transverseGram D frame xAxis yAxis).toQuadraticForm') := by
  classical
  let rows := realFrame D frame
  let rowGram := rows * gramReal D * rows.transpose
  obtain ⟨leftReal, rightReal⟩ := real_frame_inverse D frame inverse realRows leftInverse rightInverse
  let basisChange := Matrix.toLinearEquivRight'OfInv leftReal rightReal
  have frameEquiv : QuadraticMap.Equivalent rowGram.toQuadraticForm' (gramReal D).toQuadraticForm' := by
    refine ⟨{ basisChange with map_app' := ?_ }⟩
    intro vector
    change (gramReal D).toQuadraticForm' (Matrix.vecMul vector rows) = rowGram.toQuadraticForm' vector
    simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply']
    rw [Matrix.mulVec_vecMul]
    simp only [rowGram, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mul_assoc]
  have gramEntry (first second : Fin D.rank) :
      rowGram first second = (gramPair D (frame first) (frame second)).re :=
    row_gram_real D frame realRows first second
  have gramSymm (first second : Fin D.rank) : rowGram first second = rowGram second first := by
    rw [gramEntry, gramEntry, gramPair_symm]
  have xEntry (row : Fin D.rank) : rowGram xAxis row = if row = yAxis then 1 else 0 := by
    rw [gramEntry, yDual]
    split_ifs <;> simp
  have yEntry (row : Fin D.rank) : rowGram yAxis row = if row = xAxis then 1 else 0 := by
    rw [gramEntry, xDual]
    split_ifs <;> simp
  have splitEquiv : QuadraticMap.Equivalent rowGram.toQuadraticForm'
      (((2 : ℝ) • QuadraticMap.linMulLin (LinearMap.fst ℝ ℝ ℝ)
        (LinearMap.snd ℝ ℝ ℝ)).prod (transverseGram D frame xAxis yAxis).toQuadraticForm') := by
    refine ⟨{ coordinateEquiv D xAxis yAxis distinct with map_app' := ?_ }⟩
    intro vector
    simp only [QuadraticMap.prod_apply, smul_apply, QuadraticMap.linMulLin_apply,
      LinearMap.fst_apply, LinearMap.snd_apply, coordinateEquiv,
      quadratic_apply_sum, smul_eq_mul]
    change (2 : ℝ) * (vector xAxis * vector yAxis) +
      (∑ first : TransverseAxis D xAxis yAxis, ∑ second : TransverseAxis D xAxis yAxis,
        vector first.1 * transverseGram D frame xAxis yAxis first second * vector second.1) =
      ∑ first : Fin D.rank, ∑ second : Fin D.rank,
        vector first * rowGram first second * vector second
    have xSum : (∑ row, vector xAxis * rowGram xAxis row * vector row) =
        vector xAxis * vector yAxis := by
      simp only [xEntry, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have ySum : (∑ row, vector yAxis * rowGram yAxis row * vector row) =
        vector yAxis * vector xAxis := by
      simp only [yEntry, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have transverseEntry (axis : TransverseAxis D xAxis yAxis) :
        ∑ row, vector axis.1 * rowGram axis.1 row * vector row =
          ∑ row : TransverseAxis D xAxis yAxis,
            vector axis.1 * transverseGram D frame xAxis yAxis axis row * vector row.1 := by
      rw [axis_sum D xAxis yAxis distinct]
      rw [gramSymm axis.1 xAxis, gramSymm axis.1 yAxis, xEntry, yEntry]
      simp only [if_neg axis.2.2, if_neg axis.2.1, mul_zero, zero_mul, zero_add]
      simp only [gramEntry, transverseGram]
    have transverseSum :
        (∑ axis : TransverseAxis D xAxis yAxis, ∑ row : Fin D.rank,
          vector axis.1 * rowGram axis.1 row * vector row) =
        ∑ axis : TransverseAxis D xAxis yAxis, ∑ row : TransverseAxis D xAxis yAxis,
          vector axis.1 * transverseGram D frame xAxis yAxis axis row * vector row.1 :=
      Finset.sum_congr rfl (fun axis _ => transverseEntry axis)
    have wholeSum := axis_sum D xAxis yAxis distinct
      (fun axis => ∑ row, vector axis * rowGram axis row * vector row)
    rw [xSum, ySum, transverseSum] at wholeSum
    rw [wholeSum]
    ring
  exact frameEquiv.symm.trans splitEquiv

theorem transverseGram_posDef (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : inverse * frame = 1) (rightInverse : frame * inverse = 1)
    (xAxis yAxis : Fin D.rank) (distinct : xAxis ≠ yAxis)
    (realRows : ∀ row column, star (frame row column) = frame row column)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (lorentzian : QuadraticForms.ActualSignature.signature (gramReal D).toQuadraticForm' =
      (D.rank : ℤ) - 2) :
    (transverseGram D frame xAxis yAxis).PosDef := by
  classical
  have equivalence := ambient_equivalent_split D frame inverse leftInverse rightInverse
    xAxis yAxis distinct realRows xDual yDual
  have inertia : QuadraticForms.ActualSignature.signature (gramReal D).toQuadraticForm' =
      QuadraticForms.ActualSignature.signature (transverseGram D frame xAxis yAxis).toQuadraticForm' := by
    unfold QuadraticForms.ActualSignature.signature
    rw [equivalence.sigPos_eq, equivalence.sigNeg_eq]
    change QuadraticForms.ActualSignature.signature _ = _
    rw [QuadraticForms.ActualSignature.signature_prod,
      show (2 : ℝ) = 2 * 1 by ring, QuadraticForms.ActualSignature.signature_hyperbolic, zero_add]
  have full : QuadraticForms.ActualSignature.signature
      (transverseGram D frame xAxis yAxis).toQuadraticForm' =
      (Module.finrank ℝ (TransverseAxis D xAxis yAxis → ℝ) : ℤ) := by
    rw [← inertia, lorentzian, Module.finrank_pi_fintype]
    have count := transverse_card D xAxis yAxis distinct
    norm_num
    omega
  apply Matrix.PosDef.of_toQuadraticForm' _ (signature_full_posDef _ full)
  ext first second
  exact congrArg Complex.re (gramPair_symm D (frame second.1) (frame first.1))

theorem nativePolynomial_positive_of_lorentzian (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : inverse * frame = 1) (rightInverse : frame * inverse = 1)
    (xAxis yAxis : Fin D.rank) (distinct : xAxis ≠ yAxis)
    (realRows : ∀ row column, star (frame row column) = frame row column)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (lorentzian : QuadraticForms.ActualSignature.signature (gramReal D).toQuadraticForm' =
      (D.rank : ℤ) - 2)
    (polynomial : MvPolynomial (TransverseAxis D xAxis yAxis × ℕ) ℂ)
    (nonzero : polynomial ≠ 0) :
    0 < (fockForm D (nativePolynomial D frame xAxis yAxis polynomial)
      (nativePolynomial D frame xAxis yAxis polynomial)).re ∧
      (fockForm D (nativePolynomial D frame xAxis yAxis polynomial)
        (nativePolynomial D frame xAxis yAxis polynomial)).im = 0 := by
  have positive := transverseGram_posDef D frame inverse leftInverse rightInverse xAxis yAxis
    distinct realRows xDual yDual lorentzian
  have realTransverse := fun (axis : TransverseAxis D xAxis yAxis) column => realRows axis.1 column
  exact ⟨nativePolynomial_positive D frame xAxis yAxis realTransverse positive polynomial nonzero,
    nativePolynomial_norm_real D frame xAxis yAxis realTransverse positive polynomial⟩

theorem native_degree_one_negative_C0_positive_of_lorentzian (D : LatticeData)
    (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1)
    (rightGramInverse : gramComplex D * H = 1)
    (leftFrameInverse : inverse * frame = 1)
    (rightFrameInverse : frame * inverse = 1)
    (beta : Charge D) (xAxis yAxis : Fin D.rank) (distinct : xAxis ≠ yAxis) (level : ℤ)
    (realRows : ∀ row column, star (frame row column) = frame row column)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (lorentzian : QuadraticForms.ActualSignature.signature (gramReal D).toQuadraticForm' =
      (D.rank : ℤ) - 2)
    (state : State D)
    (member : state ∈ nativeTransverseEnergySpace D H frame inverse leftGramInverse
      rightGramInverse leftFrameInverse rightFrameInverse beta xAxis yAxis level)
    (degreeOne : LatticeBcGhostBrstGhostNumber.J D state = state) (nonzero : state ≠ 0) :
    0 < (-LatticeBcGhostHermitianForm.F D state (C D 0 state)).re ∧
      (-LatticeBcGhostHermitianForm.F D state (C D 0 state)).im = 0 := by
  have positive := transverseGram_posDef D frame inverse leftFrameInverse rightFrameInverse
    xAxis yAxis distinct realRows xDual yDual lorentzian
  exact native_degree_one_negative_C0_positive D H frame inverse leftGramInverse rightGramInverse
    leftFrameInverse rightFrameInverse beta xAxis yAxis level
    (fun axis column => realRows axis.1 column) positive state member degreeOne nonzero

#print axioms ambient_equivalent_split
#print axioms transverseGram_posDef
#print axioms nativePolynomial_positive_of_lorentzian
#print axioms native_degree_one_negative_C0_positive_of_lorentzian

end
end D5.S3.VertexAlgebra.TransverseMetric.LorentzianSignature
