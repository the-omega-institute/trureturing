/- GID: D5/S3/VertexAlgebra/TransverseMetric/NativePositivity
   generality: G
   mirror-B: none
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native transverse polynomial and degree-one negative right-C0 positivity. -/

import D5.S3.VertexAlgebra.TransverseMetric.FiniteRowFock
import D5.S3.VertexAlgebra.OriginalNonzeroGhostMultiplicity
import D5.S3.VertexAlgebra.LatticeBcGhostAuxiliarySelection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.TransverseMetric.NativePositivity

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
  LatticeOscillatorFockForm LatticeBcGhostBrstCharge BcGhostFockSupport
  OriginalQQuartetSource MvPolynomial FiniteRowFock
open scoped BigOperators TensorProduct

noncomputable section

abbrev TransverseAxis (D : LatticeData) (xAxis yAxis : Fin D.rank) :=
  {axis : Fin D.rank // axis ≠ xAxis ∧ axis ≠ yAxis}

def transverseIndex (D : LatticeData) (xAxis yAxis : Fin D.rank) :
    TransverseAxis D xAxis yAxis × ℕ → Index D :=
  fun coordinate => (coordinate.1.1, coordinate.2)

private theorem transverseIndex_injective (D : LatticeData) (xAxis yAxis : Fin D.rank) :
    Function.Injective (transverseIndex D xAxis yAxis) := by
  rintro ⟨first, firstFrequency⟩ ⟨second, secondFrequency⟩ equality
  have components := Prod.mk.inj equality
  exact Prod.ext (Subtype.ext components.1) components.2

def transverseRows (D : LatticeData) (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (xAxis yAxis : Fin D.rank) : Matrix (TransverseAxis D xAxis yAxis) (Fin D.rank) ℝ :=
  fun axis component => (frame axis.1 component).re

def transverseGram (D : LatticeData) (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (xAxis yAxis : Fin D.rank) :
    Matrix (TransverseAxis D xAxis yAxis) (TransverseAxis D xAxis yAxis) ℝ :=
  fun first second => (gramPair D (frame first.1) (frame second.1)).re

def nativePolynomial (D : LatticeData) (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (xAxis yAxis : Fin D.rank) :
    MvPolynomial (TransverseAxis D xAxis yAxis × ℕ) ℂ →ₐ[ℂ] Oscillator D :=
  (coordinateSub D frame).comp (rename (transverseIndex D xAxis yAxis))

private theorem row_real (D : LatticeData) (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (xAxis yAxis : Fin D.rank)
    (realRows : ∀ (axis : TransverseAxis D xAxis yAxis) component,
      star (frame axis.1 component) = frame axis.1 component)
    (axis : TransverseAxis D xAxis yAxis) (component : Fin D.rank) :
    ((frame axis.1 component).re : ℂ) = frame axis.1 component :=
  Complex.conj_eq_iff_re.mp (realRows axis component)

theorem transverseGram_actual_real (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (xAxis yAxis : Fin D.rank)
    (realRows : ∀ (axis : TransverseAxis D xAxis yAxis) component,
      star (frame axis.1 component) = frame axis.1 component)
    (first second : TransverseAxis D xAxis yAxis) :
    gramPair D (frame first.1) (frame second.1) =
      (transverseGram D frame xAxis yAxis first second : ℂ) := by
  apply (Complex.conj_eq_iff_re.mp ?_).symm
  change star (gramPair D (frame first.1) (frame second.1)) = _
  simp only [gramPair, star_sum, star_mul, realRows, star_intCast]
  apply Finset.sum_congr rfl
  intro firstComponent _
  apply Finset.sum_congr rfl
  intro secondComponent _
  ring

private theorem transverseGram_rowGram (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (xAxis yAxis : Fin D.rank)
    (realRows : ∀ (axis : TransverseAxis D xAxis yAxis) component,
      star (frame axis.1 component) = frame axis.1 component) :
    transverseGram D frame xAxis yAxis = rowGram D (transverseRows D frame xAxis yAxis) := by
  classical
  ext first second
  apply Complex.ofReal_injective
  rw [← transverseGram_actual_real D frame xAxis yAxis realRows first second]
  simp only [rowGram, Matrix.mul_apply, Matrix.transpose_apply, transverseRows,
    LatticeOscillatorFockMetric.gramReal, Finset.sum_mul, gramPair,
    Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast,
    row_real D frame xAxis yAxis realRows]
  rw [Finset.sum_comm]

private theorem nativePolynomial_rowPolynomial (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (xAxis yAxis : Fin D.rank)
    (realRows : ∀ (axis : TransverseAxis D xAxis yAxis) component,
      star (frame axis.1 component) = frame axis.1 component) :
    nativePolynomial D frame xAxis yAxis = rowPolynomial D (transverseRows D frame xAxis yAxis) := by
  classical
  apply MvPolynomial.algHom_ext
  intro coordinate
  simp only [nativePolynomial, AlgHom.comp_apply, rename_X, coordinateSub_X,
    OriginalQQuartetSource.coordinate, rowPolynomial, aeval_X, transverseIndex,
    transverseRows, row_real D frame xAxis yAxis realRows]

theorem nativePolynomial_positive (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (xAxis yAxis : Fin D.rank)
    (realRows : ∀ (axis : TransverseAxis D xAxis yAxis) component,
      star (frame axis.1 component) = frame axis.1 component)
    (positive : (transverseGram D frame xAxis yAxis).PosDef)
    (polynomial : MvPolynomial (TransverseAxis D xAxis yAxis × ℕ) ℂ)
    (nonzero : polynomial ≠ 0) :
    0 < (fockForm D (nativePolynomial D frame xAxis yAxis polynomial)
      (nativePolynomial D frame xAxis yAxis polynomial)).re := by
  rw [transverseGram_rowGram D frame xAxis yAxis realRows] at positive
  rw [nativePolynomial_rowPolynomial D frame xAxis yAxis realRows]
  exact rowPolynomial_positive D _ positive polynomial nonzero

theorem nativePolynomial_norm_real (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (xAxis yAxis : Fin D.rank)
    (realRows : ∀ (axis : TransverseAxis D xAxis yAxis) component,
      star (frame axis.1 component) = frame axis.1 component)
    (positive : (transverseGram D frame xAxis yAxis).PosDef)
    (polynomial : MvPolynomial (TransverseAxis D xAxis yAxis × ℕ) ℂ) :
    (fockForm D (nativePolynomial D frame xAxis yAxis polynomial)
      (nativePolynomial D frame xAxis yAxis polynomial)).im = 0 := by
  rw [transverseGram_rowGram D frame xAxis yAxis realRows] at positive
  rw [nativePolynomial_rowPolynomial D frame xAxis yAxis realRows]
  exact rowPolynomial_norm_real D _ positive polynomial

theorem nativePolynomial_injective (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (xAxis yAxis : Fin D.rank)
    (realRows : ∀ (axis : TransverseAxis D xAxis yAxis) component,
      star (frame axis.1 component) = frame axis.1 component)
    (positive : (transverseGram D frame xAxis yAxis).PosDef) :
    Function.Injective (nativePolynomial D frame xAxis yAxis) := by
  rw [transverseGram_rowGram D frame xAxis yAxis realRows] at positive
  rw [nativePolynomial_rowPolynomial D frame xAxis yAxis realRows]
  exact rowPolynomial_injective D _ positive

def nativeDown (D : LatticeData) (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (beta : Charge D) (xAxis yAxis : Fin D.rank) :
    MvPolynomial (TransverseAxis D xAxis yAxis × ℕ) ℂ →ₗ[ℂ] State D where
  toFun := fun polynomial =>
    Finsupp.single beta (nativePolynomial D frame xAxis yAxis polynomial) ⊗ₜ[ℂ]
      OriginalQQuartetSource.down
  map_add' := by
    intro left right
    simp [map_add, Finsupp.single_add, TensorProduct.add_tmul]
  map_smul' := by
    intro scalar polynomial
    simp only [map_smul, ← Finsupp.smul_single, TensorProduct.smul_tmul,
      TensorProduct.tmul_smul, RingHom.id_apply]

private theorem transverse_monomial_preimage (D : LatticeData)
    (xAxis yAxis : Fin D.rank) (powers : Index D →₀ ℕ)
    (noX : ∀ frequency, powers (xAxis, frequency) = 0)
    (noY : ∀ frequency, powers (yAxis, frequency) = 0) :
    ∃ polynomial : MvPolynomial (TransverseAxis D xAxis yAxis × ℕ) ℂ,
      rename (transverseIndex D xAxis yAxis) polynomial = monomial powers 1 := by
  classical
  let embedding := transverseIndex D xAxis yAxis
  have injective := transverseIndex_injective D xAxis yAxis
  have supported : ↑powers.support ⊆ Set.range embedding := by
    rintro ⟨axis, frequency⟩ member
    have nonzero := Finsupp.mem_support_iff.mp member
    have unequalX : axis ≠ xAxis := by intro equality; subst axis; exact nonzero (noX frequency)
    have unequalY : axis ≠ yAxis := by intro equality; subst axis; exact nonzero (noY frequency)
    exact ⟨(⟨axis, unequalX, unequalY⟩, frequency), rfl⟩
  refine ⟨monomial (powers.comapDomain embedding injective.injOn) 1, ?_⟩
  rw [rename_monomial, Finsupp.mapDomain_comapDomain embedding injective powers supported]

theorem native_J_one_down (D : LatticeData)
    (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1)
    (rightGramInverse : gramComplex D * H = 1)
    (leftFrameInverse : inverse * frame = 1)
    (rightFrameInverse : frame * inverse = 1)
    (beta : Charge D) (xAxis yAxis : Fin D.rank) (level : ℤ) (state : State D)
    (member : state ∈ nativeTransverseEnergySpace D H frame inverse leftGramInverse
      rightGramInverse leftFrameInverse rightFrameInverse beta xAxis yAxis level)
    (degreeOne : LatticeBcGhostBrstGhostNumber.J D state = state) :
    ∃ polynomial, nativeDown D frame beta xAxis yAxis polynomial = state := by
  classical
  let projection : Module.End ℂ (State D) :=
    (2 : ℂ) • LinearMap.id - LatticeBcGhostBrstGhostNumber.J D
  have nativeProjection : projection state = state := by
    simp [projection, degreeOne, two_smul]
  have spanMember : state ∈ Submodule.span ℂ
      (Set.range (transverseLevelWord D frame beta xAxis yAxis level)) := by
    rw [nativeTransverseEnergySpace_span D H frame inverse leftGramInverse rightGramInverse
      leftFrameInverse rightFrameInverse]
    exact member
  have projectedRange : projection state ∈ LinearMap.range (nativeDown D frame beta xAxis yAxis) := by
    clear member degreeOne nativeProjection
    induction spanMember using Submodule.span_induction with
    | mem word rangeMember =>
        obtain ⟨index, rfl⟩ := rangeMember
        have degree := transverseLevelWord_J_degree D frame beta xAxis yAxis level index
        by_cases empty : index.1.2 = ∅
        · obtain ⟨polynomial, equality⟩ := transverse_monomial_preimage D xAxis yAxis
            index.1.1 index.2.1 index.2.2.1
          refine ⟨polynomial, ?_⟩
          simp only [projection, LinearMap.sub_apply, LinearMap.smul_apply,
            LinearMap.id_apply, degree, if_pos empty, one_smul, two_smul, add_sub_cancel_right]
          simp [nativeDown, nativePolynomial, equality, transverseLevelWord,
            nativeWord, empty, downWord]
        · simp only [projection, LinearMap.sub_apply, LinearMap.smul_apply,
            LinearMap.id_apply, degree, if_neg empty, sub_self]
          exact ⟨0, map_zero _⟩
    | zero => simpa using (Submodule.zero_mem (LinearMap.range (nativeDown D frame beta xAxis yAxis)))
    | add first second firstMember secondMember firstProof secondProof =>
        simpa only [map_add] using Submodule.add_mem _ firstProof secondProof
    | smul scalar word wordMember inductionProof =>
        simpa only [map_smul] using Submodule.smul_mem _ scalar inductionProof
  rw [nativeProjection] at projectedRange
  exact projectedRange

theorem native_degree_one_negative_C0_positive (D : LatticeData)
    (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1)
    (rightGramInverse : gramComplex D * H = 1)
    (leftFrameInverse : inverse * frame = 1)
    (rightFrameInverse : frame * inverse = 1)
    (beta : Charge D) (xAxis yAxis : Fin D.rank) (level : ℤ)
    (realRows : ∀ (axis : TransverseAxis D xAxis yAxis) component,
      star (frame axis.1 component) = frame axis.1 component)
    (positive : (transverseGram D frame xAxis yAxis).PosDef) (state : State D)
    (member : state ∈ nativeTransverseEnergySpace D H frame inverse leftGramInverse
      rightGramInverse leftFrameInverse rightFrameInverse beta xAxis yAxis level)
    (degreeOne : LatticeBcGhostBrstGhostNumber.J D state = state) (nonzero : state ≠ 0) :
    0 < (-LatticeBcGhostHermitianForm.F D state (C D 0 state)).re ∧
      (-LatticeBcGhostHermitianForm.F D state (C D 0 state)).im = 0 := by
  obtain ⟨polynomial, rfl⟩ := native_J_one_down D H frame inverse leftGramInverse
    rightGramInverse leftFrameInverse rightFrameInverse beta xAxis yAxis level state member degreeOne
  have polynomialNonzero : polynomial ≠ 0 := by
    intro zero
    rw [zero, map_zero] at nonzero
    exact nonzero rfl
  have normalization :
      -LatticeBcGhostHermitianForm.F D (nativeDown D frame beta xAxis yAxis polynomial)
        (C D 0 (nativeDown D frame beta xAxis yAxis polynomial)) =
        fockForm D (nativePolynomial D frame xAxis yAxis polynomial)
          (nativePolynomial D frame xAxis yAxis polynomial) := by
    change -LatticeBcGhostHermitianForm.F D (_ ⊗ₜ[ℂ] down) (C D 0 (_ ⊗ₜ[ℂ] down)) = _
    rw [LatticeBcGhostAuxiliarySelection.F_c0_down_normalization,
      LatticeChargedFockForms.hermitian_single, if_pos rfl, neg_neg]
  rw [normalization]
  exact ⟨nativePolynomial_positive D frame xAxis yAxis realRows positive polynomial polynomialNonzero,
    nativePolynomial_norm_real D frame xAxis yAxis realRows positive polynomial⟩

end
end D5.S3.VertexAlgebra.TransverseMetric.NativePositivity
