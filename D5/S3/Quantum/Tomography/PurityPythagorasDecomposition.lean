/- GID: D5/S3/Quantum/Tomography/PurityPythagorasDecomposition
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/PurityPythagorasDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Assuming pairwise orthogonal contexts, purity excess splits with residual mass. -/

import D5.S3.Quantum.Measurement.BasisMeasurementProjection
import D5.S3.Quantum.Fibers.TraceZeroReadoutOrthogonalEquivalence

open scoped BigOperators ComplexOrder InnerProductSpace Matrix

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.PurityPythagorasDecomposition

open D5.S3.Quantum.Measurement.BasisMeasurementProjection
open D5.S3.Observer.Conditioning
open D5.S3.Quantum.Tomography.RankOneContextCommutator

attribute [local instance]
  D5.S3.Quantum.Measurement.BasisMeasurementProjection.matrixNormedAddCommGroup
  D5.S3.Quantum.Measurement.BasisMeasurementProjection.matrixComplexInnerProductSpace
  D5.S3.Quantum.Measurement.BasisMeasurementProjection.matrixRealInnerProductSpace

/-- A normalized positive matrix, centered at the maximally mixed state, as a concrete
trace-zero Hermitian vector. -/
def centeredDensity {d : Nat} [NeZero d]
    (rho : Matrix (Fin d) (Fin d) ℂ)
    (hrho : rho.PosSemidef ∧ Matrix.trace rho = 1) : traceZeroHermitian d := by
  refine ⟨⟨rho - ((d : ℂ)⁻¹) • 1, ?_⟩, ?_⟩
  · change (rho - ((d : ℂ)⁻¹) • 1)ᴴ = rho - ((d : ℂ)⁻¹) • 1
    exact (hrho.1.isHermitian.sub
      (Matrix.IsHermitian.smul (by simp) (by rw [isSelfAdjoint_iff]; simp))).eq
  · change Matrix.trace (rho - ((d : ℂ)⁻¹) • 1) = 0
    simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, hrho.2,
      Fintype.card_fin, smul_eq_mul]
    field_simp [show (d : ℂ) ≠ 0 by exact_mod_cast NeZero.ne d]
    ring

theorem matrix_inner_eq_trace_conjTranspose_mul
    {d : Nat}
    (A C : Matrix (Fin d) (Fin d) ℂ) :
    inner ℂ A C = Matrix.trace (Aᴴ * C) := by
  change Matrix.trace (C * 1 * Aᴴ) = Matrix.trace (Aᴴ * C)
  rw [Matrix.mul_one, Matrix.trace_mul_comm]

/-- Sum of the underlying matrices of all visible trace-zero measurement projections. -/
def visibleMatrix {d : Nat} [NeZero d] {L : Type*} [Fintype L]
    (context : L -> RankOneContext d)
    (hRecord : ∀ l, IsRecordMeasurement (context l).projector)
    (state : traceZeroHermitian d) : Matrix (Fin d) (Fin d) ℂ :=
  ∑ l, (traceZeroBasisMeasurement (context l) (hRecord l) state).1.1

/-- The component left after subtracting all mutually orthogonal visible projections. -/
def residualVector {d : Nat} [NeZero d] {L : Type*} [Fintype L]
    (context : L -> RankOneContext d)
    (hRecord : ∀ l, IsRecordMeasurement (context l).projector)
    (state : traceZeroHermitian d) : Matrix (Fin d) (Fin d) ℂ :=
  state.1.1 - visibleMatrix context hRecord state

/-- Squared Hilbert--Schmidt mass of the component orthogonal to every visible image. -/
def purityResidual {d : Nat} [NeZero d] {L : Type*} [Fintype L]
    (context : L -> RankOneContext d)
    (hRecord : ∀ l, IsRecordMeasurement (context l).projector)
    (state : traceZeroHermitian d) : ℝ :=
  ‖residualVector context hRecord state‖ ^ 2

/-- Born probability for an outcome of a complete rank-one context. -/
def basisProbability {d : Nat} [NeZero d]
    (rho : Matrix (Fin d) (Fin d) ℂ) (context : RankOneContext d)
    (j : Fin d) : ℝ :=
  (Matrix.trace (rho * context.projector j)).re

theorem trace_mul_real_of_hermitian
    {d : Nat} (A C : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) (hC : C.IsHermitian) :
    Matrix.trace (A * C) = ((Matrix.trace (A * C)).re : ℂ) := by
  have hstar : star (Matrix.trace (A * C)) = Matrix.trace (A * C) := by
    calc
      star (Matrix.trace (A * C)) = Matrix.trace ((A * C)ᴴ) :=
        (Matrix.trace_conjTranspose _).symm
      _ = Matrix.trace (C * A) := by
        rw [Matrix.conjTranspose_mul, hA.eq, hC.eq]
      _ = Matrix.trace (A * C) := Matrix.trace_mul_comm _ _
  apply Complex.ext
  · simp
  · have him := congrArg Complex.im hstar
    change (starRingEnd ℂ (Matrix.trace (A * C))).im = _ at him
    rw [Complex.conj_im] at him
    simpa using (show (Matrix.trace (A * C)).im = 0 by linarith)

/-- Removing the scalar trace component subtracts exactly its squared Hilbert--Schmidt mass. -/
theorem centered_hermitian_norm_sq
    {d : Nat} [NeZero d] (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian) :
    ‖H - (H.trace / (d : ℂ)) • 1‖ ^ 2 =
      (H * H).trace.re - (H.trace.re) ^ 2 / (d : ℝ) := by
  have hreal : H.trace = (H.trace.re : ℂ) := by
    simpa only [Matrix.mul_one] using trace_mul_real_of_hermitian H 1 hH Matrix.isHermitian_one
  have hCentered : (H - (H.trace / (d : ℂ)) • 1).IsHermitian := by
    have h :=
      (D5.S3.Quantum.Fibers.TraceZeroReadoutOrthogonalEquivalence.centered_effect_mem H hH).1
    change (H - (H.trace / (Fintype.card (Fin d) : ℂ)) • 1).IsHermitian at h
    simpa only [Fintype.card_fin] using h
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ),
    matrix_inner_eq_trace_conjTranspose_mul, hCentered.eq]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Matrix.one_mul, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  rw [hreal]
  rw [show (d : ℂ) = ((d : ℝ) : ℂ) by simp]
  simp only [RCLike.re_eq_complex_re, ← Complex.ofReal_div, ← Complex.ofReal_mul,
    Complex.sub_re, Complex.ofReal_re]
  field_simp [show (d : ℝ) ≠ 0 by exact_mod_cast NeZero.ne d]
  ring_nf
  simp

private theorem centered_density_norm_sq
    {d : Nat} [NeZero d]
    (rho : Matrix (Fin d) (Fin d) ℂ)
    (hrho : rho.PosSemidef ∧ Matrix.trace rho = 1) :
    ‖(centeredDensity rho hrho).1.1‖ ^ 2 =
      (Matrix.trace (rho * rho)).re - (d : ℝ)⁻¹ := by
  change ‖rho - (d : ℂ)⁻¹ • 1‖ ^ 2 = _
  have h := centered_hermitian_norm_sq rho hrho.1.isHermitian
  simpa only [hrho.2, one_div, Complex.one_re, one_pow] using h

private theorem centered_measurement_eq_probability_sum
    {d : Nat} [NeZero d]
    (rho : Matrix (Fin d) (Fin d) ℂ)
    (hrho : rho.PosSemidef ∧ Matrix.trace rho = 1)
    (context : RankOneContext d)
    (hRecord : IsRecordMeasurement context.projector) :
    (traceZeroBasisMeasurement context hRecord (centeredDensity rho hrho)).1.1 =
      ∑ j, (((basisProbability rho context j - (d : ℝ)⁻¹ : ℝ) : ℂ) •
        context.projector j) := by
  classical
  change unreadState context.projector (rho - ((d : ℂ)⁻¹) • 1) = _
  rw [unreadState]
  apply Finset.sum_congr rfl
  intro j _
  rw [(context.rankOne j).2.2.2]
  apply congrArg (fun z : ℂ => z • context.projector j)
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub,
    Matrix.trace_smul, Matrix.trace_mul_comm]
  rw [trace_mul_real_of_hermitian rho (context.projector j)
    hrho.1.isHermitian (context.rankOne j).1]
  rw [(context.rankOne j).2.2.1]
  have hinv : (d : ℂ)⁻¹ = (((d : ℝ)⁻¹ : ℝ) : ℂ) := by
    exact (Complex.ofReal_inv (d : ℝ)).symm
  rw [hinv]
  simp [basisProbability]

private theorem basis_projector_inner
    {d : Nat} [NeZero d]
    (context : RankOneContext d)
    (hRecord : IsRecordMeasurement context.projector) (i j : Fin d) :
    inner ℂ (context.projector i) (context.projector j) =
      if i = j then 1 else 0 := by
  rw [matrix_inner_eq_trace_conjTranspose_mul, (context.rankOne i).1]
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, hRecord.idempotent, (context.rankOne i).2.2.1]
  · rw [if_neg hij, hRecord.orthogonal i j hij, Matrix.trace_zero]

/-- The squared norm of a real linear combination of the orthonormal basis projectors. -/
private theorem projector_sum_norm_sq
    {d : Nat} [NeZero d] (context : RankOneContext d)
    (hRecord : IsRecordMeasurement context.projector) (c : Fin d → ℝ) :
    ‖∑ j, (c j : ℂ) • context.projector j‖ ^ 2 = ∑ j, (c j) ^ 2 := by
  classical
  have hOrthonormal : Orthonormal ℂ context.projector :=
    orthonormal_iff_ite.mpr (basis_projector_inner context hRecord)
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)]
  simpa [← pow_two, ← Complex.ofReal_pow] using congrArg Complex.re
    (hOrthonormal.inner_sum (fun j => (c j : ℂ)) (fun j => (c j : ℂ)) Finset.univ)


/-- The energy of a trace-zero measurement is the sum of its squared trace coordinates. -/
theorem traceZero_measurement_norm_sq
    {d : Nat} [NeZero d] (context : RankOneContext d)
    (hRecord : IsRecordMeasurement context.projector) (X : traceZeroHermitian d) :
    ‖(traceZeroBasisMeasurement context hRecord X).1.1‖ ^ 2 =
      ∑ j, ((X.1.1 * context.projector j).trace.re) ^ 2 := by
  change ‖unreadState context.projector X.1.1‖ ^ 2 = _
  have hExpansion : unreadState context.projector X.1.1 =
      ∑ j, (((X.1.1 * context.projector j).trace.re : ℝ) : ℂ) •
        context.projector j := by
    have h := congrArg (fun A : HermitianSpace d => A.1)
      (basis_measurement_eq_projector_sum context X.1)
    simp only [basisMeasurement_val, Submodule.coe_sum, Submodule.coe_smul,
      basisProjector_val] at h
    refine h.trans ?_
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.trace_mul_comm]
    exact algebra_compatible_smul ℂ _ _
  rw [hExpansion]
  exact projector_sum_norm_sq context hRecord _

private theorem centered_measurement_norm_sq
    {d : Nat} [NeZero d]
    (rho : Matrix (Fin d) (Fin d) ℂ)
    (hrho : rho.PosSemidef ∧ Matrix.trace rho = 1)
    (context : RankOneContext d)
    (hRecord : IsRecordMeasurement context.projector) :
    ‖(traceZeroBasisMeasurement context hRecord (centeredDensity rho hrho)).1.1‖ ^ 2 =
      ∑ j, (basisProbability rho context j - (d : ℝ)⁻¹) ^ 2 := by
  rw [centered_measurement_eq_probability_sum rho hrho context hRecord]
  exact projector_sum_norm_sq context hRecord _

/-- Pairwise orthogonality of the ranges of the concrete basis-measurement projections. -/
def PairwiseOrthogonalMeasurements {d : Nat} [NeZero d]
    {L : Type*} [Fintype L] (context : L -> RankOneContext d)
    (hRecord : ∀ l, IsRecordMeasurement (context l).projector) : Prop :=
  ∀ l k, l ≠ k → ∀ x y,
    inner ℝ (traceZeroBasisMeasurement (context l) (hRecord l) x).1.1
      (traceZeroBasisMeasurement (context k) (hRecord k) y).1.1 = 0

/-- Subtracting all pairwise orthogonal measurement projections leaves a vector orthogonal to
the image of every visible projection, so its norm is genuinely complementary mass. -/
theorem measurement_inner_residualVector
    {d : Nat} [NeZero d] {L : Type*} [Fintype L]
    (context : L -> RankOneContext d)
    (hRecord : ∀ l, IsRecordMeasurement (context l).projector)
    (hOrtho : PairwiseOrthogonalMeasurements context hRecord)
    (state x : traceZeroHermitian d) (l : L) :
    inner ℝ (traceZeroBasisMeasurement (context l) (hRecord l) x).1.1
      (residualVector context hRecord state) = 0 := by
  classical
  let P := fun k => traceZeroBasisMeasurement (context k) (hRecord k)
  let component := fun k => (P k state).1.1
  have hProjection :=
    (trace_zero_basis_measurement_is_orthogonal_projection
      (context l) (hRecord l)).1
  have hIdempotent : P l (P l state) = P l state := by
    have hEq := congrArg
      (fun f : Module.End ℝ (traceZeroHermitian d) => f state)
      hProjection.isIdempotentElem.eq
    simpa only [Module.End.mul_apply] using hEq
  have hSelfSubtype :
      inner ℝ (P l x) state = inner ℝ (P l x) (P l state) := by
    calc
      inner ℝ (P l x) state = inner ℝ x (P l state) :=
        hProjection.isSymmetric x state
      _ = inner ℝ x (P l (P l state)) := by rw [hIdempotent]
      _ = inner ℝ (P l x) (P l state) :=
        (hProjection.isSymmetric x (P l state)).symm
  have hSelf :
      inner ℝ (P l x).1.1 state.1.1 =
        inner ℝ (P l x).1.1 (component l) := by
    exact hSelfSubtype
  have hSumTerms :
      ∑ k, inner ℝ (P l x).1.1 (component k) =
        inner ℝ (P l x).1.1 (component l) := by
    apply Finset.sum_eq_single l
    · intro k _ hkl
      exact hOrtho l k hkl.symm x state
    · simp
  change inner ℝ (P l x).1.1
    (state.1.1 - ∑ k, component k) = 0
  rw [inner_sub_right]
  rw [inner_sum Finset.univ component (P l x).1.1]
  rw [hSumTerms, hSelf, sub_self]

/-- Pairwise orthogonal measurement projections split every trace-zero Hermitian matrix. -/
theorem traceZero_context_pythagoras
    {d : Nat} [NeZero d] {L : Type*} [Fintype L]
    (context : L → RankOneContext d)
    (hRecord : ∀ l, IsRecordMeasurement (context l).projector)
    (hOrtho : PairwiseOrthogonalMeasurements context hRecord)
    (state : traceZeroHermitian d) :
    ‖state.1.1‖ ^ 2 =
      (∑ l, ‖(traceZeroBasisMeasurement (context l) (hRecord l) state).1.1‖ ^ 2) +
        ‖residualVector context hRecord state‖ ^ 2 := by
  classical
  let P := fun l => traceZeroBasisMeasurement (context l) (hRecord l)
  let component := fun l => (P l state).1.1
  let visible := ∑ l, component l
  let residual := state.1.1 - visible
  have hComponentResidual (l : L) : inner ℝ (component l) residual = 0 := by
    change inner ℝ (P l state).1.1
      (residualVector context hRecord state) = 0
    exact measurement_inner_residualVector context hRecord hOrtho state state l
  have hNormFinset : ∀ s : Finset L,
      ‖∑ l ∈ s, component l‖ ^ 2 = ∑ l ∈ s, ‖component l‖ ^ 2 := by
    let range := fun l => LinearMap.range (P l)
    have hFamily : OrthogonalFamily ℝ (fun l => range l)
        (fun l => (range l).subtypeₗᵢ) := by
      rintro l k hlk ⟨_, x, rfl⟩ ⟨_, y, rfl⟩
      exact hOrtho l k hlk x y
    intro s
    simpa only [Submodule.coe_subtypeₗᵢ, Submodule.subtype_apply,
      Submodule.coe_norm, Submodule.coe_sum] using
      hFamily.norm_sum (fun l => ⟨P l state, ⟨state, rfl⟩⟩) s
  have hVisibleNorm :
      ‖visible‖ ^ 2 = ∑ l, ‖component l‖ ^ 2 := by
    simpa only [visible] using hNormFinset Finset.univ
  have hVisibleResidual :
      inner ℝ visible residual = 0 := by
    dsimp only [visible]
    rw [sum_inner Finset.univ component residual]
    apply Finset.sum_eq_zero
    intro l _
    exact hComponentResidual l
  have hSplit : visible + residual = state := by
    dsimp only [residual]
    abel
  have hResidualEq : residual = residualVector context hRecord state := by
    rfl
  calc
    ‖state.1.1‖ ^ 2 = ‖visible + residual‖ ^ 2 := by rw [hSplit]
    _ = ‖visible‖ ^ 2 + ‖residual‖ ^ 2 := by
      simpa only [pow_two] using
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hVisibleResidual
    _ = _ := by rw [hVisibleNorm, hResidualEq]

/-- Pairwise orthogonal basis contexts split a normalized density matrix's purity excess into
their centered Born-probability energies and the remaining orthogonal-complement mass. -/
theorem purity_pythagoras_decomposition
    {d : Nat} [NeZero d] {L : Type*} [Fintype L]
    (context : L -> RankOneContext d)
    (hRecord : ∀ l, IsRecordMeasurement (context l).projector)
    (rho : Matrix (Fin d) (Fin d) ℂ)
    (hrho : rho.PosSemidef ∧ Matrix.trace rho = 1)
    (hOrtho : PairwiseOrthogonalMeasurements context hRecord) :
    (Matrix.trace (rho * rho)).re - (d : ℝ)⁻¹ =
      (∑ l, ∑ j, (basisProbability rho (context l) j - (d : ℝ)⁻¹) ^ 2) +
        purityResidual context hRecord (centeredDensity rho hrho) := by
  rw [← centered_density_norm_sq rho hrho,
    traceZero_context_pythagoras context hRecord hOrtho]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  exact centered_measurement_norm_sq rho hrho (context l) (hRecord l)

example :
    purityResidual (Fin.elim0 : Fin 0 -> RankOneContext 1)
      (fun l : Fin 0 => Fin.elim0 l) (0 : traceZeroHermitian 1) = 0 := by
  simp [purityResidual, residualVector, visibleMatrix]

#print axioms purity_pythagoras_decomposition

end D5.S3.Quantum.Tomography.PurityPythagorasDecomposition
