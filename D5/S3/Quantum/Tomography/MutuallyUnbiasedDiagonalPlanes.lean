/- GID: D5/S3/Quantum/Tomography/MutuallyUnbiasedDiagonalPlanes
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/MutuallyUnbiasedDiagonalPlanes
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Mutually unbiased contexts are exactly orthogonal traceless diagonal planes. -/

import D5.S3.Observer.Conditioning
import D5.S3.Quantum.Tomography.OneStepProbabilityInnovation

/- Library-search audit trail (2026-08-23):
   * Exact family hits `RankOneContext`, `overlap`, `HermitianTraceZero`,
     `centeredContextPlane`, and `Conditioning.unreadState` supply every source object.
   * Pinned Mathlib exact hits `Submodule.isOrtho_span`, `Matrix.trace_mul_comm`,
     `Matrix.trace_mul_cycle`, and the finite-sum matrix identities are applied below.
   * Repository, pinned-Mathlib, and Loogle searches found no theorem packaging the four
     equivalent clauses on the real Hermitian and trace-zero Hermitian carriers. -/

open scoped BigOperators ComplexOrder InnerProductSpace Matrix

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.MutuallyUnbiasedDiagonalPlanes

open D5.S3.Observer.Conditioning
open D5.S3.Quantum.Fibers.ReadoutOrthogonalEquivalence
open D5.S3.Quantum.Fibers.TraceZeroReadoutOrthogonalEquivalence
open D5.S3.Quantum.Tomography.OneStepProbabilityInnovation
open D5.S3.Quantum.Tomography.RankOneContextCommutator

variable {d : Nat} [NeZero d]

local instance matrixNormedAddCommGroup :
    NormedAddCommGroup (Matrix (Fin d) (Fin d) ℂ) :=
  Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one

local instance matrixInnerProductSpace :
    InnerProductSpace ℂ (Matrix (Fin d) (Fin d) ℂ) :=
  Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

local instance matrixRealInnerProductSpace :
    InnerProductSpace ℝ (Matrix (Fin d) (Fin d) ℂ) :=
  InnerProductSpace.rclikeToReal ℂ (Matrix (Fin d) (Fin d) ℂ)

local instance hermitianTraceZeroTopologicalSpace :
    TopologicalSpace (HermitianTraceZero (d := Fin d)) :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace

private theorem trace_hermitian_real
    (X : Matrix (Fin d) (Fin d) ℂ) (hX : X.IsHermitian) :
    Matrix.trace X = (Matrix.trace X).re := by
  apply Complex.ext
  · simp
  · have hstar : star (Matrix.trace X) = Matrix.trace X := by
      rw [← Matrix.trace_conjTranspose, hX.eq]
    have him := congrArg Complex.im hstar
    change (starRingEnd ℂ (Matrix.trace X)).im = _ at him
    rw [Complex.conj_im] at him
    simpa using (show (Matrix.trace X).im = 0 by linarith)

private theorem trace_overlap_real
    (B C : RankOneContext d) (j k : Fin d) :
    Matrix.trace (B.projector j * C.projector k) =
      (Matrix.trace (B.projector j * C.projector k)).re := by
  apply Complex.ext
  · simp
  · have hstar : star (Matrix.trace (B.projector j * C.projector k)) =
        Matrix.trace (B.projector j * C.projector k) := by
      calc
        star (Matrix.trace (B.projector j * C.projector k)) =
            Matrix.trace ((B.projector j * C.projector k)ᴴ) :=
          (Matrix.trace_conjTranspose _).symm
        _ = Matrix.trace (C.projector k * B.projector j) := by
          rw [Matrix.conjTranspose_mul, (B.rankOne j).1, (C.rankOne k).1]
        _ = Matrix.trace (B.projector j * C.projector k) :=
          Matrix.trace_mul_comm _ _
    have him := congrArg Complex.im hstar
    change (starRingEnd ℂ (Matrix.trace (B.projector j * C.projector k))).im = _ at him
    rw [Complex.conj_im] at him
    simpa using
      (show (Matrix.trace (B.projector j * C.projector k)).im = 0 by linarith)

private theorem matrix_inner_eq_trace_conjTranspose_mul
    (A B : Matrix (Fin d) (Fin d) ℂ) :
    inner ℂ A B = Matrix.trace (Aᴴ * B) := by
  change Matrix.trace (B * 1 * Aᴴ) = Matrix.trace (Aᴴ * B)
  rw [Matrix.mul_one, Matrix.trace_mul_comm]

private theorem centered_projector_inner
    (hd : 2 ≤ d) (B C : RankOneContext d) (j k : Fin d) :
    inner ℝ (centeredProjector B j) (centeredProjector C k) =
      overlap B C j k - (d : ℝ)⁻¹ := by
  change (inner ℂ (centeredProjector B j).1 (centeredProjector C k).1).re = _
  rw [matrix_inner_eq_trace_conjTranspose_mul]
  have hBstar : (B.projector j)ᴴ = B.projector j := (B.rankOne j).1
  have hCstar : (C.projector k)ᴴ = C.projector k := (C.rankOne k).1
  have hdComplex : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hdReal : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  simp only [centeredProjector, centeredEffect, (B.rankOne j).2.2.1,
    (C.rankOne k).2.2.1, Fintype.card_fin, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hBstar,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_one, overlap]
  rw [trace_overlap_real B C j k]
  have hstarInv : star ((d : ℂ)⁻¹) = (d : ℂ)⁻¹ := by
    rw [star_inv₀]
    simp
  have hinv : (d : ℂ)⁻¹ = (((d : ℝ)⁻¹ : ℝ) : ℂ) := by
    exact (Complex.ofReal_inv (d : ℝ)).symm
  simp only [div_eq_mul_inv, one_mul]
  rw [hstarInv, hinv]
  simp only [smul_eq_mul, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.one_re, Complex.one_im, Complex.natCast_re,
    mul_zero, zero_mul, sub_zero]
  field_simp [hdComplex, hdReal]
  ring

private theorem mutually_unbiased_iff_planes_orthogonal
    (hd : 2 ≤ d) (B C : RankOneContext d) :
    (∀ j k, overlap B C j k = (d : ℝ)⁻¹) ↔
      centeredContextPlane B ⟂ centeredContextPlane C := by
  rw [centeredContextPlane, centeredContextPlane, Submodule.isOrtho_span]
  constructor
  · intro h u hu v hv
    rcases hu with ⟨j, rfl⟩
    rcases hv with ⟨k, rfl⟩
    rw [centered_projector_inner hd B C j k, h j k, sub_self]
  · intro h j k
    have hj : centeredProjector B j ∈ Set.range (centeredProjector B) := ⟨j, rfl⟩
    have hk : centeredProjector C k ∈ Set.range (centeredProjector C) := ⟨k, rfl⟩
    have hinner := h hj hk
    rw [centered_projector_inner hd B C j k] at hinner
    linarith

private theorem dephasing_eq_sum_trace_smul
    (context : RankOneContext d) (X : Matrix (Fin d) (Fin d) ℂ) :
    unreadState context.projector X =
      ∑ j, Matrix.trace (context.projector j * X) • context.projector j := by
  unfold unreadState
  apply Finset.sum_congr rfl
  intro j _
  exact (context.rankOne j).2.2.2 X

private theorem sum_trace_projector_mul
    (context : RankOneContext d) (X : Matrix (Fin d) (Fin d) ℂ) :
    ∑ j, Matrix.trace (context.projector j * X) = Matrix.trace X := by
  calc
    ∑ j, Matrix.trace (context.projector j * X) =
        Matrix.trace ((∑ j, context.projector j) * X) := by
      rw [Finset.sum_mul, Matrix.trace_sum]
    _ = Matrix.trace X := by rw [context.resolvesIdentity, Matrix.one_mul]

private theorem complex_overlap_of_mutually_unbiased
    (hd : 2 ≤ d) (B C : RankOneContext d)
    (h : ∀ j k, overlap B C j k = (d : ℝ)⁻¹) (j k : Fin d) :
    Matrix.trace (B.projector j * C.projector k) = (d : ℂ)⁻¹ := by
  rw [trace_overlap_real B C j k]
  have hdComplex : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  apply Complex.ext
  · simpa [overlap] using h j k
  · simp

private theorem mutually_unbiased_comm
    (B C : RankOneContext d)
    (h : ∀ j k, overlap B C j k = (d : ℝ)⁻¹) :
    ∀ k j, overlap C B k j = (d : ℝ)⁻¹ := by
  intro k j
  rw [overlap, Matrix.trace_mul_comm]
  exact h j k

private theorem dephasing_composition_of_mutually_unbiased
    (hd : 2 ≤ d) (B C : RankOneContext d)
    (h : ∀ j k, overlap B C j k = (d : ℝ)⁻¹)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    unreadState B.projector (unreadState C.projector X) =
      (Matrix.trace X / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  rw [dephasing_eq_sum_trace_smul C X,
    dephasing_eq_sum_trace_smul B]
  simp_rw [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum,
    Matrix.trace_smul, smul_eq_mul,
    complex_overlap_of_mutually_unbiased hd B C h]
  simp_rw [← Finset.sum_mul, sum_trace_projector_mul C X]
  rw [← Finset.smul_sum, B.resolvesIdentity, div_eq_mul_inv]

private theorem unread_projector
    (context : RankOneContext d) (hContext : IsRecordMeasurement context.projector)
    (k : Fin d) :
    unreadState context.projector (context.projector k) = context.projector k := by
  apply (unreadState_fixed_iff hContext _).2
  intro i j hij
  by_cases hik : i = k
  · subst i
    rw [hContext.idempotent, hContext.orthogonal k j hij]
  · rw [hContext.orthogonal i k hik, Matrix.zero_mul]

private theorem trace_projector_mul_unread
    (context : RankOneContext d) (hContext : IsRecordMeasurement context.projector)
    (X : Matrix (Fin d) (Fin d) ℂ) (j : Fin d) :
    Matrix.trace (context.projector j * unreadState context.projector X) =
      Matrix.trace (context.projector j * X) := by
  classical
  rw [unreadState, Matrix.mul_sum, Matrix.trace_sum]
  calc
    ∑ k, Matrix.trace (context.projector j *
          (context.projector k * X * context.projector k)) =
        Matrix.trace (context.projector j *
          (context.projector j * X * context.projector j)) := by
      apply Finset.sum_eq_single j
      · intro k _ hkj
        rw [show context.projector j *
              (context.projector k * X * context.projector k) =
              (context.projector j * context.projector k) * X * context.projector k by
              noncomm_ring,
          hContext.orthogonal j k hkj.symm,
          Matrix.zero_mul, Matrix.zero_mul, Matrix.trace_zero]
      · simp
    _ = Matrix.trace (context.projector j * X) := by
      rw [show context.projector j *
              (context.projector j * X * context.projector j) =
              (context.projector j * context.projector j) * X * context.projector j by
              noncomm_ring,
        hContext.idempotent,
        Matrix.trace_mul_cycle, hContext.idempotent]

private theorem full_composition_implies_mutually_unbiased
    (hd : 2 ≤ d) (B C : RankOneContext d)
    (hB : IsRecordMeasurement B.projector)
    (hC : IsRecordMeasurement C.projector)
    (hFull : ∀ X : Matrix (Fin d) (Fin d) ℂ, X.IsHermitian →
      unreadState B.projector (unreadState C.projector X) =
          (Matrix.trace X / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ) ∧
        unreadState C.projector (unreadState B.projector X) =
          (Matrix.trace X / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ)) :
    ∀ j k, overlap B C j k = (d : ℝ)⁻¹ := by
  intro j k
  have hcomp := (hFull (C.projector k) (C.rankOne k).1).1
  rw [unread_projector C hC k] at hcomp
  have htrace := congrArg
    (fun Y => Matrix.trace (B.projector j * Y)) hcomp
  rw [trace_projector_mul_unread B hB] at htrace
  simp only [Matrix.mul_smul, Matrix.trace_smul,
    (B.rankOne j).2.2.1, (C.rankOne k).2.2.1, smul_eq_mul, mul_one] at htrace
  have hdComplex : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hre := congrArg Complex.re htrace
  have hreInv : (1 / (d : ℂ)).re = (d : ℝ)⁻¹ := by
    have hinv : (d : ℂ)⁻¹ = (((d : ℝ)⁻¹ : ℝ) : ℂ) := by
      exact (Complex.ofReal_inv (d : ℝ)).symm
    rw [one_div, hinv]
    simp
  rw [overlap, hre, hreInv]

private theorem unread_one
    (context : RankOneContext d) :
    unreadState context.projector (1 : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  rw [dephasing_eq_sum_trace_smul]
  simp only [Matrix.mul_one, (context.rankOne _).2.2.1, one_smul]
  exact context.resolvesIdentity

private theorem unread_add
    (context : RankOneContext d)
    (X Y : Matrix (Fin d) (Fin d) ℂ) :
    unreadState context.projector (X + Y) =
      unreadState context.projector X + unreadState context.projector Y := by
  classical
  simp [unreadState, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

private theorem unread_smul
    (context : RankOneContext d) (a : ℂ)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    unreadState context.projector (a • X) =
      a • unreadState context.projector X := by
  classical
  simp [unreadState, Finset.smul_sum]

private theorem zero_composition_of_full
    (B C : RankOneContext d)
    (hFull : ∀ X : Matrix (Fin d) (Fin d) ℂ, X.IsHermitian →
      unreadState B.projector (unreadState C.projector X) =
          (Matrix.trace X / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ) ∧
        unreadState C.projector (unreadState B.projector X) =
          (Matrix.trace X / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ)) :
    ∀ X : HermitianTraceZero (d := Fin d),
      unreadState B.projector (unreadState C.projector X.1) = 0 ∧
        unreadState C.projector (unreadState B.projector X.1) = 0 := by
  intro X
  simpa [X.2.2] using hFull X.1 X.2.1

private theorem full_composition_of_zero
    (hd : 2 ≤ d) (B C : RankOneContext d)
    (hZero : ∀ X : HermitianTraceZero (d := Fin d),
      unreadState B.projector (unreadState C.projector X.1) = 0 ∧
        unreadState C.projector (unreadState B.projector X.1) = 0) :
    ∀ X : Matrix (Fin d) (Fin d) ℂ, X.IsHermitian →
      unreadState B.projector (unreadState C.projector X) =
          (Matrix.trace X / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ) ∧
        unreadState C.projector (unreadState B.projector X) =
          (Matrix.trace X / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  intro X hX
  let r : ℝ := (Matrix.trace X).re / (d : ℝ)
  let Xzero : HermitianTraceZero (d := Fin d) :=
    ⟨X - (r : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ), by
      constructor
      · exact hX.sub (Matrix.IsHermitian.smul (by simp)
          (by rw [isSelfAdjoint_iff]; simp))
      · rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]
        simp only [Fintype.card_fin, smul_eq_mul]
        change Matrix.trace X - (r : ℂ) * (d : ℂ) = 0
        rw [trace_hermitian_real X hX]
        simp only [r, Complex.ofReal_div, Complex.ofReal_natCast]
        field_simp [show (d : ℝ) ≠ 0 by exact_mod_cast (show d ≠ 0 by omega)]
        ring⟩
  have hscalar : (r : ℂ) = Matrix.trace X / (d : ℂ) := by
    rw [trace_hermitian_real X hX]
    simp [r]
  have hdecomp : X = (r : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) + Xzero.1 := by
    dsimp [Xzero]
    abel
  have hzero := hZero Xzero
  constructor
  · rw [← hscalar, hdecomp, unread_add, unread_smul, unread_one,
      unread_add, unread_smul, unread_one, hzero.1, add_zero]
  · rw [← hscalar, hdecomp, unread_add, unread_smul, unread_one,
      unread_add, unread_smul, unread_one, hzero.2, add_zero]

/-- For two complete rank-one projective basis contexts in dimension at least two, mutual
unbiasedness, orthogonality of the real traceless diagonal planes, vanishing of both pinching
compositions on trace-zero Hermitian matrices, and complete depolarization of both compositions
on all Hermitian matrices are equivalent. -/
theorem mutually_unbiased_diagonal_planes
    (hd : 2 ≤ d) (B C : RankOneContext d)
    (hB : IsRecordMeasurement B.projector)
    (hC : IsRecordMeasurement C.projector) :
    ((∀ j k, overlap B C j k = (d : ℝ)⁻¹) ↔
        centeredContextPlane B ⟂ centeredContextPlane C) ∧
      (centeredContextPlane B ⟂ centeredContextPlane C ↔
        ∀ X : HermitianTraceZero (d := Fin d),
          unreadState B.projector (unreadState C.projector X.1) = 0 ∧
            unreadState C.projector (unreadState B.projector X.1) = 0) ∧
      ((∀ X : HermitianTraceZero (d := Fin d),
          unreadState B.projector (unreadState C.projector X.1) = 0 ∧
            unreadState C.projector (unreadState B.projector X.1) = 0) ↔
        ∀ X : Matrix (Fin d) (Fin d) ℂ, X.IsHermitian →
          unreadState B.projector (unreadState C.projector X) =
              (Matrix.trace X / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ) ∧
            unreadState C.projector (unreadState B.projector X) =
              (Matrix.trace X / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ)) ∧
      ((∀ X : Matrix (Fin d) (Fin d) ℂ, X.IsHermitian →
          unreadState B.projector (unreadState C.projector X) =
              (Matrix.trace X / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ) ∧
            unreadState C.projector (unreadState B.projector X) =
              (Matrix.trace X / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ)) ↔
        ∀ j k, overlap B C j k = (d : ℝ)⁻¹) := by
  let hMubFull : (∀ j k, overlap B C j k = (d : ℝ)⁻¹) →
      ∀ X : Matrix (Fin d) (Fin d) ℂ, X.IsHermitian →
        unreadState B.projector (unreadState C.projector X) =
            (Matrix.trace X / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ) ∧
          unreadState C.projector (unreadState B.projector X) =
            (Matrix.trace X / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
    intro h X _
    exact ⟨dephasing_composition_of_mutually_unbiased hd B C h X,
      dephasing_composition_of_mutually_unbiased hd C B
        (mutually_unbiased_comm B C h) X⟩
  let hFullMub := full_composition_implies_mutually_unbiased hd B C hB hC
  have hMubOrth := mutually_unbiased_iff_planes_orthogonal hd B C
  constructor
  · exact hMubOrth
  constructor
  · constructor
    · intro hOrth
      exact zero_composition_of_full B C (hMubFull (hMubOrth.mpr hOrth))
    · intro hZero
      exact hMubOrth.mp (hFullMub (full_composition_of_zero hd B C hZero))
  constructor
  · exact ⟨full_composition_of_zero hd B C, zero_composition_of_full B C⟩
  · exact ⟨hFullMub, hMubFull⟩

private def coordinateProjectorTwo :
    Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![1, 0; 0, 0], !![0, 0; 0, 1]]

private def coordinateContextTwo : RankOneContext 2 where
  projector := coordinateProjectorTwo
  rankOne := by
    intro j
    fin_cases j
    · refine ⟨?_, ?_, ?_, ?_⟩
      · ext i k
        fin_cases i <;> fin_cases k <;> simp [coordinateProjectorTwo]
      · ext i k
        fin_cases i <;> fin_cases k <;>
          simp [coordinateProjectorTwo, Matrix.mul_apply, Fin.sum_univ_two]
      · simp [coordinateProjectorTwo, Matrix.trace, Fin.sum_univ_two]
      · intro X
        ext i k
        fin_cases i <;> fin_cases k <;>
          simp [coordinateProjectorTwo, Matrix.mul_apply, Matrix.trace,
            Matrix.vecMul, Fin.sum_univ_two]
    · refine ⟨?_, ?_, ?_, ?_⟩
      · ext i k
        fin_cases i <;> fin_cases k <;> simp [coordinateProjectorTwo]
      · ext i k
        fin_cases i <;> fin_cases k <;>
          simp [coordinateProjectorTwo, Matrix.mul_apply, Fin.sum_univ_two]
      · simp [coordinateProjectorTwo, Matrix.trace, Fin.sum_univ_two]
      · intro X
        ext i k
        fin_cases i <;> fin_cases k <;>
          simp [coordinateProjectorTwo, Matrix.mul_apply, Matrix.trace,
            Matrix.vecMul, Fin.sum_univ_two]
  resolvesIdentity := by
    ext i k
    fin_cases i <;> fin_cases k <;>
      simp [coordinateProjectorTwo, Fin.sum_univ_two]

private theorem coordinateContextTwo_record :
    IsRecordMeasurement coordinateContextTwo.projector := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    fin_cases j <;>
      ext i k <;> fin_cases i <;> fin_cases k <;> simp [coordinateContextTwo,
        coordinateProjectorTwo]
  · intro j
    exact (coordinateContextTwo.rankOne j).2.1
  · intro j k hjk
    fin_cases j <;> fin_cases k
    · simp at hjk
    · ext i l
      fin_cases i <;> fin_cases l <;>
        simp [coordinateContextTwo, coordinateProjectorTwo, Matrix.mul_apply,
          Fin.sum_univ_two]
    · ext i l
      fin_cases i <;> fin_cases l <;>
        simp [coordinateContextTwo, coordinateProjectorTwo, Matrix.mul_apply,
          Fin.sum_univ_two]
    · simp at hjk
  · exact coordinateContextTwo.resolvesIdentity

/- The two coordinate projectors give a nontrivial dimension-two witness that all public
hypotheses are jointly satisfiable. -/
example : ∃ B C : RankOneContext 2,
    IsRecordMeasurement B.projector ∧ IsRecordMeasurement C.projector := by
  exact ⟨coordinateContextTwo, coordinateContextTwo,
    coordinateContextTwo_record, coordinateContextTwo_record⟩

#print axioms mutually_unbiased_diagonal_planes

end D5.S3.Quantum.Tomography.MutuallyUnbiasedDiagonalPlanes
