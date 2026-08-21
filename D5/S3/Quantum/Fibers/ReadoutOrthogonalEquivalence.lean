/- GID: D5/S3/Quantum/Fibers/ReadoutOrthogonalEquivalence
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/ReadoutOrthogonalEquivalence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite matrix readout fibers equal centered-effect residual and projection fibers. -/

import D5.S3.Quantum.Algebra.FutureWordOrthogonalResidual
import D5.S3.Quantum.Fibers.PhysicalFiber

/- Library-search audit trail (2026-08-21):
   * Repository search found the exact expectation-word/residual/projection equivalences in
     `D5.S3.Quantum.Algebra.FutureWordOrthogonalResidual`; they are applied directly below.
   * Pinned-Mathlib searches found no packaged matrix theorem with all four clauses. Exact hits
     `Matrix.trace_mul_comm`, `Matrix.trace_sub`, `Matrix.toMatrixNormedAddCommGroup`, and
     `Matrix.toMatrixInnerProductSpace` supply the trace pairing and matrix Hilbert structure.
   * Exact atom-id and theorem-name searches found no existing deposit. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace Matrix

namespace D5.S3.Quantum.Fibers.ReadoutOrthogonalEquivalence

open D5.S3.Quantum.Algebra.FutureWordOrthogonalResidual

variable {n : Type*} [Fintype n] [Nonempty n] [DecidableEq n]

local instance matrixNormedAddCommGroup : NormedAddCommGroup (Matrix n n ℂ) :=
  Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one

local instance matrixInnerProductSpace : InnerProductSpace ℂ (Matrix n n ℂ) :=
  Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

/-- The trace-one state coordinate centered at the maximally mixed matrix. -/
def centeredState (rho : Matrix n n ℂ) : Matrix n n ℂ :=
  rho - ((Fintype.card n : ℂ)⁻¹) • 1

/-- An accessible effect with its scalar trace component removed. -/
def centeredEffect (effect : Matrix n n ℂ) : Matrix n n ℂ :=
  effect - (Matrix.trace effect / (Fintype.card n : ℂ)) • 1

/-- The finite readout assembled from trace expectations against accessible effects. -/
def finiteTraceReadout {m : ℕ} (effect : Fin (m + 1) → Matrix n n ℂ)
    (rho : Matrix n n ℂ) : Fin (m + 1) → ℂ :=
  fun i => Matrix.trace (rho * effect i)

omit [Nonempty n] in
private lemma matrix_inner_eq_trace_conjTranspose_mul (A B : Matrix n n ℂ) :
    ⟪A, B⟫_ℂ = Matrix.trace (Aᴴ * B) := by
  change Matrix.trace (B * 1 * Aᴴ) = Matrix.trace (Aᴴ * B)
  rw [mul_one, Matrix.trace_mul_comm]

omit [Nonempty n] in
private lemma matrix_inner_eq_trace_mul_of_hermitian (A B : Matrix n n ℂ)
    (hA : A.IsHermitian) :
    ⟪A, B⟫_ℂ = Matrix.trace (A * B) := by
  rw [matrix_inner_eq_trace_conjTranspose_mul, hA.eq]

omit [Nonempty n] in
private lemma centered_state_sub (rho sigma : Matrix n n ℂ) :
    centeredState rho - centeredState sigma = rho - sigma := by
  simp [centeredState, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

omit [Nonempty n] in
private lemma trace_sub_mul_centered_effect (rho sigma effect : Matrix n n ℂ)
    (htraceRho : Matrix.trace rho = 1) (htraceSigma : Matrix.trace sigma = 1) :
    Matrix.trace ((rho - sigma) * centeredEffect effect) =
      Matrix.trace ((rho - sigma) * effect) := by
  rw [centeredEffect, mul_sub, Matrix.trace_sub]
  have hzero : Matrix.trace (rho - sigma) = 0 := by
    rw [Matrix.trace_sub, htraceRho, htraceSigma, sub_self]
  simp [hzero]

/-- Equality of finite trace readouts is equivalent successively to vanishing of every effect
pairing, membership of the centered-state difference in the invisible residual, and equality of
the visible orthogonal projections. -/
theorem readout_fiber_orthogonal_equivalence {m : ℕ}
    (effect : Fin (m + 1) → Matrix n n ℂ)
    (rho sigma : Matrix n n ℂ)
    (hrho : rho.PosSemidef ∧ Matrix.trace rho = 1)
    (hsigma : sigma.PosSemidef ∧ Matrix.trace sigma = 1)
    (_hEffects : ∀ i, (effect i).PosSemidef ∧ (1 - effect i).PosSemidef) :
    (finiteTraceReadout effect rho = finiteTraceReadout effect sigma ↔
        ∀ i, Matrix.trace ((rho - sigma) * effect i) = 0) ∧
      ((∀ i, Matrix.trace ((rho - sigma) * effect i) = 0) ↔
        centeredState rho - centeredState sigma ∈
          futureResidual (𝕜 := ℂ) (fun i => centeredEffect (effect i))) ∧
      (centeredState rho - centeredState sigma ∈
          futureResidual (𝕜 := ℂ) (fun i => centeredEffect (effect i)) ↔
        (visibleEffectSubspace (𝕜 := ℂ) (fun i => centeredEffect (effect i))).starProjection
              (centeredState rho) =
          (visibleEffectSubspace (𝕜 := ℂ) (fun i => centeredEffect (effect i))).starProjection
              (centeredState sigma)) := by
  classical
  let centeredEffects : Fin (m + 1) → Matrix n n ℂ :=
    fun i => centeredEffect (effect i)
  have hcanonical :=
    future_word_orthogonal_residual
      (𝕜 := ℂ) (E := Matrix n n ℂ) (State := Matrix n n ℂ)
      centeredEffects centeredState rho sigma
  have hhermitian : (rho - sigma).IsHermitian :=
    hrho.1.isHermitian.sub hsigma.1.isHermitian
  have htrace_iff_word :
      (∀ i, Matrix.trace ((rho - sigma) * effect i) = 0) ↔
        futureExpectationWord (𝕜 := ℂ) centeredEffects centeredState rho =
          futureExpectationWord (𝕜 := ℂ) centeredEffects centeredState sigma := by
    constructor
    · intro htrace
      funext i
      have hcentered :
          Matrix.trace ((rho - sigma) * centeredEffect (effect i)) = 0 := by
        rw [trace_sub_mul_centered_effect rho sigma (effect i) hrho.2 hsigma.2]
        exact htrace i
      have hinner : ⟪rho - sigma, centeredEffect (effect i)⟫_ℂ = 0 := by
        rw [matrix_inner_eq_trace_mul_of_hermitian _ _ hhermitian]
        exact hcentered
      rw [← centered_state_sub rho sigma] at hinner
      simpa only [futureExpectationWord, centeredEffects, inner_sub_left, sub_eq_zero] using hinner
    · intro hword i
      have hinner :
          ⟪centeredState rho - centeredState sigma, centeredEffect (effect i)⟫_ℂ = 0 := by
        have hi := congrFun hword i
        simpa only [futureExpectationWord, centeredEffects, inner_sub_left, sub_eq_zero] using hi
      rw [centered_state_sub rho sigma] at hinner
      rw [matrix_inner_eq_trace_mul_of_hermitian _ _ hhermitian] at hinner
      rw [trace_sub_mul_centered_effect rho sigma (effect i) hrho.2 hsigma.2] at hinner
      exact hinner
  constructor
  · constructor
    · intro hreadout i
      have hi := congrFun hreadout i
      simpa only [finiteTraceReadout, sub_mul, Matrix.trace_sub, sub_eq_zero] using hi
    · intro htrace
      funext i
      have hi := htrace i
      simpa only [finiteTraceReadout, sub_mul, Matrix.trace_sub, sub_eq_zero] using hi
  constructor
  · exact htrace_iff_word.trans hcanonical.1
  · exact hcanonical.2

#print axioms readout_fiber_orthogonal_equivalence

end D5.S3.Quantum.Fibers.ReadoutOrthogonalEquivalence
