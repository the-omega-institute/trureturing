/- GID: D5/S3/Observer/Existence/EmpiricalReflexiveSeparation
   generality: G
   mirror-B: D5/B/S3/Observer/Existence/EmpiricalReflexiveSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Complete quantum readout coexists with failure of internal self-evaluation capture. -/

import D5.S3.Quantum.Foundation.FiniteStateChannel
import D5.S3.Quantum.PureState.PureStateHandshake
import D5.S3.Quantum.Tomography.ObserverDiagonalSeparation

/- Library-search audit trail (2026-09-04):
   * Exact repository hits `pure_state_handshake` and `complete_context_tomography`
     supply the standard rank-one projection laws and complete quantum readout.
   * Exact repository hit `escaped_of_fixedPointFree` supplies universal diagonal
     escape for every same-typed evaluation table and is applied directly.
   * Pinned Mathlib hit `Function.exists_fixed_point_of_surjective` is the abstract
     Lawvere engine; Loogle returned that same declaration. GitHub Lean search found
     no combined informational-completeness/self-description theorem.
   * The close Boolean theorem `state_faithfulness_not_self_description_closure`
     does not carry the quantum context required by the source's adjacent hypotheses. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.Existence.EmpiricalReflexiveSeparation

open scoped CStarAlgebra ComplexOrder MatrixOrder

open D5.S0.Diagonal.EscapeCount
open D5.S0.Diagonal.Lawvere.QualitativeEscape
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.PureState.PureStateHandshake
open D5.S3.Quantum.Tomography.ObserverDiagonalSeparation
open D5.S3.Quantum.Tomography.CompleteContextTomography
open D5.S3.Quantum.Tomography.RankOneContextCommutator

private theorem complex_sqrt_two_sq : (Real.sqrt 2 : Complex) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
  norm_num

private theorem complex_sqrt_two_inv_mul_self :
    (Real.sqrt 2 : Complex)⁻¹ * (Real.sqrt 2 : Complex)⁻¹ = (2 : Complex)⁻¹ := by
  have realIdentity := congrArg (fun value : Real => (value : Complex))
    TsirelsonInequality.sqrt_two_inv_mul_self
  simpa using realIdentity

private noncomputable def qubitTomographyVector :
    Fin 3 -> Fin 2 -> Fin 2 -> Complex :=
  let s : Complex := (Real.sqrt 2 : Complex)⁻¹
  ![
    ![![1, 0], ![0, 1]],
    ![![s, s], ![s, -s]],
    ![![s, Complex.I * s], ![s, -Complex.I * s]]
  ]

private theorem qubitTomographyVector_normalized (l : Fin 3) (j : Fin 2) :
    star (qubitTomographyVector l j) ⬝ᵥ qubitTomographyVector l j = 1 := by
  fin_cases l <;> fin_cases j <;>
    norm_num [qubitTomographyVector, dotProduct, Fin.sum_univ_two,
      complex_sqrt_two_inv_mul_self] <;>
    ring_nf <;>
    norm_num [pow_two, complex_sqrt_two_inv_mul_self]

private noncomputable def qubitTomographyProjector :
    Fin 3 -> Fin 2 -> Matrix (Fin 2) (Fin 2) Complex :=
  ![
    ![!![1, 0; 0, 0], !![0, 0; 0, 1]],
    ![!![1 / 2, 1 / 2; 1 / 2, 1 / 2],
      !![1 / 2, -1 / 2; -1 / 2, 1 / 2]],
    ![!![1 / 2, -Complex.I / 2; Complex.I / 2, 1 / 2],
      !![1 / 2, Complex.I / 2; -Complex.I / 2, 1 / 2]]
  ]

private theorem qubitTomographyProjector_eq_rankOneDensity
    (l : Fin 3) (j : Fin 2) :
    qubitTomographyProjector l j =
      rankOneDensity (qubitTomographyVector l j) := by
  ext i k
  fin_cases l <;> fin_cases j <;> fin_cases i <;> fin_cases k <;>
    norm_num [qubitTomographyProjector, qubitTomographyVector,
      rankOneDensity, Matrix.vecMulVec_apply,
      complex_sqrt_two_inv_mul_self] <;>
    ring_nf <;>
    norm_num [complex_sqrt_two_sq, complex_sqrt_two_inv_mul_self]

private theorem rankOneDensity_isNormalized
    (v : Fin 2 -> Complex) (hv : star v ⬝ᵥ v = 1) :
    IsNormalizedRankOneProjection (rankOneDensity v) := by
  refine ⟨?_, (pure_state_handshake v hv 0).1, ?_, ?_⟩
  · simp [rankOneDensity]
  · rw [rankOneDensity, Matrix.trace_vecMulVec, dotProduct]
    calc
      ∑ i, v i * star (v i) = ∑ i, star (v i) * v i := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 1 := hv
  · intro X
    have handshake := pure_state_handshake v hv X
    rw [handshake.2.1, handshake.2.2, Matrix.trace_mul_comm]

private noncomputable def qubitTomographyContext : Fin 3 -> RankOneContext 2 :=
  fun l =>
    { projector := qubitTomographyProjector l
      rankOne := fun j => by
        rw [qubitTomographyProjector_eq_rankOneDensity]
        exact rankOneDensity_isNormalized _ (qubitTomographyVector_normalized l j)
      resolvesIdentity := by
        ext i k
        fin_cases l <;> fin_cases i <;> fin_cases k <;>
          norm_num [qubitTomographyProjector, Fin.sum_univ_two] <;>
          ring }

private theorem qubitTomographyContext_overlap (l k : Fin 3) (j r : Fin 2) :
    Matrix.trace
        ((qubitTomographyContext l).projector j *
          (qubitTomographyContext k).projector r) =
      if l = k then (if j = r then 1 else 0) else ((2 : Nat) : Complex)⁻¹ := by
  simp only [qubitTomographyContext]
  fin_cases l <;> fin_cases k <;> fin_cases j <;> fin_cases r <;>
    norm_num [qubitTomographyProjector, Matrix.trace, Matrix.mul_apply,
      Fin.sum_univ_two] <;>
    ring_nf <;>
    norm_num [Complex.I_mul_I]

/-- QDO lines 16191-16239, proposition 32.18: an informationally complete
finite-dimensional quantum observer exists, while every internal table of
same-carrier Boolean self-evaluations misses its twisted diagonal. -/
theorem empirical_complete_reflexive_incomplete :
    ∃ context : Fin 3 -> RankOneContext 2,
      Function.Injective
          (fun rho : DensityState (Fin 2) =>
            contextReadout context (CStarMatrix.ofMatrix.symm rho.1)) ∧
        ∀ evaluation : DensityState (Fin 2) -> DensityState (Fin 2) -> Bool,
          (fun state => !(evaluation state state)) ∉ Set.range evaluation := by
  let context := qubitTomographyContext
  have hmatrix : Function.Injective (contextReadout context) := by
    intro rho sigma hreadout
    apply (complete_context_tomography context qubitTomographyContext_overlap).2.2
    intro l j
    exact congrFun (congrFun hreadout l) j
  have hdensity : Function.Injective
      (fun rho : DensityState (Fin 2) =>
        contextReadout context (CStarMatrix.ofMatrix.symm rho.1)) := by
    intro rho sigma hreadout
    apply Subtype.ext
    exact CStarMatrix.ofMatrix.symm.injective (hmatrix hreadout)
  refine ⟨context, hdensity, ?_⟩
  intro evaluation
  change IsEscaped (fun value : Bool => !value) evaluation
  exact escaped_of_fixedPointFree (fun value : Bool => !value) (by decide)
    evaluation

/- Reverse probe for CAS-A1: the public injectivity clause separates two
distinct density states on the fixed qubit carrier. -/
example :
    ∃ context : Fin 3 -> RankOneContext 2,
      ∃ rho sigma : DensityState (Fin 2),
        rho ≠ sigma ∧
          contextReadout context (CStarMatrix.ofMatrix.symm rho.1) ≠
            contextReadout context (CStarMatrix.ofMatrix.symm sigma.1) := by
  obtain ⟨context, hinjective, _⟩ := empirical_complete_reflexive_incomplete
  let rho : DensityState (Fin 2) :=
    ⟨CStarMatrix.ofMatrixStarAlgEquiv
        (rankOneDensity (qubitTomographyVector 0 0)),
      map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
        (Matrix.posSemidef_vecMulVec_self_star _).nonneg,
      by
        change Matrix.trace (rankOneDensity (qubitTomographyVector 0 0)) = 1
        simpa [rankOneDensity, Matrix.trace_vecMulVec, mul_comm] using
          qubitTomographyVector_normalized 0 0⟩
  let sigma : DensityState (Fin 2) :=
    ⟨CStarMatrix.ofMatrixStarAlgEquiv
        (rankOneDensity (qubitTomographyVector 0 1)),
      map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
        (Matrix.posSemidef_vecMulVec_self_star _).nonneg,
      by
        change Matrix.trace (rankOneDensity (qubitTomographyVector 0 1)) = 1
        simpa [rankOneDensity, Matrix.trace_vecMulVec, mul_comm] using
          qubitTomographyVector_normalized 0 1⟩
  have hstates : rho ≠ sigma := by
    intro hequal
    have hentry := congrArg
      (fun state : DensityState (Fin 2) =>
        CStarMatrix.ofMatrix.symm state.1 0 0) hequal
    change rankOneDensity (qubitTomographyVector 0 0) 0 0 =
      rankOneDensity (qubitTomographyVector 0 1) 0 0 at hentry
    norm_num [rho, sigma, rankOneDensity, qubitTomographyVector,
      Matrix.vecMulVec_apply] at hentry
  exact ⟨context, rho, sigma, hstates, fun hreadout =>
    hstates (hinjective hreadout)⟩

/- Reverse probe for CAS-A2: the public non-capture clause returns a concrete
missing self-evaluation for every proposed internal table. -/
example :
    ∀ evaluation : DensityState (Fin 2) -> DensityState (Fin 2) -> Bool,
      ∃ selfEvaluation : DensityState (Fin 2) -> Bool,
        selfEvaluation ∉ Set.range evaluation := by
  obtain ⟨_, _, hescape⟩ := empirical_complete_reflexive_incomplete
  intro evaluation
  exact ⟨fun state => !(evaluation state state), hescape evaluation⟩

#print axioms empirical_complete_reflexive_incomplete

end D5.S3.Observer.Existence.EmpiricalReflexiveSeparation
