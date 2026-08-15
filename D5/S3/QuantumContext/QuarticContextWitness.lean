/- GID: D5/S3/QuantumContext/QuarticContextWitness
   generality: G
   mirror-B: D5/B/S3/QuantumContext/QuarticContextWitness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exhibit exact qutrit contexts with distinct quartic pricing totals. -/

/- Library-search audit trail (2026-08-10):
   * Searches of pinned mathlib for qutrit contextuality, frame functions, projective contexts,
     and quartic Born weights found no theorem giving this explicit witness.
   * `Matrix.posSemidef_vecMulVec_self_star` supplies positivity of the rank-one state, and
     `D5.S3.Quantum.FiniteDimensional.bornProbability` supplies the frozen trace-weight
     interface. The local frozen rank-one Born reduction identifies its square with
     `|amp|^4`; it is not imported because the displayed rational matrices compute directly.
   * All remaining claims are exact calculations over three explicit integer rays. No sampled
     basis, numerical tolerance, Gleason theorem, or general extremal bound is asserted.
-/

import D5.S3.Quantum.FiniteDimensional

namespace D5.S3.QuantumContext.QuarticContextWitness

open D5.S3.Quantum.FiniteDimensional
open scoped BigOperators ComplexOrder

/-- Complex column vectors for a three-level system. -/
abbrev QutritVector := Fin 3 -> ℂ

/-- Complex matrices for a three-level system. -/
abbrev QutritMatrix := Matrix (Fin 3) (Fin 3) ℂ

/-- The ray with equal amplitude in all three coordinate directions. -/
def uniformRay : QutritVector := ![1, 1, 1]

/-- The three coordinate rays. -/
def standardRays : Fin 3 -> QutritVector :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]

/-- Three mutually orthogonal rays, the first of which is `uniformRay`. -/
def alignedRays : Fin 3 -> QutritVector :=
  ![uniformRay, ![1, -1, 0], ![1, 1, -2]]

/-- The coordinate rank-one projections. -/
def standardProjection : Fin 3 -> QutritMatrix :=
  ![!![1, 0, 0; 0, 0, 0; 0, 0, 0],
    !![0, 0, 0; 0, 1, 0; 0, 0, 0],
    !![0, 0, 0; 0, 0, 0; 0, 0, 1]]

/-- Rank-one projections onto the aligned rays, normalized by their squared lengths 3, 2, 6. -/
noncomputable def alignedProjection : Fin 3 -> QutritMatrix :=
  ![!![1 / 3, 1 / 3, 1 / 3; 1 / 3, 1 / 3, 1 / 3; 1 / 3, 1 / 3, 1 / 3],
    !![1 / 2, -(1 / 2), 0; -(1 / 2), 1 / 2, 0; 0, 0, 0],
    !![1 / 6, 1 / 6, -(1 / 3); 1 / 6, 1 / 6, -(1 / 3);
      -(1 / 3), -(1 / 3), 2 / 3]]

/-- The rational factors converting the three aligned integer rays into projections. -/
noncomputable def alignedRayScale : Fin 3 -> ℝ := ![1 / 3, 1 / 2, 1 / 6]

/-- The pure qutrit density matrix on the equal-amplitude ray. -/
noncomputable def uniformDensity : QutritMatrix := alignedProjection 0

/-- A finite triple of self-adjoint idempotents resolving the identity. -/
def IsProjectiveContext (context : Fin 3 -> QutritMatrix) : Prop :=
  (∀ k, star (context k) = context k ∧ context k * context k = context k) ∧
    ∑ k, context k = 1

/-- Square a projection's real Born weight; for this pure rank-one witness this is
the fourth power of the transition amplitude modulus. -/
noncomputable def quarticPrice (rho projection : QutritMatrix) : ℝ :=
  (bornProbability rho projection).re ^ 2

/-- Total quartic price assigned to the three outcomes of one complete context. -/
noncomputable def quarticContextTotal
    (rho : QutritMatrix) (context : Fin 3 -> QutritMatrix) : ℝ :=
  ∑ k, quarticPrice rho (context k)

/-- Every displayed coordinate projection is the outer product of its explicit ray. -/
theorem standard_projection_from_ray (k : Fin 3) :
    standardProjection k =
      Matrix.vecMulVec (standardRays k) (star (standardRays k)) := by
  fin_cases k <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [standardProjection, standardRays, Matrix.vecMulVec_apply]

/-- Every displayed aligned projection is the normalized outer product of its explicit ray. -/
theorem aligned_projection_from_ray (k : Fin 3) :
    alignedProjection k =
      (alignedRayScale k) • Matrix.vecMulVec (alignedRays k) (star (alignedRays k)) := by
  fin_cases k <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp only [alignedProjection, alignedRayScale, alignedRays, uniformRay,
        Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
        Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] <;> norm_num

/-- The displayed equal-amplitude density matrix is positive semidefinite with trace one. -/
theorem uniform_density_is_state :
    uniformDensity.PosSemidef ∧ Matrix.trace uniformDensity = 1 := by
  constructor
  · rw [uniformDensity, aligned_projection_from_ray]
    exact (Matrix.posSemidef_vecMulVec_self_star uniformRay).smul
      (by norm_num [alignedRayScale])
  · norm_num [uniformDensity, alignedProjection, Matrix.trace, Fin.sum_univ_succ]

/-- The coordinate projections are a complete projective qutrit context. -/
theorem standard_context_is_projective : IsProjectiveContext standardProjection := by
  constructor
  · intro k
    fin_cases k <;> constructor <;>
      ext i j <;> fin_cases i <;> fin_cases j <;>
        norm_num [standardProjection, Matrix.mul_apply, Fin.sum_univ_succ]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [standardProjection, standardRays, Matrix.one_apply,
        Fin.sum_univ_succ]

/-- The three normalized aligned-ray projections are another complete projective context. -/
theorem aligned_context_is_projective : IsProjectiveContext alignedProjection := by
  constructor
  · intro k
    fin_cases k <;> constructor <;>
      ext i j <;> fin_cases i <;> fin_cases j <;>
        norm_num [alignedProjection, Matrix.mul_apply, Fin.sum_univ_succ]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [alignedProjection, Matrix.one_apply, Fin.sum_univ_succ]

/-- The ordinary Born prices balance to one in both displayed complete contexts. -/
theorem born_control_totals :
    (∑ k, bornProbability uniformDensity (standardProjection k)) = 1 ∧
      (∑ k, bornProbability uniformDensity (alignedProjection k)) = 1 := by
  constructor <;>
    norm_num [bornProbability, uniformDensity, standardProjection, alignedProjection,
      Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.cons_val_two]

/-- In the coordinate context the three Born weights are all `1/3`, so their squares total
`1/3`. -/
theorem standard_quartic_total :
    quarticContextTotal uniformDensity standardProjection = 1 / 3 := by
  norm_num [quarticContextTotal, quarticPrice, bornProbability, uniformDensity,
    standardProjection, alignedProjection, Matrix.trace, Matrix.mul_apply,
    Fin.sum_univ_succ, Matrix.cons_val_two]

/-- In the aligned context the Born weights are `1, 0, 0`, so their squares total one. -/
theorem aligned_quartic_total :
    quarticContextTotal uniformDensity alignedProjection = 1 := by
  norm_num [quarticContextTotal, quarticPrice, bornProbability, uniformDensity,
    alignedProjection, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ,
    Matrix.cons_val_two]

/-- Exact qutrit counterexample to context-independent quartic pricing: the same normalized pure
state and two complete rank-one projective contexts give totals `1/3` and `1`, respectively. -/
theorem quartic_pricing_context_counterexample :
    quarticContextTotal uniformDensity standardProjection = 1 / 3 ∧
      quarticContextTotal uniformDensity alignedProjection = 1 ∧
      quarticContextTotal uniformDensity standardProjection <
        quarticContextTotal uniformDensity alignedProjection := by
  rw [standard_quartic_total, aligned_quartic_total]
  norm_num

end D5.S3.QuantumContext.QuarticContextWitness
