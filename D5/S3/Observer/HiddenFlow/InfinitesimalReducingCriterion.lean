/- GID: D5/S3/Observer/HiddenFlow/InfinitesimalReducingCriterion
   generality: G
   mirror-B: D5/B/S3/Observer/HiddenFlow/InfinitesimalReducingCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: For finite complex matrices and U_t = exp(-itH), generator commutation is equivalent to whole-flow commutation and to both complementary blocks reducing every propagator. -/

import D5.S3.Observer.HiddenFlow.VisibleHiddenProjectionCriteria
import D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow

/- Library-search audit trail (2026-08-24):
   * `rg -n -F 'infinitesimal_reducing_criterion' D5 Golden/Frozen/accepted`
     returned no public or private hit.
   * All eight modules currently present in `D5/S3/Observer/HiddenFlow/` were checked by
     digest. `VisibleHiddenProjectionCriteria` is the one-step algebraic precursor; the
     other seven concern rigidity, recurrent orbits, or streamline conservation.
   * Repository searches for Hamiltonian flow and projection commutation found
     `ProjectionProbabilityFlow`. Its public `hamiltonianGenerator` and
     `hamiltonianPropagator` are reused; its derivative helpers are private.
   * Pinned Mathlib searches found `Commute.exp_left`, `hasDerivAt_exp_smul_const`,
     `HasDerivAt.unique`, `Matrix.toLin'_mul`, and `LinearMap.toMatrix'_comp`.
   * No packaged theorem equating generator commutation, whole-flow commutation, and
     reducing complementary subspaces was found, so the proof combines those primitives
     with the public one-step `reducing_iff_cross_projection_blocks_eq_zero` theorem.
 -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix NormedSpace

namespace D5.S3.Observer.HiddenFlow.InfinitesimalReducingCriterion

open D5.S3.Observer.HiddenFlow.VisibleHiddenProjectionCriteria
open D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow

variable {n : Type*} [Fintype n] [DecidableEq n]

local instance (priority := 2000) : NormedAddCommGroup (Matrix n n ℂ) :=
  Matrix.instL2OpNormedAddCommGroup

local instance (priority := 2000) : NormedSpace ℂ (Matrix n n ℂ) :=
  Matrix.instL2OpNormedSpace

local instance (priority := 2000) : NormedRing (Matrix n n ℂ) :=
  Matrix.instL2OpNormedRing

local instance (priority := 2000) : NormedAlgebra ℂ (Matrix n n ℂ) :=
  Matrix.instL2OpNormedAlgebra

/-- The standard-basis matrix of the projection onto `V` along its complement `R`. -/
def visibleProjectionMatrix (V R : Submodule ℂ (n → ℂ)) (h : IsCompl V R) :
    Matrix n n ℂ :=
  LinearMap.toMatrix' (visibleProjection V R h)

/-- A matrix commutes with a complementary projection exactly when it preserves both blocks. -/
theorem commutes_visibleProjectionMatrix_iff_reducing
    (V R : Submodule ℂ (n → ℂ)) (h : IsCompl V R) (T : Matrix n n ℂ) :
    T * visibleProjectionMatrix V R h = visibleProjectionMatrix V R h * T ↔
      IsReducing (Matrix.toLin' T) V R := by
  let A := Matrix.toLin' T
  let P := visibleProjection V R h
  let Q := hiddenProjection V R h
  have hPMatrix : Matrix.toLin' (visibleProjectionMatrix V R h) = P := by
    simp [visibleProjectionMatrix, P]
  have hPIdempotent : P * P = P := by
    simpa only [P, visibleProjection, IsIdempotentElem] using
      Submodule.isIdempotentElem_projection h
  have hQ : Q = 1 - P := by
    simpa [Q, P] using hiddenProjection_eq_one_sub_visibleProjection V R h
  constructor
  · intro hComm
    have hCommLin := congrArg Matrix.toLin' hComm
    simp only [Matrix.toLin'_mul, hPMatrix] at hCommLin
    have hAP : A * P = P * A := by
      simpa only [Module.End.mul_eq_comp, A] using hCommLin
    apply (reducing_iff_cross_projection_blocks_eq_zero V R h _).mpr
    change P ∘ₗ A ∘ₗ Q = 0 ∧ Q ∘ₗ A ∘ₗ P = 0
    simp only [← Module.End.mul_eq_comp]
    have hPAFixed : P * A = P * (A * P) := by
      calc
        P * A = (P * P) * A := by rw [hPIdempotent]
        _ = P * (P * A) := mul_assoc P P A
        _ = P * (A * P) := congrArg (fun B => P * B) hAP.symm
    have hAPFixed : A * P = P * (A * P) := hAP.trans hPAFixed
    rw [hQ]
    constructor
    · simp only [mul_sub, mul_one]
      exact sub_eq_zero.mpr hPAFixed
    · simp only [sub_mul, one_mul]
      exact sub_eq_zero.mpr hAPFixed
  · intro hReducing
    have hCross :=
      (reducing_iff_cross_projection_blocks_eq_zero V R h _).mp hReducing
    change P ∘ₗ A ∘ₗ Q = 0 ∧ Q ∘ₗ A ∘ₗ P = 0 at hCross
    simp only [← Module.End.mul_eq_comp] at hCross
    rw [hQ] at hCross
    have hPA : P * A = P * (A * P) := by
      apply sub_eq_zero.mp
      simpa only [mul_sub, mul_one] using hCross.1
    have hAP : A * P = P * (A * P) := by
      apply sub_eq_zero.mp
      simpa only [sub_mul, one_mul] using hCross.2
    apply Matrix.toLin'.injective
    simp only [Matrix.toLin'_mul, hPMatrix]
    simpa only [Module.End.mul_eq_comp, A] using hAP.trans hPA.symm

/-- Infinitesimal commutation, whole-flow commutation, and flowwise reduction are equivalent
for the Hamiltonian convention `U_t = exp (-i t H)`. -/
theorem infinitesimal_reducing_criterion
    (V R : Submodule ℂ (n → ℂ)) (h : IsCompl V R) (H : Matrix n n ℂ) :
    List.TFAE
      [H * visibleProjectionMatrix V R h = visibleProjectionMatrix V R h * H,
       ∀ t : ℝ,
         hamiltonianPropagator H t * visibleProjectionMatrix V R h =
           visibleProjectionMatrix V R h * hamiltonianPropagator H t,
       ∀ t : ℝ, IsReducing (Matrix.toLin' (hamiltonianPropagator H t)) V R] := by
  tfae_have 1 → 2 := by
    intro hComm t
    let P := visibleProjectionMatrix V R h
    change H * P = P * H at hComm
    change hamiltonianPropagator H t * P = P * hamiltonianPropagator H t
    have hGenerator : Commute (hamiltonianGenerator H) P := by
      simpa [hamiltonianGenerator] using (show Commute H P from hComm).smul_left
        (-Complex.I)
    have hScaled : Commute (t • hamiltonianGenerator H) P := hGenerator.smul_left t
    simpa [hamiltonianPropagator] using hScaled.exp_left.eq
  tfae_have 2 → 1 := by
    intro hFlow
    let P := visibleProjectionMatrix V R h
    let A := hamiltonianGenerator H
    have hFlow' (t : ℝ) : exp (t • A) * P = P * exp (t • A) := by
      simpa [P, A, hamiltonianPropagator] using hFlow t
    have hLeft := (hasDerivAt_exp_smul_const A (0 : ℝ)).mul_const P
    have hRight := (hasDerivAt_exp_smul_const A (0 : ℝ)).const_mul P
    have hFunctionEq :
        (fun t : ℝ => exp (t • A) * P) = fun t : ℝ => P * exp (t • A) :=
      funext hFlow'
    rw [hFunctionEq] at hLeft
    have hGeneratorCommutes : A * P = P * A := by
      simpa using hLeft.unique hRight
    have hCancel := congrArg (fun M : Matrix n n ℂ => Complex.I • M) hGeneratorCommutes
    change H * visibleProjectionMatrix V R h = visibleProjectionMatrix V R h * H
    simpa [P, A, hamiltonianGenerator, smul_mul_assoc, mul_smul_comm, smul_smul,
      Complex.I_mul_I] using hCancel
  tfae_have 2 ↔ 3 := by
    constructor
    · intro hFlow t
      exact (commutes_visibleProjectionMatrix_iff_reducing V R h _).mp (hFlow t)
    · intro hReducing t
      exact (commutes_visibleProjectionMatrix_iff_reducing V R h _).mpr (hReducing t)
  tfae_finish

example :
    let V : Submodule ℂ (Fin 1 → ℂ) := ⊤
    let R : Submodule ℂ (Fin 1 → ℂ) := ⊥
    let h : IsCompl V R := isCompl_top_bot
    List.TFAE
      [(1 : Matrix (Fin 1) (Fin 1) ℂ) * visibleProjectionMatrix V R h =
        visibleProjectionMatrix V R h * 1,
       ∀ t : ℝ,
         hamiltonianPropagator (1 : Matrix (Fin 1) (Fin 1) ℂ) t *
             visibleProjectionMatrix V R h =
           visibleProjectionMatrix V R h * hamiltonianPropagator 1 t,
       ∀ t : ℝ,
         IsReducing
           (Matrix.toLin' (hamiltonianPropagator (1 : Matrix (Fin 1) (Fin 1) ℂ) t)) V R] := by
  dsimp only
  exact infinitesimal_reducing_criterion ⊤ ⊥ isCompl_top_bot 1

#print axioms infinitesimal_reducing_criterion

end D5.S3.Observer.HiddenFlow.InfinitesimalReducingCriterion
