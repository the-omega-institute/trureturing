/- GID: D5/S3/Quantum/Dynamics/FinitePropagationHistory
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/FinitePropagationHistory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite unitary trajectories identify the propagation kernel isometrically. -/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

noncomputable section
open scoped BigOperators InnerProductSpace
namespace D5.S3.Quantum.Dynamics.FinitePropagationHistory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Ordered evolution through the first `k` transitions. -/
def evolution (U : ℕ → H ≃ₗᵢ[ℂ] H) : ℕ → H ≃ₗᵢ[ℂ] H
  | 0 => LinearIsometryEquiv.refl ℂ H
  | k + 1 => (evolution U k).trans (U k)

/-- The clock has exactly `T + 1` mutually orthogonal positions. -/
abbrev ClockHistory (H : Type*) [NormedAddCommGroup H] (T : ℕ) :=
  PiLp 2 (fun _ : Fin (T + 1) => H)

/-- Differences across every adjacent pair of clock positions. -/
def propagation (U : ℕ → H ≃ₗᵢ[ℂ] H) (T : ℕ) :
    ClockHistory H T →ₗ[ℂ] PiLp 2 (fun _ : Fin T => H) where
  toFun x := WithLp.toLp 2 (fun k => x k.succ - U k (x k.castSucc))
  map_add' x y := by ext k; simp; abel
  map_smul' c x := by ext k; simp [smul_sub]

/-- The unnormalized complete trajectory. -/
def trajectory (U : ℕ → H ≃ₗᵢ[ℂ] H) (T : ℕ) : H →ₗ[ℂ] ClockHistory H T where
  toFun x := WithLp.toLp 2 (fun k => evolution U k x)
  map_add' x y := by ext k; simp
  map_smul' c x := by ext k; simp

private theorem trajectory_inner (U : ℕ → H ≃ₗᵢ[ℂ] H) (T : ℕ) (x y : H) :
    inner ℂ (trajectory U T x) (trajectory U T y) =
      (T + 1 : ℂ) * inner ℂ x y := by
  simp [PiLp.inner_apply, trajectory]

/-- A trajectory is uniquely reconstructed from its component at clock zero. -/
theorem propagation_kernel (U : ℕ → H ≃ₗᵢ[ℂ] H) (T : ℕ) (x : ClockHistory H T) :
    propagation U T x = 0 ↔ x = trajectory U T (x 0) := by
  constructor
  · intro hx
    have step (k : Fin T) : x k.succ = U k (x k.castSucc) := by
      have h := congrArg (fun z => z k) hx
      exact sub_eq_zero.mp h
    ext k
    change x k = evolution U k (x 0)
    obtain ⟨k, hk⟩ := k
    induction k with
    | zero => rfl
    | succ k ih =>
      have hk' : k < T := by omega
      change x (Fin.succ ⟨k, hk'⟩) = _
      rw [step]
      change U k (x ⟨k, by omega⟩) = U k (evolution U k (x 0))
      rw [ih (by omega)]
  · intro hx
    rw [hx]
    ext k
    simp [propagation, trajectory, evolution]

/-- The inverse square-root clock normalization, including the one-slot clock. -/
def historyEmbedding (U : ℕ → H ≃ₗᵢ[ℂ] H) (T : ℕ) :
    H →ₗᵢ[ℂ] ClockHistory H T :=
  LinearMap.isometryOfInner
    (((Real.sqrt (T + 1 : ℝ))⁻¹ : ℂ) • trajectory U T)
    (by
      intro x y
      simp only [LinearMap.smul_apply, inner_smul_left, inner_smul_right]
      rw [trajectory_inner]
      have hr : Real.sqrt (T + 1 : ℝ) ≠ 0 := by positivity
      have hs : (Real.sqrt (T + 1 : ℝ) : ℂ) ^ 2 = (T + 1 : ℂ) := by
        exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ T + 1 by positivity)
      simp only [map_inv₀, Complex.conj_ofReal]
      field_simp
      linear_combination - hs * inner ℂ x y)

/-- The normalized history embedding has exactly the complete propagation trajectories as range. -/
theorem history_range (U : ℕ → H ≃ₗᵢ[ℂ] H) (T : ℕ) :
    LinearMap.range (historyEmbedding U T).toLinearMap = (propagation U T).ker := by
  ext x
  change (∃ y, historyEmbedding U T y = x) ↔ propagation U T x = 0
  constructor
  · rintro ⟨y, rfl⟩
    apply (propagation_kernel U T _).2
    ext k
    simp [historyEmbedding, trajectory, evolution]
  · intro hx
    refine ⟨(Real.sqrt (T + 1 : ℝ) : ℂ) • x 0, ?_⟩
    have hr : (Real.sqrt (T + 1 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (show Real.sqrt (T + 1 : ℝ) ≠ 0 by positivity)
    rw [(propagation_kernel U T x).mp hx]
    ext k
    change (↑(Real.sqrt (T + 1 : ℝ)) : ℂ)⁻¹ •
      (evolution U k ((Real.sqrt (T + 1 : ℝ) : ℂ) • x 0)) =
      evolution U k (x 0)
    rw [LinearIsometryEquiv.map_smul, smul_smul, inv_mul_cancel₀ hr, one_smul]


#print axioms propagation_kernel
#print axioms history_range
end D5.S3.Quantum.Dynamics.FinitePropagationHistory
