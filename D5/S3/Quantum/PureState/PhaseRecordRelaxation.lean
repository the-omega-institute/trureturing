/- GID: D5/S3/Quantum/PureState/PhaseRecordRelaxation
   generality: G
   mirror-B: D5/B/S3/Quantum/PureState/PhaseRecordRelaxation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every feasible profile gives sharp relaxed effects for flat orthogonal phase signals. -/

import D5.S3.Quantum.PureState.QuantumMemoryBudget

namespace PhaseRecordDistillation

noncomputable section

open Matrix
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
open D5.S3.Quantum.PureState.PureStateHandshake
open JointRecordDecoding

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

/-- For a flat orthogonal phase matrix every feasible diagonal profile attains
its bound in the effect relaxation. The witnesses are the normalized phase
effects sandwiched by the diagonal matrix with entries `√(d i)`. -/
theorem relaxed_effects_attain (u : I → I → ℂ) (t d : I → ℝ) (M : ℝ)
    (hu : ∀ j i, ‖u j i‖ = 1)
    (horth : ∀ i l, ∑ j, u j i * star (u j l) =
      if i = l then (Fintype.card I : ℂ) else 0)
    (hd : Feasible d M) :
    ∃ F : I → Matrix I I ℂ, (∀ j, (F j).PosSemidef) ∧
      (∑ j, F j) = diagonal (fun i => (d i : ℂ)) ∧
      (∑ j, F j) ≤ 1 ∧ (∑ j, (trace (F j)).re) ≤ M ∧
      ∀ j, (trace (F j * rankOneDensity (phaseVector u t j))).re =
        (Fintype.card I : ℝ)⁻¹ * profileValue t d ^ 2 := by
  let s (i : I) : ℂ := Real.sqrt (d i)
  let B : Matrix I I ℂ := diagonal s
  let F (j : I) := rankOneDensity (fun i => s i * phaseBasis u j i)
  have hF (j : I) : F j = B * phaseEffect u j * B := by
    ext i l
    simp only [F, phaseEffect, rankOneDensity, vecMulVec_apply, Pi.star_apply, B,
      mul_diagonal, diagonal_mul, star_mul, s, Complex.star_def, Complex.conj_ofReal]
    ring
  have hsum : ∑ j, F j = diagonal (fun i => (d i : ℂ)) := by
    simp_rw [hF]
    rw [← Matrix.sum_mul, ← Matrix.mul_sum, sum_phaseEffect u horth, mul_one]
    dsimp only [B]
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    change (↑(Real.sqrt (d i)) : ℂ) * ↑(Real.sqrt (d i)) = ↑(d i)
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hd.1 i)]
  refine ⟨F, fun j => Matrix.posSemidef_vecMulVec_self_star _, hsum, ?_, ?_, ?_⟩
  · apply Matrix.le_iff.mpr
    rw [hsum, ← Matrix.diagonal_one, diagonal_sub]
    apply Matrix.PosSemidef.diagonal
    intro i
    change (0 : ℂ) ≤ 1 - (d i : ℂ)
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.nonneg_iff, Complex.ofReal_re, Complex.ofReal_im]
    exact ⟨sub_nonneg.mpr (hd.2.1 i), rfl⟩
  · rw [← Complex.re_sum, ← trace_sum, hsum, trace_diagonal, ← Complex.ofReal_sum,
      Complex.ofReal_re]
    exact hd.2.2
  · intro j
    let q : ℝ := (Real.sqrt (Fintype.card I))⁻¹
    have hu' (i : I) : star (u j i) * u j i = 1 := by
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
        hu, one_pow, Complex.ofReal_one]
    have hinner : star (fun i => s i * phaseBasis u j i) ⬝ᵥ phaseVector u t j =
        ((q * profileValue t d : ℝ) : ℂ) := by
      rw [profileValue, Finset.mul_sum, Complex.ofReal_sum, dotProduct]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Pi.star_apply, s, phaseBasis, phaseVector, star_mul,
        Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul, q]
      calc
        _ = (↑q * (↑(t i) * ↑(Real.sqrt (d i)))) * (star (u j i) * u j i) := by
          dsimp [q]
          ring
        _ = _ := by rw [hu', mul_one]
    change (trace (rankOneDensity (fun i => s i * phaseBasis u j i) *
      rankOneDensity (phaseVector u t j))).re = _
    rw [trace_rankOne_pair, hinner, Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, mul_pow]
    have hq : q ^ 2 = (Fintype.card I : ℝ)⁻¹ := by
      dsimp [q]
      rw [inv_pow, Real.sq_sqrt (by positivity)]
    rw [hq]

end

end PhaseRecordDistillation
