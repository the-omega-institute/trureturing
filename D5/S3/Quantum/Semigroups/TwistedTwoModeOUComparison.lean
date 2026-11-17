/- GID: D5/S3/Quantum/Semigroups/TwistedTwoModeOUComparison
   generality: G
   mirror-B: D5/B/S3/Quantum/Semigroups/TwistedTwoModeOUComparison
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complex two-mode fermionic pure-state attenuation for unital Kraus maps. -/

import D5.S3.Quantum.Foundation.TwoKrausRankOneAttenuation

/-! Quantitative pure-state loss for the two literal Jordan-Wigner modes. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Matrix Kronecker
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open D5.S3.Quantum.Foundation.TwoKrausRankOneAttenuation

namespace D5.S3.Quantum.Semigroups.TwistedTwoModeOUComparison

private def localJump : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;0,0]
private def signZ : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![-1,1]

/-- The modes on the ordered basis 00,01,10,11. -/
def modeJump (i : Fin 2) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ![localJump ⊗ₖ 1, signZ ⊗ₖ localJump] i

/-- The quartic directional budget, including both complex determinant terms. -/
def directionalBudget (ψ : EuclideanSpace ℂ (Fin 2 × Fin 2)) : ℝ :=
  (Complex.normSq (ψ (0,0)) + Complex.normSq (ψ (0,1)))^2 +
  (Complex.normSq (ψ (0,0)) + Complex.normSq (ψ (1,0)))^2 +
  2 * Complex.normSq (ψ (0,0) * ψ (1,1)) +
  2 * Complex.normSq (ψ (0,1) * ψ (1,0))

private theorem mode_car (i : Fin 2) :
    modeJump i * modeJump i = 0 ∧
    modeJump i * (modeJump i).conjTranspose +
      (modeJump i).conjTranspose * modeJump i = 1 := by
  fin_cases i <;> constructor <;> ext ⟨a,b⟩ ⟨c,d⟩ <;>
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [modeJump, localJump, signZ, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Matrix.kroneckerMap_apply]

set_option maxHeartbeats 2000000 in
-- Expanding the two nested four-dimensional Kraus maps requires finite polynomial normalization.
private theorem mode_maps_commute (q : ℝ) (hq : 0 ≤ q)
    (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    jumpMap (modeJump 0) q (jumpMap (modeJump 1) q X) =
      jumpMap (modeJump 1) q (jumpMap (modeJump 0) q X) := by
  simp only [jumpMap_apply _ _ hq]
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [jumpFilter, modeJump, localJump, signZ, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.kroneckerMap_apply,
      Matrix.conjTranspose_apply] <;> ring

private theorem directional_defect_sum
    (ψ : EuclideanSpace ℂ (Fin 2 × Fin 2)) (hψ : ‖ψ‖ = 1) :
    let u := WithLp.ofLp ψ
    let defect := fun i : Fin 2 =>
      (star u ⬝ᵥ ((modeJump i * (modeJump i).conjTranspose) *ᵥ u)).re -
        Complex.normSq (star u ⬝ᵥ (modeJump i *ᵥ u))
    defect 0 + defect 1 = directionalBudget ψ := by
  have hsum : Complex.normSq (ψ (0,0)) + Complex.normSq (ψ (0,1)) +
      Complex.normSq (ψ (1,0)) + Complex.normSq (ψ (1,1)) = 1 := by
    have h := EuclideanSpace.norm_sq_eq ψ
    rw [hψ] at h
    simpa [Fintype.sum_prod_type, Fin.sum_univ_two, ← Complex.normSq_eq_norm_sq,
      add_assoc] using h.symm
  have halg :
      let u := WithLp.ofLp ψ
      let defect := fun i : Fin 2 =>
        (star u ⬝ᵥ ((modeJump i * (modeJump i).conjTranspose) *ᵥ u)).re -
          Complex.normSq (star u ⬝ᵥ (modeJump i *ᵥ u))
      defect 0 + defect 1 = directionalBudget ψ +
        (2 * Complex.normSq (ψ (0,0)) + Complex.normSq (ψ (0,1)) +
          Complex.normSq (ψ (1,0))) *
        (1 - (Complex.normSq (ψ (0,0)) + Complex.normSq (ψ (0,1)) +
          Complex.normSq (ψ (1,0)) + Complex.normSq (ψ (1,1)))) := by
    simp [modeJump, localJump, signZ, directionalBudget, Matrix.mul_apply,
      Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im]
    ring
  simpa only [hsum, sub_self, mul_zero, add_zero] using halg

/-- Attenuation of every complex pure state by both literal fermionic modes. -/
theorem two_mode_pure_state_attenuation
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (ψ : EuclideanSpace ℂ (Fin 2 × Fin 2)) (hψ : ‖ψ‖ = 1) :
    let u := WithLp.ofLp ψ
    ‖toEuclideanCLM (n := Fin 2 × Fin 2) (𝕜 := ℂ)
      (jumpMap (modeJump 0) q
        (jumpMap (modeJump 1) q (vecMulVec u (star u))))‖ ≤
      1 - q * (1-q) * directionalBudget ψ / 2 := by
  let u := WithLp.ofLp ψ
  let P := vecMulVec u (star u)
  let H := fun i : Fin 2 => jumpMap (modeJump i) q
  let defect := fun i : Fin 2 =>
    (star u ⬝ᵥ ((modeJump i * (modeJump i).conjTranspose) *ᵥ u)).re -
      Complex.normSq (star u ⬝ᵥ (modeJump i *ᵥ u))
  have hsingle (i : Fin 2) :
      ‖toEuclideanCLM (n := Fin 2 × Fin 2) (𝕜 := ℂ) (H i P)‖ ≤
        1 - q * (1-q) * defect i :=
    nilpotent_jump_rank_one_attenuation (modeJump i) (mode_car i).1
      (mode_car i).2 q hq0 hq1 ψ hψ
  have hHerm (i : Fin 2) : (H i P).IsHermitian :=
    (jumpMap_positive (modeJump i) q hq0
      (posSemidef_vecMulVec_self_star u).nonneg).posSemidef.isHermitian
  have hfirst := (jumpMap_norm_le (modeJump 0) (mode_car 0).1 (mode_car 0).2
    q hq0 hq1 (H 1 P) (hHerm 1)).trans (hsingle 1)
  have hsecond := (jumpMap_norm_le (modeJump 1) (mode_car 1).1 (mode_car 1).2
    q hq0 hq1 (H 0 P) (hHerm 0)).trans (hsingle 0)
  change ‖toEuclideanCLM (n := Fin 2 × Fin 2) (𝕜 := ℂ)
    (H 0 (H 1 P))‖ ≤ _
  have hcomm : H 1 (H 0 P) = H 0 (H 1 P) :=
    (mode_maps_commute q hq0 P).symm
  rw [hcomm] at hsecond
  have hsum : defect 0 + defect 1 = directionalBudget ψ :=
    directional_defect_sum ψ hψ
  change ‖toEuclideanCLM (n := Fin 2 × Fin 2) (𝕜 := ℂ)
    (H 0 (H 1 P))‖ ≤ _ at hfirst
  calc
    _ ≤ ((1 - q * (1-q) * defect 0) + (1 - q * (1-q) * defect 1)) / 2 :=
      by linarith
    _ = _ := by rw [← hsum]; ring

#print axioms two_mode_pure_state_attenuation

end D5.S3.Quantum.Semigroups.TwistedTwoModeOUComparison
