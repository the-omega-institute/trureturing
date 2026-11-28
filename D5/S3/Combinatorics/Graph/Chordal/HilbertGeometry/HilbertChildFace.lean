/- GID: D5/S3/Combinatorics/Graph/Chordal/HilbertGeometry/HilbertChildFace
   generality: G
   mirror-B: none(waiver:covered-by-hilbert-clique-phase-reversal-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Centered estimates for a child tetrahedron -/

import OmegaBuild.Commands
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

compile_only_with_mathlib

/-! Omega original.

# Centered estimates for a child tetrahedron

The three old residuals need not sum to zero. The candidate differences
sum to zero, so subtracting the residual mean leaves their pairing invariant.
-/

open scoped InnerProductSpace

namespace HilbertChildFace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem cauchy_three (a b c x y z : E) :
    ⟪a,x⟫_ℝ + ⟪b,y⟫_ℝ + ⟪c,z⟫_ℝ ≤
      Real.sqrt ((‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) * (‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2)) := by
  let F : PiLp 2 (fun _ : Fin 3 => E) := WithLp.toLp 2 ![a,b,c]
  let G : PiLp 2 (fun _ : Fin 3 => E) := WithLp.toLp 2 ![x,y,z]
  have hi : ⟪F,G⟫_ℝ = ⟪a,x⟫_ℝ + ⟪b,y⟫_ℝ + ⟪c,z⟫_ℝ := by
    rw [PiLp.inner_apply, Fin.sum_univ_three]
    rfl
  have hF : ‖F‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
    rfl
  have hG : ‖G‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
    rfl
  rw [← hi, ← hF, ← hG, ← mul_pow, Real.sqrt_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact real_inner_le_norm _ _

theorem centered_energy (p q r : E) :
      ‖p - ((1 / 3 : ℝ) • (p + q + r))‖ ^ 2 +
      ‖q - ((1 / 3 : ℝ) • (p + q + r))‖ ^ 2 +
      ‖r - ((1 / 3 : ℝ) • (p + q + r))‖ ^ 2 =
      ‖p‖ ^ 2 + ‖q‖ ^ 2 + ‖r‖ ^ 2 - ‖p + q + r‖ ^ 2 / 3 := by
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_add_left,
    inner_add_right, real_inner_smul_right, real_inner_comm]
  ring

/-- Centering gives the face-energy estimate for the child tetrahedron. -/
theorem estimates (a b c x y z : E) (h : x + y + z = 0)
    {M T : ℝ}
    (hM : ‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 - (2 / 3) * ‖a + b + c‖ ^ 2 ≤ M) :
    let u := ‖a + b + c‖ ^ 2
    let S := ‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2
    let I := ‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + T -
      (u + ‖a - x‖ ^ 2 + ‖b - y‖ ^ 2 + ‖c - z‖ ^ 2) / 2
    I ≤ M + T ∧ I ≤ M / 2 - u / 6 + Real.sqrt (S * (M + u / 3)) + T - S / 2 := by
  dsimp
  let m : E := (1 / 3 : ℝ) • (a + b + c)
  have hc := centered_energy a b c
  change ‖a - m‖ ^ 2 + ‖b - m‖ ^ 2 + ‖c - m‖ ^ 2 =
    ‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 - ‖a + b + c‖ ^ 2 / 3 at hc
  have hcent : ‖a - m‖ ^ 2 + ‖b - m‖ ^ 2 + ‖c - m‖ ^ 2 ≤ M + ‖a + b + c‖ ^ 2 / 3 := by
    linarith only [hc, hM]
  constructor
  · have hh := centered_energy (a - x) (b - y) (c - z)
    have hsum : (a - x) + (b - y) + (c - z) = a + b + c := by
      calc
        _ = (a + b + c) - (x + y + z) := by abel
        _ = _ := by rw [h, sub_zero]
    rw [hsum] at hh
    linarith only [hM, hh, sq_nonneg ‖a - x - m‖, sq_nonneg ‖b - y - m‖, sq_nonneg ‖c - z - m‖]
  · have hi : ⟪a-m,x⟫_ℝ + ⟪b-m,y⟫_ℝ + ⟪c-m,z⟫_ℝ =
        ⟪a,x⟫_ℝ + ⟪b,y⟫_ℝ + ⟪c,z⟫_ℝ := by
      have hz : ⟪m,x⟫_ℝ + ⟪m,y⟫_ℝ + ⟪m,z⟫_ℝ = 0 := by
        rw [← inner_add_right, ← inner_add_right, h, inner_zero_right]
      simp only [inner_sub_left]
      linarith only [hz]
    have hcs := cauchy_three (a-m) (b-m) (c-m) x y z
    rw [hi, mul_comm] at hcs
    have hroot := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hcent
      (by positivity : 0 ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2))
    rw [norm_sub_sq_real, norm_sub_sq_real b, norm_sub_sq_real c]
    linarith only [hM, hcs, hroot]

end HilbertChildFace
