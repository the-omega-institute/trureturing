/- GID: D5/S3/Weil/GroundMode/RealReadoutCancellation
   generality: G
   mirror-B: D5/B/S3/Weil/GroundMode/RealReadoutCancellation
   mirror-E: none(waiver:real-hilbert-interpolation-with-separate-arithmetic-consumer)
   anchors: []
   digest: Compute the exact minimum real error energy for two simultaneous readout constraints and give primal and dual zero-exclusion certificates. -/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Two real readouts constrain one real error

A complex zero of a transform of a real function imposes two real equations
on the same error vector. A complex one-functional error ball does not
preserve this restriction. This file solves the two-equation problem by an
explicit rank-two Gram inverse and proves minimum energy by orthogonality.

The determinant-positive case is stated explicitly; no inverse is invoked
at a rank drop. A dual exclusion theorem has no rank hypothesis. Rescaling
the second equation is proved to preserve the energy formula, which permits
the imaginary Fourier equation to be divided by the nonzero ordinate before
approaching the real axis.

Methodological reference: Gnazzo--Guglielmi--Poloni--Sicilia,
arXiv:2603.05419v1, Section 2.2, equations (12)--(14): the classical constrained
minimum-norm solve inside a structured distance problem. Their nonlinear
matrix iteration is not used here. No priority claim is made.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Weil.GroundMode.RealReadoutCancellation

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The determinant of the real two-readout Gram matrix. -/
def pairGramDet (b c : H) : ℝ := ‖b‖ ^ 2 * ‖c‖ ^ 2 - ⟪b, c⟫_ℝ ^ 2

/-- The algebraic minimum-energy expression, used under positive determinant. -/
def pairEnergy (b c : H) (x y : ℝ) : ℝ :=
  (‖c‖ ^ 2 * x ^ 2 - 2 * ⟪b, c⟫_ℝ * x * y + ‖b‖ ^ 2 * y ^ 2) / pairGramDet b c

/-- The explicit least-norm vector satisfying the two readout equations. -/
def pairWitness (b c : H) (x y : ℝ) : H :=
  ((‖c‖ ^ 2 * x - ⟪b, c⟫_ℝ * y) / pairGramDet b c) • b +
    ((‖b‖ ^ 2 * y - ⟪b, c⟫_ℝ * x) / pairGramDet b c) • c

private theorem pairWitness_inner (b c w : H) (x y : ℝ) :
    ⟪pairWitness b c x y, w⟫_ℝ =
      ((‖c‖ ^ 2 * x - ⟪b, c⟫_ℝ * y) / pairGramDet b c) * ⟪b, w⟫_ℝ +
        ((‖b‖ ^ 2 * y - ⟪b, c⟫_ℝ * x) / pairGramDet b c) * ⟪c, w⟫_ℝ := by
  rw [pairWitness, inner_add_left, real_inner_smul_left, real_inner_smul_left]

/-- Construct both exact readouts and compute the witness energy. -/
theorem pairWitness_spec (b c : H) (x y : ℝ) (hdet : 0 < pairGramDet b c) :
    ⟪b, pairWitness b c x y⟫_ℝ = x ∧
      ⟪c, pairWitness b c x y⟫_ℝ = y ∧
      ‖pairWitness b c x y‖ ^ 2 = pairEnergy b c x y := by
  have hD : pairGramDet b c ≠ 0 := ne_of_gt hdet
  have hb : ⟪b, pairWitness b c x y⟫_ℝ = x := by
    simp only [pairWitness, inner_add_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    field_simp [hD]
    unfold pairGramDet
    ring
  have hc : ⟪c, pairWitness b c x y⟫_ℝ = y := by
    simp only [pairWitness, inner_add_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, real_inner_comm b c]
    field_simp [hD]
    unfold pairGramDet
    ring
  have hn : ‖pairWitness b c x y‖ ^ 2 = pairEnergy b c x y := by
    rw [← real_inner_self_eq_norm_sq, pairWitness_inner, hb, hc]
    unfold pairEnergy
    ring
  exact ⟨hb, hc, hn⟩

/-- The explicit witness is orthogonal to every feasible displacement.
Consequently its energy is the exact minimum, without a pseudoinverse oracle. -/
theorem real_pair_energy_decomposition (b c w : H) (x y : ℝ)
    (hdet : 0 < pairGramDet b c) (hb : ⟪b, w⟫_ℝ = x) (hc : ⟪c, w⟫_ℝ = y) :
    ‖w‖ ^ 2 = pairEnergy b c x y + ‖w - pairWitness b c x y‖ ^ 2 := by
  obtain ⟨hp, hq, hn⟩ := pairWitness_spec b c x y hdet
  have horth : ⟪pairWitness b c x y, w - pairWitness b c x y⟫_ℝ = 0 := by
    rw [pairWitness_inner, inner_sub_right, inner_sub_right, hb, hc, hp, hq]
    ring
  have hsum : pairWitness b c x y + (w - pairWitness b c x y) = w := by
    simp [add_comm]
  have hh := norm_add_sq_real (pairWitness b c x y) (w - pairWitness b c x y)
  rw [hsum, horth, hn] at hh
  linarith

/-- Exact feasibility of two real readouts within a squared-norm budget. -/
theorem real_pair_attainable_iff (b c : H) (x y e : ℝ)
    (hdet : 0 < pairGramDet b c) :
    (∃ w : H, ‖w‖ ^ 2 ≤ e ∧ ⟪b, w⟫_ℝ = x ∧ ⟪c, w⟫_ℝ = y) ↔
      pairEnergy b c x y ≤ e := by
  constructor
  · rintro ⟨w, hw, hb, hc⟩
    have hd := real_pair_energy_decomposition b c w x y hdet hb hc
    nlinarith [sq_nonneg ‖w - pairWitness b c x y‖]
  · intro he
    obtain ⟨hb, hc, hn⟩ := pairWitness_spec b c x y hdet
    exact ⟨pairWitness b c x y, hn.trans_le he, hb, hc⟩

/-- If both readout representers are candidate-orthogonal, the minimizing
witness is too. Thus passing to the real candidate-orthogonal space loses
no attainability information in this two-readout problem. -/
theorem pairWitness_orthogonal (k b c : H) (x y : ℝ)
    (hb : ⟪k, b⟫_ℝ = 0) (hc : ⟪k, c⟫_ℝ = 0) :
    ⟪k, pairWitness b c x y⟫_ℝ = 0 := by
  simp only [pairWitness, inner_add_right, real_inner_smul_right, hb, hc,
    mul_zero, add_zero]

/-- A strict minimum-energy margin excludes a complex zero for every real
error in the ball. This is a structured robustness claim, not a statement
that every feasible ball vector is an eigenvector of a fixed operator. -/
theorem real_ball_complex_readout_ne_zero (b c w : H) (x y e : ℝ)
    (hdet : 0 < pairGramDet b c) (hw : ‖w‖ ^ 2 ≤ e)
    (hmargin : e < pairEnergy b c (-x) (-y)) :
    Complex.mk (x + ⟪b, w⟫_ℝ) (y + ⟪c, w⟫_ℝ) ≠ 0 := by
  intro hz
  have hx := congrArg Complex.re hz
  have hy := congrArg Complex.im hz
  simp only [Complex.mk_re, Complex.mk_im, Complex.zero_re, Complex.zero_im] at hx hy
  have hf := (real_pair_attainable_iff b c (-x) (-y) e hdet).mp
    ⟨w, hw, by linarith, by linarith⟩
  exact (not_le_of_gt hmargin) hf

/-- Any real combination of the two equations gives a valid dual exclusion
certificate. Unlike the inverse-Gram expression this needs no rank premise. -/
theorem dual_pair_exclusion (b c w : H) (x y e s t : ℝ)
    (hw : ‖w‖ ^ 2 ≤ e)
    (hmargin : e * ‖s • b + t • c‖ ^ 2 < (s * x + t * y) ^ 2) :
    ¬ (⟪b, w⟫_ℝ = x ∧ ⟪c, w⟫_ℝ = y) := by
  rintro ⟨hb, hc⟩
  have hh := abs_real_inner_le_norm (s • b + t • c) w
  have hs := pow_le_pow_left₀ (abs_nonneg _) hh 2
  have hv := mul_le_mul_of_nonneg_left hw (sq_nonneg ‖s • b + t • c‖)
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hb, hc] at hs
  rw [sq_abs, mul_pow] at hs
  nlinarith

/-- Multiplying the second readout equation by a nonzero real scalar does
not change its minimum-energy expression. In the Fourier application the
factor is 1/y, used only for y nonzero; the rescaled kernel has a finite
limit on the real axis. -/
theorem rescaled_pair_cost (U V C x y s : ℝ) (hs : s ≠ 0) :
    ((s ^ 2 * V) * x ^ 2 - 2 * (s * C) * x * (s * y) + U * (s * y) ^ 2) /
        (U * (s ^ 2 * V) - (s * C) ^ 2) =
      (V * x ^ 2 - 2 * C * x * y + U * y ^ 2) / (U * V - C ^ 2) := by
  rw [show (s ^ 2 * V) * x ^ 2 - 2 * (s * C) * x * (s * y) + U * (s * y) ^ 2 =
    s ^ 2 * (V * x ^ 2 - 2 * C * x * y + U * y ^ 2) by ring]
  rw [show U * (s ^ 2 * V) - (s * C) ^ 2 = s ^ 2 * (U * V - C ^ 2) by ring]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hs)

#print axioms pairWitness_spec
#print axioms real_pair_energy_decomposition
#print axioms real_pair_attainable_iff
#print axioms pairWitness_orthogonal
#print axioms real_ball_complex_readout_ne_zero
#print axioms dual_pair_exclusion
#print axioms rescaled_pair_cost

end D5.S3.Weil.GroundMode.RealReadoutCancellation
end
