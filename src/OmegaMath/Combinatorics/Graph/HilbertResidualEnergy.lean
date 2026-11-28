import OmegaBuild.Commands
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

compile_only_with_mathlib

/-! Omega original.

# Gradient and cycle energies on a tetrahedron

Edges are ordered (01,02,03,12,13,23). The squared energy on the four
oriented faces measures precisely four times the squared cycle projection.
-/

open scoped InnerProductSpace

namespace HilbertResidualEnergy

variable {E : Type*} [NormedAddCommGroup E]

/-- The oriented differences along the six increasing edges. -/
def gradient (y : Fin 4 → E) : Fin 6 → E :=
  ![y 0 - y 1, y 0 - y 2, y 0 - y 3, y 1 - y 2, y 1 - y 3, y 2 - y 3]

/-- The four oriented triangle sums. -/
def faces (r : Fin 6 → E) : Fin 4 → E :=
  ![r 0 + r 3 - r 1, r 0 + r 4 - r 2, r 1 + r 5 - r 2, r 3 + r 5 - r 4]

/-- The sum of the three outgoing residuals from each vertex. -/
def divergence (r : Fin 6 → E) : Fin 4 → E :=
  ![r 0 + r 1 + r 2, -r 0 + r 3 + r 4, -r 1 - r 3 + r 5, -r 2 - r 4 - r 5]

/-- The gradient component of an edge array. -/
noncomputable def gradientPart [NormedSpace ℝ E] (r : Fin 6 → E) : Fin 6 → E :=
  gradient (fun i => (1 / 4 : ℝ) • divergence r i)

/-- Squared Euclidean energy of an array with Hilbert entries. -/
noncomputable def energy {n : ℕ} (r : Fin n → E) : ℝ :=
  ∑ i, ‖r i‖ ^ 2

theorem energy_nonneg {n : ℕ} (r : Fin n → E) : 0 ≤ energy r :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem energy_sqrt {n : ℕ} (r : Fin n → E) :
    Real.sqrt (energy r) = ‖(WithLp.toLp 2 r : PiLp 2 (fun _ : Fin n => E))‖ := by
  rw [← Real.sqrt_sq (norm_nonneg (WithLp.toLp 2 r : PiLp 2 (fun _ : Fin n => E))),
    PiLp.norm_sq_eq_of_L2]
  rfl

theorem energy_add_le {n : ℕ} (r s : Fin n → E) :
    energy (r + s) ≤ (Real.sqrt (energy r) + Real.sqrt (energy s)) ^ 2 := by
  have h : Real.sqrt (energy (r + s)) ≤ Real.sqrt (energy r) + Real.sqrt (energy s) := by
    simp only [energy_sqrt]
    exact norm_add_le _ _
  have hh := pow_le_pow_left₀ (Real.sqrt_nonneg (energy (r + s))) h 2
  rwa [Real.sq_sqrt (energy_nonneg (r + s))] at hh

theorem gradientPart_sub [NormedSpace ℝ E] (r s : Fin 6 → E) :
    gradientPart (r - s) = gradientPart r - gradientPart s := by
  ext i
  fin_cases i <;> simp [gradientPart, gradient, divergence] <;> module

theorem gradientPart_gradient [NormedSpace ℝ E] (y : Fin 4 → E) :
    gradientPart (gradient y) = gradient y := by
  ext i
  fin_cases i <;> simp [gradientPart, gradient, divergence] <;> module

theorem faces_sub_gradient (r : Fin 6 → E) (y : Fin 4 → E) :
    faces (gradient y - r) = -faces r := by
  ext i
  fin_cases i <;> simp [faces, gradient] <;> abel

theorem energy_neg {n : ℕ} (r : Fin n → E) : energy (-r) = energy r := by
  simp [energy]

variable [InnerProductSpace ℝ E]

private theorem gradientPart_energy (r : Fin 6 → E) :
    energy (gradientPart r) = energy (divergence r) / 4 := by
  simp only [energy, Fin.sum_univ_six, Fin.sum_univ_four, ← real_inner_self_eq_norm_sq]
  have g0 : gradientPart r 0 = (1 / 4 : ℝ) • divergence r 0 - (1 / 4 : ℝ) • divergence r 1 := rfl
  have g1 : gradientPart r 1 = (1 / 4 : ℝ) • divergence r 0 - (1 / 4 : ℝ) • divergence r 2 := rfl
  have g2 : gradientPart r 2 = (1 / 4 : ℝ) • divergence r 0 - (1 / 4 : ℝ) • divergence r 3 := rfl
  have g3 : gradientPart r 3 = (1 / 4 : ℝ) • divergence r 1 - (1 / 4 : ℝ) • divergence r 2 := rfl
  have g4 : gradientPart r 4 = (1 / 4 : ℝ) • divergence r 1 - (1 / 4 : ℝ) • divergence r 3 := rfl
  have g5 : gradientPart r 5 = (1 / 4 : ℝ) • divergence r 2 - (1 / 4 : ℝ) • divergence r 3 := rfl
  have h0 : divergence r 0 = r 0 + r 1 + r 2 := rfl
  have h1 : divergence r 1 = -r 0 + r 3 + r 4 := rfl
  have h2 : divergence r 2 = -r 1 - r 3 + r 5 := rfl
  have h3 : divergence r 3 = -r 2 - r 4 - r 5 := rfl
  simp only [g0, g1, g2, g3, g4, g5, h0, h1, h2, h3]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    inner_neg_left, inner_neg_right, real_inner_smul_left, real_inner_smul_right]
  simp only [real_inner_comm]
  ring

/-- The tetrahedron has cycle energy equal to one quarter of the face energy. -/
theorem hodge_energy (r : Fin 6 → E) :
    energy (gradientPart r) + energy (faces r) / 4 = energy r := by
  rw [gradientPart_energy]
  simp only [energy, Fin.sum_univ_six, Fin.sum_univ_four, ← real_inner_self_eq_norm_sq]
  have d0 : divergence r 0 = r 0 + r 1 + r 2 := rfl
  have d1 : divergence r 1 = -r 0 + r 3 + r 4 := rfl
  have d2 : divergence r 2 = -r 1 - r 3 + r 5 := rfl
  have d3 : divergence r 3 = -r 2 - r 4 - r 5 := rfl
  have h0 : faces r 0 = r 0 + r 3 - r 1 := rfl
  have h1 : faces r 1 = r 0 + r 4 - r 2 := rfl
  have h2 : faces r 2 = r 1 + r 5 - r 2 := rfl
  have h3 : faces r 3 = r 3 + r 5 - r 4 := rfl
  simp only [d0, d1, d2, d3, h0, h1, h2, h3]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    inner_neg_left, inner_neg_right, real_inner_comm]
  ring

/-- The correction of a gain residual has the opposite cycle component
when the sum of residual and correction is a gradient. -/
theorem corrected_gradient_energy (r : Fin 6 → E) (y : Fin 4 → E) :
    energy (gradient y) ≤
      (Real.sqrt (energy (gradientPart r)) +
        Real.sqrt (energy (gradientPart (gradient y - r)))) ^ 2 := by
  have he : gradient y = gradientPart r + gradientPart (gradient y - r) := by
    rw [gradientPart_sub, gradientPart_gradient]
    abel
  conv_lhs => rw [he]
  exact energy_add_le _ _

end HilbertResidualEnergy
