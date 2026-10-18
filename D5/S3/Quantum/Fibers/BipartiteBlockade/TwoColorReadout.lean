/- GID: D5/S3/Quantum/Fibers/BipartiteBlockade/TwoColorReadout
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/BipartiteBlockade/TwoColorReadout
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two proper color-scaled drives recover all blockade expectations from actual matrix accelerations. -/

import D5.S3.Quantum.Fibers.BipartiteBlockade.GeneralCommutator

attribute [local instance] LieRing.ofAssociativeRing

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators Matrix Classical

namespace D5.S3.Quantum.Fibers.BipartiteBlockade
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The second drive doubles one color class. -/
def colorScaledDrive (color : V → Bool) (Ω : V → ℝ) (v : V) : ℝ :=
  if color v then 2 * Ω v else Ω v

/-- Occupation mean in the actual matrix state. -/
def occupationMean (G : SimpleGraph V)
    (ρ : Matrix (Configuration G) (Configuration G) ℂ) (v : V) : ℝ :=
  (Matrix.trace (ρ * number G v)).re

/-- Empty-neighborhood mean in the actual matrix state. -/
def blockadeMean (G : SimpleGraph V)
    (ρ : Matrix (Configuration G) (Configuration G) ℂ) (v : V) : ℝ :=
  (Matrix.trace (ρ * blockade G v)).re

/-- The double-commutator acceleration; no scaling equation is assumed. -/
def acceleration (G : SimpleGraph V) (Ω : V → ℝ)
    (ρ : Matrix (Configuration G) (Configuration G) ℂ) (v : V) : ℝ :=
  -(Matrix.trace (ρ * ⁅hamiltonian G (fun u => (Ω u : ℂ)),
    ⁅hamiltonian G (fun u => (Ω u : ℂ)), number G v⁆⁆)).re

private theorem edge_scaled_product (color : V → Bool) (Ω : V → ℝ)
    (u v : V) (h : color u ≠ color v) :
    (colorScaledDrive color Ω u : ℂ) * (colorScaledDrive color Ω v : ℂ) =
      2 * ((Ω u : ℂ) * (Ω v : ℂ)) := by
  cases hu : color u <;> cases hv : color v <;>
    simp_all [colorScaledDrive] <;> ring

/-- Scaling one side of a proper bipartition cancels all exchange terms in the
same actual finite-configuration Hamiltonian. -/
private theorem two_color_operator_cancel (G : SimpleGraph V) (color : V → Bool)
    (hcolor : ∀ u v, G.Adj u v → color u ≠ color v) (Ω : V → ℝ) (v : V) :
    ⁅hamiltonian G (fun u => (colorScaledDrive color Ω u : ℂ)),
      ⁅hamiltonian G (fun u => (colorScaledDrive color Ω u : ℂ)), number G v⁆⁆ -
      (2 : ℂ) • ⁅hamiltonian G (fun u => (Ω u : ℂ)),
        ⁅hamiltonian G (fun u => (Ω u : ℂ)), number G v⁆⁆ =
      (((if color v then (4 : ℝ) else -2) * Ω v ^ 2 : ℝ) : ℂ) •
        ((2 : ℂ) • number G v - blockade G v) := by
  rw [general_double_commutator, general_double_commutator]
  have hsum :
      (∑ u, if G.Adj u v then
        ((colorScaledDrive color Ω u : ℂ) * (colorScaledDrive color Ω v : ℂ)) •
          exchange G u v else 0) =
        (2 : ℂ) • ∑ u, if G.Adj u v then
          ((Ω u : ℂ) * (Ω v : ℂ)) • exchange G u v else 0 := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro u _
    by_cases ha : G.Adj u v
    · simp [ha, edge_scaled_product color Ω u v (hcolor u v ha), smul_smul]
    · simp [ha]
  rw [hsum, smul_add, smul_smul]
  have hcancel : ∀ A B C : Matrix (Configuration G) (Configuration G) ℂ,
      (A + C) - (B + C) = A - B := by intros; abel
  rw [hcancel, ← sub_smul]
  congr 1
  cases hc : color v <;> simp [colorScaledDrive, hc] <;> ring

/-- Exact two-color inversion for the actual trace acceleration. It applies to
every complex matrix, hence in particular to every density matrix. -/
theorem two_color_readout_inverse (G : SimpleGraph V) (color : V → Bool)
    (hcolor : ∀ u v, G.Adj u v → color u ≠ color v) (Ω : V → ℝ)
    (ρ : Matrix (Configuration G) (Configuration G) ℂ) (v : V) (hΩ : Ω v ≠ 0) :
    blockadeMean G ρ v = 2 * occupationMean G ρ v +
      if color v then
        (acceleration G (colorScaledDrive color Ω) ρ v - 2 * acceleration G Ω ρ v) /
          (4 * Ω v ^ 2)
      else
        (2 * acceleration G Ω ρ v - acceleration G (colorScaledDrive color Ω) ρ v) /
          (2 * Ω v ^ 2) := by
  have ht := congrArg (fun M : Matrix (Configuration G) (Configuration G) ℂ =>
    (Matrix.trace (ρ * M)).re) (two_color_operator_cancel G color hcolor Ω v)
  simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul,
    smul_eq_mul, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero] at ht
  norm_num at ht
  cases hc : color v <;> simp only [hc, Bool.false_eq_true, if_false, if_true] at ht ⊢ <;>
    dsimp [acceleration, occupationMean, blockadeMean] <;>
    field_simp [hΩ] <;> nlinarith [ht]

/-- info: 'D5.S3.Quantum.Fibers.BipartiteBlockade.two_color_readout_inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms two_color_readout_inverse
end D5.S3.Quantum.Fibers.BipartiteBlockade
