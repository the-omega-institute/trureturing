/- GID: D5/S3/Quantum/Foundation/ApproximateOrientedAnchorRepair
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/ApproximateOrientedAnchorRepair
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform Hilbert polar repair from finite oriented approximate comparisons. -/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Tactic

noncomputable section
open scoped InnerProductSpace ComplexOrder BigOperators MatrixOrder Matrix.Norms.L2Operator
open Complex ContinuousLinearMap

namespace D5.S3.Quantum.Foundation.ApproximateOrientedAnchorRepair

variable {H W : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W]

/-- The actual basis extension, without any orthogonality premise on its images. -/
def basisExtension {d : ℕ} (a : OrthonormalBasis (Fin d) ℂ H) (F : H → W) : H →L[ℂ] W :=
  (a.toBasis.constr ℂ (fun j => F (a j))).toContinuousLinearMap

def eta (d : ℕ) (δ : ℝ) : ℝ := Real.sqrt ((d : ℝ) / 2) * δ

def kappa (d : ℕ) (δ : ℝ) : ℝ := ((d : ℝ) - 1) / Real.sqrt 2 * δ

private lemma basisExtension_apply {d : ℕ} (a : OrthonormalBasis (Fin d) ℂ H)
    (F : H → W) (j : Fin d) : basisExtension a F (a j) = F (a j) := by
  simp [basisExtension]

private lemma comparison_re (x a : H) (y b : W)
    (hx : ‖x‖ = 1) (ha : ‖a‖ = 1) (hy : ‖y‖ = 1) (hb : ‖b‖ = 1)
    {δ : ℝ} (h : ‖y - b‖ ^ 2 ≤ ‖x - a‖ ^ 2 + δ) :
    (⟪a, x⟫_ℂ).re - δ / 2 ≤ (⟪b, y⟫_ℂ).re := by
  rw [norm_sub_sq, norm_sub_sq, hx, ha, hy, hb, inner_re_symm y b,
    inner_re_symm x a] at h
  linarith

private lemma four_anchor_coordinates {d : ℕ}
    (a : OrthonormalBasis (Fin d) ℂ H) (F : H → W) {δ : ℝ}
    (hN : ∀ x, ‖x‖ = 1 → ‖F x‖ = 1)
    (hphase : ∀ j (k : Fin 4), F ((I ^ (k : ℕ)) • a j) = (I ^ (k : ℕ)) • F (a j))
    (hcomp : ∀ x, ‖x‖ = 1 → ∀ j (k : Fin 4),
      ‖F x - F ((I ^ (k : ℕ)) • a j)‖ ^ 2 ≤
        ‖x - (I ^ (k : ℕ)) • a j‖ ^ 2 + δ)
    (x : H) (hx : ‖x‖ = 1) (j : Fin d) :
    |(⟪F (a j), F x⟫_ℂ - ⟪a j, x⟫_ℂ).re| ≤ δ / 2 ∧
    |(⟪F (a j), F x⟫_ℂ - ⟪a j, x⟫_ℂ).im| ≤ δ / 2 := by
  have hn := hN (a j) (a.norm_eq_one j)
  have h (k : Fin 4) := comparison_re x ((I ^ (k : ℕ)) • a j) (F x)
    ((I ^ (k : ℕ)) • F (a j)) hx
    (by simp [norm_smul, a.norm_eq_one]) (hN x hx)
    (by simp [norm_smul, hn]) (by simpa only [hphase] using hcomp x hx j k)
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  norm_num [inner_smul_left, I_sq, pow_succ, Complex.mul_re, Complex.mul_im,
    Complex.conj_ofReal, Complex.sub_re, Complex.sub_im] at h0 h1 h2 h3 ⊢
  constructor <;> rw [abs_le] <;> constructor <;> linarith

end D5.S3.Quantum.Foundation.ApproximateOrientedAnchorRepair
