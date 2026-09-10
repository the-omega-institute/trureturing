/- GID: D5/S3/Quantum/Tomography/Hadamard/HadamardResidualConservation
   generality: I
   mirror-B: D5/B/S3/Quantum/Tomography/Hadamard/HadamardResidualConservation
   mirror-E: none(waiver:interval-replay-is-not-kernel-admission)
   anchors: []
   utility: none
   digest: Actual Hadamard residual conservation supplies balanced-box dual bounds and asymmetric sublevel Newton-row enclosures. -/

import D5.S3.Quantum.Tomography.HadamardResidualBarrier
import D5.S3.Quantum.Tomography.SublevelRowEnclosure

/-!
The exact six-outcome residuals sum to zero for the actual scaled unitary
matrix. Independent intervals lose that relation. Subtracting any common
coefficient lambda from a preconditioner row leaves its residual readout
unchanged. The second theorem transports this sharper interval through the
already-owned directional mean-value theorem.

Reuse: Matrix.star_mulVec, dotProduct_mulVec, mulVec_mulVec, and the existing
SublevelRowEnclosure. No second interval or residual carrier is introduced.
The repository RationalFarkas owner was inspected: its primal variables are
rational, whereas the residuals here are real. The short endpoint argument is
kept private instead of silently restricting real roots to rational points.
-/

open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.Hadamard.HadamardResidualConservation

open Matrix
open D5.S3.Quantum.Tomography.SublevelRowEnclosure

private theorem normSq_sum_eq_real_star_dot (v : Fin 6 → ℂ) :
    ∑ i, Complex.normSq (v i) = (star v ⬝ᵥ v).re := by
  rw [dotProduct, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  change Complex.normSq (v i) = (star (v i) * v i).re
  simp [Complex.star_def, Complex.mul_re, Complex.normSq_apply]

private theorem actual_residual_sum_zero
    (H : Matrix (Fin 6) (Fin 6) ℂ) (u : Fin 6 → ℂ)
    (hGram : H * Hᴴ = (6 : ℂ) • (1 : Matrix (Fin 6) (Fin 6) ℂ))
    (hu : ∀ i, Complex.normSq (u i) = 1) :
    ∑ j, (Complex.normSq ((Hᴴ *ᵥ u) j) - 6) = 0 := by
  have hEnergy :
      star (Hᴴ *ᵥ u) ⬝ᵥ (Hᴴ *ᵥ u) = (6 : ℂ) * (star u ⬝ᵥ u) := by
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose,
      ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hGram,
      Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul] <;> rfl
  have hSum : ∑ j, Complex.normSq ((Hᴴ *ᵥ u) j) = (36 : ℝ) := by
    calc
      ∑ j, Complex.normSq ((Hᴴ *ᵥ u) j) =
          (star (Hᴴ *ᵥ u) ⬝ᵥ (Hᴴ *ᵥ u)).re := normSq_sum_eq_real_star_dot _
      _ = ((6 : ℂ) * (star u ⬝ᵥ u)).re := congrArg Complex.re hEnergy
      _ = 6 * (star u ⬝ᵥ u).re := by simp
      _ = 6 * ∑ i, Complex.normSq (u i) := by rw [← normSq_sum_eq_real_star_dot]
      _ = 36 := by norm_num [hu]
  rw [Finset.sum_sub_distrib, hSum]
  norm_num

private theorem weighted_sum_recenter
    (c r : Fin 6 → ℝ) (lambda : ℝ) (hr : ∑ i, r i = 0) :
    ∑ i, c i * r i = ∑ i, (c i - lambda) * r i := by
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hr, mul_zero, sub_zero]

private theorem balanced_box_dual
    (c r lo hi : Fin 6 → ℝ) (lambdalo lambdahi : ℝ)
    (hr : ∑ i, r i = 0)
    (hlo : ∀ i, lo i ≤ r i) (hhi : ∀ i, r i ≤ hi i) :
    (∑ i, min ((c i - lambdalo) * lo i) ((c i - lambdalo) * hi i)) ≤
        ∑ i, c i * r i ∧
      (∑ i, c i * r i) ≤
        ∑ i, max ((c i - lambdahi) * lo i) ((c i - lambdahi) * hi i) := by
  constructor
  · rw [weighted_sum_recenter c r lambdalo hr]
    apply Finset.sum_le_sum
    intro i _
    by_cases hsign : 0 ≤ c i - lambdalo
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left (hlo i) hsign)
    · exact (min_le_right _ _).trans
        (mul_le_mul_of_nonpos_left (hhi i) (le_of_not_ge hsign))
  · rw [weighted_sum_recenter c r lambdahi hr]
    apply Finset.sum_le_sum
    intro i _
    by_cases hsign : 0 ≤ c i - lambdahi
    · exact (mul_le_mul_of_nonneg_left (hhi i) hsign).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_left (hlo i) (le_of_not_ge hsign)).trans
        (le_max_left _ _)

/-- Any pair of real dual shifts supplies a sound asymmetric bound for a
linear readout of the ACTUAL six-outcome squared-modulus residual. Balance is
proved from H H*=6I and the six unit-modulus entries; it is not a premise.
An external routine may try several shifts and intersect the resulting
intervals. Neither optimality nor a sampled root is needed for soundness. -/
theorem hadamard_residual_box_dual
    (H : Matrix (Fin 6) (Fin 6) ℂ) (u : Fin 6 → ℂ)
    (hGram : H * Hᴴ = (6 : ℂ) • (1 : Matrix (Fin 6) (Fin 6) ℂ))
    (hu : ∀ i, Complex.normSq (u i) = 1)
    (c lo hi : Fin 6 → ℝ) (lambdalo lambdahi : ℝ)
    (hlo : ∀ i, lo i ≤ Complex.normSq ((Hᴴ *ᵥ u) i) - 6)
    (hhi : ∀ i, Complex.normSq ((Hᴴ *ᵥ u) i) - 6 ≤ hi i) :
    (∑ i, min ((c i - lambdalo) * lo i) ((c i - lambdalo) * hi i)) ≤
        ∑ i, c i * (Complex.normSq ((Hᴴ *ᵥ u) i) - 6) ∧
      (∑ i, c i * (Complex.normSq ((Hᴴ *ᵥ u) i) - 6)) ≤
        ∑ i, max ((c i - lambdahi) * lo i) ((c i - lambdahi) * hi i) := by
  exact balanced_box_dual c (fun i ↦ Complex.normSq ((Hᴴ *ᵥ u) i) - 6)
    lo hi lambdalo lambdahi (actual_residual_sum_zero H u hGram hu) hlo hhi

/-- The balanced residual dual bounds enter the actual sublevel Newton-row
enclosure additively. This replaces the independent-box inflation by the
conserved six-outcome readout interval while retaining the full derivative
remainder. The residual function is displayed explicitly. The supplied
Frechet derivative and directional bound remain analytic obligations.

The proof reuses SublevelRowEnclosure on f-f(x), whose residual at x is zero.
It therefore obtains the mean-value remainder without another mean-value
proof or a fictitious shared vector mean-value point. -/
theorem balanced_hadamard_sublevel_row_enclosure
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : Matrix (Fin 6) (Fin 6) ℂ) (phase : E → Fin 6 → ℂ)
    (J : E → E →L[ℝ] (Fin 6 → ℝ))
    (observe : E →L[ℝ] ℝ) (precondition : (Fin 6 → ℝ) →L[ℝ] ℝ)
    (c lo hi : Fin 6 → ℝ) (m x : E) (radius lambdalo lambdahi : ℝ)
    (hGram : H * Hᴴ = (6 : ℂ) • (1 : Matrix (Fin 6) (Fin 6) ℂ))
    (hphase : ∀ i, Complex.normSq (phase x i) = 1)
    (hprecondition : ∀ y, precondition y = ∑ i, c i * y i)
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasFDerivAt (fun z i ↦ Complex.normSq ((Hᴴ *ᵥ phase z) i) - 6)
        (J (m + t • (x - m))) (m + t • (x - m)))
    (hdirectional : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖observe (x - m) - precondition (J (m + t • (x - m)) (x - m))‖ ≤ radius)
    (hlo : ∀ i, lo i ≤ Complex.normSq ((Hᴴ *ᵥ phase x) i) - 6)
    (hhi : ∀ i, Complex.normSq ((Hᴴ *ᵥ phase x) i) - 6 ≤ hi i) :
    observe m - precondition (fun i ↦ Complex.normSq ((Hᴴ *ᵥ phase m) i) - 6)
        - radius + (∑ i, min ((c i - lambdalo) * lo i) ((c i - lambdalo) * hi i)) ≤
        observe x ∧
      observe x ≤
        observe m - precondition (fun i ↦ Complex.normSq ((Hᴴ *ᵥ phase m) i) - 6)
          + radius + (∑ i, max ((c i - lambdahi) * lo i) ((c i - lambdahi) * hi i)) := by
  let f : E → Fin 6 → ℝ := fun z i ↦ Complex.normSq ((Hᴴ *ᵥ phase z) i) - 6
  have hread := hadamard_residual_box_dual H (phase x) hGram hphase
    c lo hi lambdalo lambdahi hlo hhi
  have hreadLo : (∑ i, min ((c i - lambdalo) * lo i) ((c i - lambdalo) * hi i)) ≤
      precondition (f x) := by
    rw [hprecondition]
    exact hread.1
  have hreadHi : precondition (f x) ≤
      ∑ i, max ((c i - lambdahi) * lo i) ((c i - lambdahi) * hi i) := by
    rw [hprecondition]
    exact hread.2
  have hshift : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasFDerivAt (fun z ↦ f z - f x)
        (J (m + t • (x - m))) (m + t • (x - m)) := by
    intro t ht
    exact (hderiv t ht).sub_const (f x)
  have hrem := preconditioned_sublevel_row_enclosure
    (fun z ↦ f z - f x) J observe precondition m x radius 0
    hshift hdirectional (by simp)
  simp only [map_sub, mul_zero, add_zero, Real.norm_eq_abs] at hrem
  have hremLo := (abs_le.mp hrem).1
  have hremHi := (abs_le.mp hrem).2
  change observe m - precondition (f m) - radius + _ ≤ observe x ∧
    observe x ≤ observe m - precondition (f m) + radius + _
  constructor <;> linarith

#print axioms hadamard_residual_box_dual
#print axioms balanced_hadamard_sublevel_row_enclosure

end D5.S3.Quantum.Tomography.Hadamard.HadamardResidualConservation
