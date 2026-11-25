/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/CenteredAverageKernel
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Entrywise path resolvents preserve positive semidefiniteness on a bounded kernel. -/

import D5.S3.Quantum.Analysis.RefinedBMVKernel
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! A positive Schur kernel for successive centered averages can be obtained
by the continued fraction for the reciprocal of twice the hyperbolic cosine. -/

noncomputable section

namespace RefinedBMV

open Filter Matrix Topology
open private weighted_cauchy_psd from D5.S3.Quantum.Analysis.RefinedBMVKernel

/-- At (x=(2\cosh t)^{-1}), this is the successive ratio
(\sinh(nt)/\sinh((n+1)t)), continued at zero. -/
def centeredRatio : ℕ → ℝ → ℝ
  | 0, _ => 0
  | n + 1, x => x / (1 - x * centeredRatio n x)

private theorem centeredRatio_bounds (x : ℝ) (hx : 0 ≤ x) (hh : x ≤ 1/2) (n : ℕ) :
    0 ≤ centeredRatio n x ∧ centeredRatio n x ≤ 1 := by
  induction n with
  | zero => simp [centeredRatio]
  | succ n ih =>
    have hm := mul_le_mul_of_nonneg_left ih.2 hx
    have hden : 0 < 1 - x * centeredRatio n x := by linarith
    refine ⟨div_nonneg hx hden.le, (div_le_one hden).mpr ?_⟩
    linarith

/-- The continued fraction preserves positive semidefiniteness when lifted
entrywise to a kernel with values in ([0,1/2]). -/
theorem centeredRatio_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : H.PosSemidef)
    (h0 : ∀ i j, 0 ≤ H i j) (hhalf : ∀ i j, H i j ≤ 1/2) (n : ℕ) :
    (of fun i j ↦ centeredRatio n (H i j)).PosSemidef := by
  induction n with
  | zero =>
    change (0 : Matrix ι ι ℝ).PosSemidef
    exact .zero
  | succ n ih =>
    let M : Matrix ι ι ℝ := of fun i j ↦ H i j * centeredRatio n (H i j)
    have hM : M.PosSemidef := hH.hadamard ih
    let term (k : ℕ) : Matrix ι ι ℝ := of fun i j ↦ H i j * M i j ^ k
    have hterm (k : ℕ) : (term k).PosSemidef := by
      induction k with
      | zero =>
        convert hH using 1
        ext i j
        simp [term]
      | succ k ih =>
        convert ih.hadamard hM using 1
        ext i j
        simp [term, pow_succ, mul_assoc]
    have hlim : Tendsto (fun N ↦ ∑ k ∈ Finset.range N, term k) atTop
        (𝓝 (of fun i j ↦ centeredRatio (n + 1) (H i j))) := by
      apply tendsto_pi_nhds.2
      intro i
      apply tendsto_pi_nhds.2
      intro j
      have hb := centeredRatio_bounds (H i j) (h0 i j) (hhalf i j) n
      have hm0 : 0 ≤ M i j := mul_nonneg (h0 i j) hb.1
      have hm : M i j < 1 :=
        (mul_le_mul_of_nonneg_left hb.2 (h0 i j)).trans_lt (by linarith [hhalf i j])
      simpa only [term, M, Matrix.sum_apply, Matrix.of_apply, centeredRatio,
          div_eq_mul_inv, Finset.mul_sum] using
        ((hasSum_geometric_of_lt_one hm0 hm).tendsto_sum_nat.const_mul (H i j))
    exact posSemidef_is_closed.mem_of_tendsto hlim
      (Eventually.of_forall fun N ↦ posSemidef_sum _ fun k _ ↦ hterm k)

private def hyperbolicBase (t : ℝ) : ℝ := (2 * Real.cosh t)⁻¹

private theorem hyperbolicBase_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) : (of fun i j ↦ hyperbolicBase (x i - x j)).PosSemidef := by
  let weight := Real.exp ∘ x
  have hp (i) : 0 < weight i := Real.exp_pos _
  have h := weighted_cauchy_psd (fun i ↦ (weight i)^2) weight
    (fun i ↦ sq_nonneg _) (fun i hzero ↦ False.elim ((pow_ne_zero 2 (hp i).ne') hzero))
  convert h using 1
  ext i j
  change (2 * Real.cosh (x i - x j))⁻¹ =
    Real.exp (x i) * Real.exp (x j) / (Real.exp (x i)^2 + Real.exp (x j)^2)
  rw [Real.cosh_eq, show -(x i - x j) = x j - x i by ring,
    Real.exp_sub, Real.exp_sub]
  have hden : Real.exp (x i) / Real.exp (x j) +
      Real.exp (x j) / Real.exp (x i) ≠ 0 := by positivity
  have hsq : Real.exp (x i)^2 + Real.exp (x j)^2 ≠ 0 := by positivity
  field_simp [(Real.exp_pos (x i)).ne', (Real.exp_pos (x j)).ne', hden, hsq] <;> ring

/-- The successive hyperbolic ratio supplies a positive Schur kernel. -/
theorem centered_hyperbolic_kernel_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (n : ℕ) :
    (of fun i j ↦ centeredRatio n (hyperbolicBase (x i - x j))).PosSemidef := by
  refine centeredRatio_posSemidef _ (hyperbolicBase_posSemidef x) (fun i j ↦ ?_)
    (fun i j ↦ ?_) n
  · exact inv_nonneg.mpr (by positivity : 0 ≤ 2 * Real.cosh (x i - x j))
  · change (2 * Real.cosh (x i - x j))⁻¹ ≤ (1:ℝ)/2
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    norm_num
    nlinarith [Real.one_le_cosh (x i - x j)]

/-- At a nonzero argument the continued fraction equals the ratio of hyperbolic sines. -/
theorem centeredRatio_eq_sinh_div (n : ℕ) {t : ℝ} (ht : t ≠ 0) :
    centeredRatio n (hyperbolicBase t) =
      Real.sinh ((n : ℝ)*t) / Real.sinh (((n : ℝ)+1)*t) := by
  induction n with
  | zero => simp [centeredRatio]
  | succ n ih =>
    rw [centeredRatio, ih]
    push_cast
    have hz : 2 * Real.cosh t ≠ 0 := by positivity
    have h1 : Real.sinh (((n : ℝ)+1)*t) ≠ 0 :=
      Real.sinh_ne_zero.mpr (mul_ne_zero (by positivity) ht)
    have h2 : Real.sinh (((n : ℝ)+2)*t) ≠ 0 :=
      Real.sinh_ne_zero.mpr (mul_ne_zero (by positivity) ht)
    have hrec : 2 * Real.cosh t * Real.sinh (((n : ℝ)+1)*t) - Real.sinh ((n:ℝ)*t) =
        Real.sinh (((n : ℝ)+2)*t) := by
      rw [show ((n : ℝ)+2)*t = ((n : ℝ)+1)*t+t by ring, Real.sinh_add,
        show (n : ℝ)*t = ((n : ℝ)+1)*t-t by ring, Real.sinh_sub]
      ring
    have hden : 1 - (2 * Real.cosh t)⁻¹ *
          (Real.sinh ((n : ℝ)*t) / Real.sinh (((n : ℝ)+1)*t)) =
        Real.sinh (((n : ℝ)+2)*t) / (2 * Real.cosh t * Real.sinh (((n : ℝ)+1)*t)) := by
      field_simp [hz, h1]
      linear_combination hrec
    rw [hyperbolicBase, hden, show (n : ℝ)+1+1 = (n : ℝ)+2 by ring]
    field_simp [hz, h1, h2]

/-- The diagonal value of the successive ratio. -/
theorem centeredRatio_half (n : ℕ) : centeredRatio n (1 / 2) = (n : ℝ) / (n + 1) := by
  induction n with
  | zero => simp [centeredRatio]
  | succ n ih =>
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
    have hd : 1 - (1/2 : ℝ)*((n : ℝ)/(n+1)) = ((n : ℝ)+2)/(2*(n+1)) := by
      field_simp [hn]
      ring
    rw [centeredRatio, ih, hd, Nat.cast_succ, show (n : ℝ)+1+1 = (n : ℝ)+2 by ring]
    field_simp [hn, hn2]

#print axioms centeredRatio_posSemidef
#print axioms centered_hyperbolic_kernel_posSemidef

end RefinedBMV
