/- GID: D5/S3/Quantum/Analysis/RefinedBMVDimThreePairing
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMVDimThreePairing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The three-vertex cubic walk bound from PSD and arithmetic–geometric mean. -/

import D5.S3.Quantum.Analysis.RefinedBMV33
import Mathlib.Analysis.Matrix.Order

/-!
# The dimension-three pairing inequality

The three possible terminal vertices give three pairs of repeated-index walks.
Their arithmetic means dominate the corresponding triangle terms by the
two-column Gram bound. This is the pairing in Hägele, arXiv:2611.00129v1,
Lemma 5, applied without division by the diagonal entries.
-/

open Matrix
open scoped ComplexOrder BigOperators MatrixOrder

namespace RefinedBMV.DimThree

private theorem entry_norm_sq_le (B : Matrix (Fin 3) (Fin 3) ℂ)
    (hB : B.PosSemidef) (i j : Fin 3) :
    ‖B i j‖ ^ 2 ≤ (B i i).re * (B j j).re := by
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  let v (k : Fin 3) : EuclideanSpace ℂ (Fin 3) := WithLp.toLp 2 (fun l ↦ C l k)
  have hentry (k l : Fin 3) : inner ℂ (v k) (v l) = (star C * C) k l := by
    simp only [v, PiLp.inner_apply, RCLike.inner_apply', Matrix.mul_apply,
      Matrix.star_apply, RCLike.star_def]
  have hdiag (k : Fin 3) : ‖v k‖ ^ 2 = ((star C * C) k k).re := by
    simpa only [hentry, RCLike.re_eq_complex_re] using norm_sq_eq_re_inner (𝕜 := ℂ) (v k)
  rw [← hentry i j, ← hdiag i, ← hdiag j, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := ℂ) (v i) (v j)) 2

private theorem paired_terms (β γ x y z D E : ℝ)
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hz : z ^ 2 ≤ β * γ) :
    2 * (z * x * y) * Real.sqrt (D * E) ≤ β * x ^ 2 * D + γ * y ^ 2 * E := by
  rw [mul_assoc]
  refine two_mul_le_add_of_sq_le_mul (by positivity) (by positivity) ?_
  calc
    _ = z ^ 2 * (x ^ 2 * y ^ 2 * (D * E)) := by
      simp only [mul_pow, Real.sq_sqrt (mul_nonneg hD hE)]
      ring
    _ ≤ (β * γ) * (x ^ 2 * y ^ 2 * (D * E)) := mul_le_mul_of_nonneg_right hz (by positivity)
    _ = _ := by ring

/-- The three-vertex cubic walk with a symmetric, diagonal-vanishing defect is
nonnegative when the three geometric means cover the mixed defect. -/
theorem walk_nonneg (d : ℝ → ℝ → ℝ → ℝ) (a : Fin 3 → ℝ)
    (B : Matrix (Fin 3) (Fin 3) ℂ) (hB : B.PosSemidef)
    (hn : ∀ i j k, 0 ≤ d (a i) (a j) (a k)) (hdiag : ∀ x, d x x x = 0)
    (hswap : ∀ x y z, d y x z = d x y z) (hrotate : ∀ x y z, d y z x = d x y z)
    (hpair : d (a 0) (a 1) (a 2) ≤
      Real.sqrt (d (a 1) (a 1) (a 0) * d (a 2) (a 2) (a 0)) +
      Real.sqrt (d (a 0) (a 0) (a 1) * d (a 2) (a 2) (a 1)) +
      Real.sqrt (d (a 0) (a 0) (a 2) * d (a 1) (a 1) (a 2))) :
    0 ≤ walk B (fun i j k ↦ (d (a i) (a j) (a k) : ℂ)) := by
  let β (i : Fin 3) := (B i i).re
  let δ (i j : Fin 3) := d (a i) (a i) (a j)
  let p (i j : Fin 3) := β i * ‖B i j‖ ^ 2 * δ i j
  let t := B 0 1 * B 1 2 * B 2 0
  let w (i j k : Fin 3) := B i j * B j k * B k i * (d (a i) (a j) (a k) : ℂ)
  have hconj (i j : Fin 3) : star (B i j) = B j i :=
    congrFun (congrFun hB.isHermitian j) i
  have hnorm (i j : Fin 3) : ‖B j i‖ = ‖B i j‖ := by rw [← hconj, norm_star]
  have hcycle (i j k : Fin 3) : w j k i = w i j k := by
    dsimp only [w]
    rw [hrotate]
    ring
  have hreverse (i j k : Fin 3) : w j i k = star (w i j k) := by
    have hreal (r : ℝ) : star (r : ℂ) = (r : ℂ) := Complex.conj_ofReal r
    simp only [w, hswap (a i) (a j) (a k), star_mul, hreal, hconj]
    ring
  have hzero (i : Fin 3) : w i i i = 0 := by simp [w, hdiag]
  have hrepeat (i j : Fin 3) : w i i j = (p i j : ℂ) := by
    have hdi : (β i : ℂ) = B i i := Complex.conj_eq_iff_re.mp (hconj i i)
    have hij : (‖B i j‖ ^ 2 : ℝ) = Complex.normSq (B i j) :=
      (Complex.normSq_eq_norm_sq _).symm
    simp only [p, Complex.ofReal_mul, hdi, hij, Complex.normSq_eq_conj_mul_self, δ, w]
    rw [← Complex.star_def, hconj]
    ring
  have hrepeat₁ (i j : Fin 3) : w i j i = (p i j : ℂ) :=
    (hcycle i i j).trans (hrepeat i j)
  have hrepeat₂ (i j : Fin 3) : w j i i = (p i j : ℂ) :=
    (hcycle i j i).trans (hrepeat₁ i j)
  have hcounter : w 0 2 1 = star (w 0 1 2) :=
    (hcycle 1 0 2).trans (hreverse 0 1 2)
  have htriangle : w 0 1 2 + star (w 0 1 2) =
      (2 * t.re * d (a 0) (a 1) (a 2) : ℝ) := by
    rw [Complex.star_def, Complex.add_conj, Complex.ofReal_inj]
    change 2 * (t * (d (a 0) (a 1) (a 2) : ℂ)).re = _
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, mul_assoc]
  have hexpand : walk B (fun i j k ↦ (d (a i) (a j) (a k) : ℂ)) =
      (3 * (p 1 0 + p 2 0 + (p 0 1 + p 2 1) + (p 0 2 + p 1 2)) +
        6 * t.re * d (a 0) (a 1) (a 2) : ℝ) := by
    change (∑ i, ∑ j, ∑ k, w i j k) = _
    simp only [Fin.sum_univ_three, hzero, zero_add, add_zero]
    simp only [hrepeat, hrepeat₁, hrepeat₂,
      hcycle 0 1 2, hcycle 1 2 0, hcycle 0 2 1, hcycle 2 1 0, hcounter]
    calc
      _ = 3 * ((p 1 0 : ℂ) + (p 2 0 : ℂ) + ((p 0 1 : ℂ) + (p 2 1 : ℂ)) +
          ((p 0 2 : ℂ) + (p 1 2 : ℂ))) +
          3 * (w 0 1 2 + star (w 0 1 2)) := by ring
      _ = _ := by rw [htriangle]; push_cast; ring
  have hβ (i : Fin 3) : 0 ≤ β i :=
    (Complex.nonneg_iff.mp (hB.diag_nonneg (i := i))).1
  have hbound (i j k : Fin 3) :
      2 * (‖B i j‖ * ‖B i k‖ * ‖B j k‖) * Real.sqrt (δ i k * δ j k) ≤ p i k + p j k :=
    paired_terms _ _ _ _ _ _ _ (hβ i) (hβ j) (hn i i k) (hn j j k)
      (entry_norm_sq_le B hB i j)
  have h0 := hbound 1 2 0
  have h1 := hbound 0 2 1
  have h2 := hbound 0 1 2
  have ht0 : ‖B 1 2‖ * ‖B 1 0‖ * ‖B 2 0‖ = ‖t‖ := by
    simp only [t, norm_mul, hnorm 0 1]
    ring
  have ht1 : ‖B 0 2‖ * ‖B 0 1‖ * ‖B 2 1‖ = ‖t‖ := by
    simp only [t, norm_mul, hnorm 2 0, hnorm 1 2]
    ring
  have ht2 : ‖B 0 1‖ * ‖B 0 2‖ * ‖B 1 2‖ = ‖t‖ := by
    simp only [t, norm_mul, hnorm 2 0]
    ring
  rw [ht0] at h0
  rw [ht1] at h1
  rw [ht2] at h2
  have htotal := mul_le_mul_of_nonneg_left hpair (show 0 ≤ 2 * ‖t‖ by positivity)
  have hneg : -‖t‖ ≤ t.re := (abs_le.mp (Complex.abs_re_le_norm _)).1
  have hreal := mul_le_mul_of_nonneg_right hneg (hn 0 1 2)
  change 2 * ‖t‖ * d (a 0) (a 1) (a 2) ≤
    2 * ‖t‖ * (Real.sqrt (δ 1 0 * δ 2 0) + Real.sqrt (δ 0 1 * δ 2 1) +
      Real.sqrt (δ 0 2 * δ 1 2)) at htotal
  rw [hexpand, Complex.zero_le_real]
  nlinarith only [h0, h1, h2, htotal, hreal]

#print axioms walk_nonneg

end RefinedBMV.DimThree
