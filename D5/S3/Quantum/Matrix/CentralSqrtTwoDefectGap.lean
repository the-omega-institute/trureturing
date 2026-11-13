/- GID: D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap
   generality: G
   mirror-B: none(waiver:evidence-not-specified-by-formal-manifest)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quantitative rank-one sector separation and simple spectrum for the central sqrt-two defect family. -/

import D5.S3.Quantum.Matrix.GibbsStochasticSimpleSpectrum

noncomputable section

open Finset Matrix
open scoped BigOperators

namespace D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap

/-! The scalar estimate used by the defect calculation.  The endpoint control is
the output of the recurrence argument; the theorem below is the rank-one
bridge which turns it into an inverse-cubic spectral separation. -/

theorem rank_one_gap_from_identity {c K lam mu x y z : ℝ}
    (hc : 0 < c) (hK : 0 < K)
    (hidentity : (lam - mu) * z = c * x * y)
    (hx : 1 ≤ K * x ^ 2) (hy : 1 ≤ K * y ^ 2)
    (hz : |z| ≤ 1) :
    c / K ≤ |lam - mu| := by
  have hxy : 1 ≤ K ^ 2 * (x * y) ^ 2 := by
    have hmul := mul_le_mul hx hy (by norm_num : (0 : ℝ) ≤ 1)
      (by positivity : 0 ≤ K * x ^ 2)
    nlinarith
  have habs := congrArg abs hidentity
  rw [abs_mul, abs_mul] at habs
  have hxyabs : 1 ≤ K * |x * y| := by
    have hKabs : 0 ≤ K * |x * y| := mul_nonneg hK.le (abs_nonneg _)
    have hsquare : 1 ≤ (K * |x * y|) ^ 2 := by
      simpa [sq_abs, mul_pow] using hxy
    nlinarith [sq_nonneg (K * |x * y| - 1)]
  have hupper : c * |x * y| ≤ |lam - mu| := by
    have hcx : |c * x| * |y| = c * |x * y| := by
      rw [abs_mul, abs_mul, abs_of_pos hc]
      ring
    calc
      c * |x * y| = |lam - mu| * |z| := by rw [habs, hcx]
      _ ≤ |lam - mu| := mul_le_of_le_one_right (abs_nonneg _) hz
  have hscale : c ≤ K * (c * |x * y|) := by
    have := mul_le_mul_of_nonneg_left hxyabs hc.le
    nlinarith
  have hfinal : c ≤ K * |lam - mu| := by
    exact hscale.trans (mul_le_mul_of_nonneg_left hupper hK.le)
  exact (div_le_iff₀ hK).2 (by simpa [mul_comm] using hfinal)

theorem rank_one_cross_identity {d : Type*} [Fintype d] [DecidableEq d]
    {A B : Matrix d d ℝ} {q : d} {c : ℝ}
    (hA : A.IsSymm)
    (hupdate : B = A + c • Matrix.vecMulVec (Pi.single q 1) (Pi.single q 1))
    (u v : d → ℝ) (lam mu : ℝ)
    (hu : A *ᵥ u = lam • u) (hv : B *ᵥ v = mu • v) :
    (mu - lam) * (u ⬝ᵥ v) = c * (u q) * (v q) := by
  have hs : (A *ᵥ u) ⬝ᵥ v = u ⬝ᵥ (A *ᵥ v) := by
    rw [dotProduct_comm]
    exact hA.dotProduct_mulVec_comm
  have hcore : (lam - mu) * (u ⬝ᵥ v) = -c * (u q) * (v q) := by
    calc
    (lam - mu) * (u ⬝ᵥ v) = (A *ᵥ u) ⬝ᵥ v - u ⬝ᵥ (B *ᵥ v) := by
      rw [hu, hv, smul_dotProduct, dotProduct_smul]
      ring
    _ = u ⬝ᵥ (A *ᵥ v) - u ⬝ᵥ (B *ᵥ v) := by rw [hs]
    _ = u ⬝ᵥ ((A - B) *ᵥ v) := by rw [sub_mulVec, dotProduct_sub]
    _ = -c * (u q) * (v q) := by
      have hab : A - B = -(c • Matrix.vecMulVec (Pi.single q 1) (Pi.single q 1)) := by
        rw [hupdate]
        ext i j
        simp
      rw [hab, neg_mulVec, smul_mulVec, dotProduct_neg, dotProduct_smul]
      simp [Matrix.mulVec, Matrix.vecMulVec, dotProduct, Pi.single_apply]
      ring
  calc
    (mu - lam) * (u ⬝ᵥ v) = -((lam - mu) * (u ⬝ᵥ v)) := by ring
    _ = -(-c * (u q) * (v q)) := by rw [hcore]
    _ = c * (u q) * (v q) := by ring

theorem rank_one_gap_of_matrices {d : Type*} [Fintype d] [DecidableEq d]
    {A B : Matrix d d ℝ} {q : d} {c K : ℝ}
    (hc : 0 < c) (hK : 0 < K) (hA : A.IsSymm)
    (hupdate : B = A + c • Matrix.vecMulVec (Pi.single q 1) (Pi.single q 1))
    (u v : d → ℝ) (lam mu : ℝ)
    (hu : A *ᵥ u = lam • u) (hv : B *ᵥ v = mu • v)
    (hx : 1 ≤ K * (u q) ^ 2) (hy : 1 ≤ K * (v q) ^ 2)
    (hz : |u ⬝ᵥ v| ≤ 1) :
    c / K ≤ |lam - mu| := by
  have h := rank_one_gap_from_identity hc hK
    (rank_one_cross_identity hA hupdate u v lam mu hu hv) hx hy hz
  simpa [abs_sub_comm] using h

def centralEdges (n : ℕ) (hn : 1 ≤ n) : Fin (2 * n - 1 + 1) → ℝ :=
  fun i => if i.val = n - 1 then Real.sqrt 2 else 1

def centralDefect (n : ℕ) (hn : 1 ≤ n) :
    Matrix (Fin (2 * n - 1 + 1)) (Fin (2 * n - 1 + 1)) ℝ :=
  D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence.jacobiMatrix
    (2 * n - 1) 0 (centralEdges n hn)

theorem centralEdges_ne_zero (n : ℕ) (hn : 1 ≤ n) (i : Fin (2 * n - 1 + 1)) :
    centralEdges n hn i ≠ 0 := by
  dsimp [centralEdges]
  split_ifs
  · exact (Real.sqrt_pos.2 (by norm_num)).ne'
  · norm_num

theorem centralDefect_simple (n : ℕ) (hn : 1 ≤ n) :
    D5.S3.Quantum.Matrix.GibbsStochasticSimpleSpectrum.HasSimpleEigenvalues
      (centralDefect n hn) := by
  apply D5.S3.Quantum.Matrix.GibbsStochasticSimpleSpectrum.jacobi_simple
    (2 * n - 1) 0 (centralEdges n hn)
  intro t
  exact centralEdges_ne_zero n hn t.castSucc

end D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap
