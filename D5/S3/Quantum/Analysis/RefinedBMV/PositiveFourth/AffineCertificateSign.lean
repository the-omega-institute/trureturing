/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/AffineCertificateSign
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nonnegative affine coefficient tables at every integral degree beyond the starting value. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineCertificateBounds
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineTableTerms

/-! The static rate checks ensure that both spectral substitutions have the
integer exponents used by the coefficient table and packed identity. -/

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum.GroupedAffineMasks

open RefinedBMV.DividedDifference.SparseExpansion

private def checkRoot (start : ℕ) (a : AffineRate) : Bool :=
  decide (start * a.2 ≤ a.1 ∧ 4 ∣ a.1 - start * a.2)

def Certificate.checkRootExponents (c : Certificate) (start : ℕ) : Bool :=
  c.rootsU.all (checkRoot start) && c.rootsV.all (checkRoot start)

theorem Certificate.nonneg_tableTerms_at_degree (c : Certificate)
    (start degree cap width digits p : ℕ)
    (hp : start ≤ p)
    (hroots : c.checkRootExponents start = true)
    (hrates : c.checkRates = true)
    (hstatic : c.staticCheck degree cap width digits = true)
    (hrows : ∀ k < c.rootsU.length, c.checkRow width digits k = true)
    {r t : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) (ht : 0 < t) (ht₁ : t ≤ 1) :
    0 ≤ evalTerms ((p - start : ℕ) : ℝ) (r ^ 4) (t ^ 4) (r ^ p) (t ^ p)
      (c.tableTerms start) := by
  simp only [Certificate.checkRootExponents, Bool.and_eq_true, List.all_eq_true,
    checkRoot, decide_eq_true_eq] at hroots
  have hU (i : c.Index) := hroots.1 _ (c.rates_mem hrates i).1
  have hV (i : c.Index) := hroots.2 _ (c.rates_mem hrates i).2
  rw [c.eval_tableTerms start (fun i => (hU i).2) (fun i => (hV i).2)]
  have h := c.nonneg_evaluate_of_rows start width digits
    (fun i => (hU i).1) (fun i => (hV i).1) hrates hrows
    (c.bounds_of_staticCheck degree cap width digits hrates hstatic)
    (x := ((p - start : ℕ) : ℝ)) (by positivity) hr hr₁ ht ht₁
  have he : (start : ℝ) + ((p - start : ℕ) : ℝ) = (p : ℝ) := by
    rw [Nat.cast_sub hp]
    ring
  simpa only [he, Real.rpow_natCast] using h

end RefinedBMV.ThreeBlockGram.PositiveSpectrum.GroupedAffineMasks
