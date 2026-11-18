/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalMoments
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Explicit central-column moments in the literal all-mode displacement equations. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalDisplacement

/-! The two rank-one columns are the original central column and its actual derivative jet. -/

noncomputable section
open scoped BigOperators Topology ENNReal
namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalMoments
open OriginalGaussianMatrix OriginalGaussianResolvent OriginalGaussianWeightedResolvent
open OriginalGaussianAllIndexResolvent OriginalGaussianDifferentiation
open OriginalGaussianExternalResolvent OriginalGaussianExternalFrequency
open OriginalGaussianExternalDisplacement OriginalGaussianSourceEvaluation

def sourceMoment (out : Bool) (p : ℕ) (x : ℂ) : ℂ :=
  ∑' n : ℕ, (n + 1 : ℂ) * (-1 : ℂ) ^ (n + 1) * externalBinomial out p (n + 1) *
    x ^ (n + 1) * shiftedCentralSeries x (n + 1)

def sourceJetMoment (out : Bool) (p : ℕ) (x : ℂ) : ℂ :=
  ∑' n : ℕ, (-1 : ℂ) ^ (n + 1) * externalBinomial out p (n + 1) *
    x ^ (n + 1) * centralColumnJet x (n + 1)

/-- The full zero-frequency term cancels in the signed mode difference. -/
theorem sourceMoment_eq_modeFrequency (out : Bool) (p : ℕ) {x : ℂ} (hx : ‖x‖ < 1) :
    sourceMoment out p x = modeFrequency out p (fun e k => sourceAmplitude e k x) := by
  have h₁ := sourceAmplitude_hasSum out p hx
  have h₂ := sourceAmplitude_hasSum (predecessor out p).1 (predecessor out p).2 hx
  have h := (h₁.sub h₂).mul_left (externalParameter out p)
  have he (s : ℕ) : externalParameter out p *
      ((-1 : ℂ) ^ s * externalBinomial out p s * x ^ s * shiftedCentralSeries x s -
        (-1 : ℂ) ^ s * externalBinomial (predecessor out p).1 (predecessor out p).2 s *
          x ^ s * shiftedCentralSeries x s) =
      (s : ℂ) * (-1 : ℂ) ^ s * externalBinomial out p s * x ^ s *
        shiftedCentralSeries x s := by
    linear_combination -(-1 : ℂ) ^ s * x ^ s * shiftedCentralSeries x s *
      binomial_frequency out p s
  have hh := h.congr_fun (fun s => (he s).symm)
  have hshift := (hasSum_nat_add_iff' 1).mpr hh
  simpa only [Finset.sum_range_one, Nat.cast_zero, zero_mul, sub_zero,
    Nat.cast_add, Nat.cast_one, modeFrequency, sourceMoment] using hshift.tsum_eq

private lemma negative_term (out : Bool) (p : ℕ) {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (n : ℕ) :
    externalVector out p (Real.sqrt r : ℂ) n *
      oppositeResolvent (Real.sqrt r : ℂ) (weightedSource r hr.le hr1) n =
    -(Real.sqrt (1 - r) : ℂ) * ((n + 1 : ℂ) * (-1 : ℂ) ^ (n + 1) *
      externalBinomial out p (n + 1) * (r : ℂ) ^ (n + 1) *
        shiftedCentralSeries (r : ℂ) (n + 1)) := by
  rw [externalVector_apply out p (radial_norm_lt_one hr1), radial_negative_column hr hr1]
  have hs : (Real.sqrt (n + 1 : ℝ) : ℂ) ^ 2 = (n + 1 : ℂ) := by
    exact_mod_cast Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n + 1)
  have hz : (Real.sqrt r : ℂ) ^ 2 = (r : ℂ) := by
    exact_mod_cast Real.sq_sqrt hr.le
  simp only [externalColumn]
  rw [← hs, ← hz]
  ring

private lemma positive_term (out : Bool) (p : ℕ) {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (n : ℕ) :
    externalVector out p (Real.sqrt r : ℂ) n *
      resolvent (Real.sqrt r : ℂ) (weightedSource r hr.le hr1) n =
    -(Real.sqrt (1 - r) : ℂ) * ((-1 : ℂ) ^ (n + 1) *
      externalBinomial out p (n + 1) * (r : ℂ) ^ (n + 1) *
        centralColumnJet (r : ℂ) (n + 1)) := by
  rw [externalVector_apply out p (radial_norm_lt_one hr1), radial_positive_column hr hr1]
  have hn : (Real.sqrt (n + 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < n + 1)).ne'
  have hz : (Real.sqrt r : ℂ) ^ 2 = (r : ℂ) := by
    exact_mod_cast Real.sq_sqrt hr.le
  simp only [externalColumn]
  rw [← hz]
  field_simp [hn]
  ring

/-- Exact rank-one pairings, without replacing either signed inverse column. -/
theorem source_moment_pairings (out : Bool) (p : ℕ) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) :
    (sourceBilinearFunctional (externalVector out p (Real.sqrt r : ℂ))
      (oppositeResolvent (Real.sqrt r : ℂ) (weightedSource r hr.le hr1)) =
        -(Real.sqrt (1 - r) : ℂ) * sourceMoment out p (r : ℂ)) ∧
    (sourceBilinearFunctional (externalVector out p (Real.sqrt r : ℂ))
      (resolvent (Real.sqrt r : ℂ) (weightedSource r hr.le hr1)) =
        -(Real.sqrt (1 - r) : ℂ) * sourceJetMoment out p (r : ℂ)) := by
  constructor
  · rw [sourceBilinearFunctional_apply, sourceMoment, ← tsum_mul_left]
    exact tsum_congr (negative_term out p hr hr1)
  · rw [sourceBilinearFunctional_apply, sourceJetMoment, ← tsum_mul_left]
    exact tsum_congr (positive_term out p hr hr1)

/-- The explicit finite source equations retain all four signed labels and every zero-mode boundary. -/
theorem external_displacement_explicit (out : Bool) (p : ℕ) (out' : Bool) (q : ℕ)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    let z : ℂ := Real.sqrt r
    (modeFrequency out p (fun e k => externalJ e k out' q z) +
      modeFrequency out' q (fun e k => externalJ out p e k z) =
      (1 - (r : ℂ)) * (sourceMoment out p r * sourceJetMoment out' q r +
        sourceJetMoment out p r * sourceMoment out' q r) / 2) ∧
    (modeFrequency out p (fun e k => externalT e k out' q z) -
      modeFrequency out' q (fun e k => externalT out p e k z) =
      (1 - (r : ℂ)) * (sourceMoment out p r * sourceJetMoment out' q r -
        sourceJetMoment out p r * sourceMoment out' q r) / 2) := by
  have h := external_displacement out p out' q hr.le hr1
  dsimp only at h ⊢
  rw [(source_moment_pairings out p hr hr1).1, (source_moment_pairings out p hr hr1).2,
    (source_moment_pairings out' q hr hr1).1, (source_moment_pairings out' q hr hr1).2] at h
  have hc : (Real.sqrt (1 - r) : ℂ) ^ 2 = 1 - (r : ℂ) := by
    exact_mod_cast Real.sq_sqrt (by linarith : 0 ≤ 1 - r)
  constructor
  · calc
      _ = _ := h.1
      _ = _ := by rw [← hc]; ring
  · calc
      _ = _ := h.2
      _ = _ := by rw [← hc]; ring


end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalMoments
