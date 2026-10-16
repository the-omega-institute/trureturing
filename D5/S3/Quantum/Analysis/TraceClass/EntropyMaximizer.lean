/- GID: D5/S3/Quantum/Analysis/TraceClass/EntropyMaximizer
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/TraceClass/EntropyMaximizer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bounded entropy and a unique global maximum from finite continuous entropy. -/

import D5.S3.Quantum.Analysis.TraceClass.EntropyConcavity
import D5.S3.Analytic.Convexity.StrongConcavityAttainment

noncomputable section
open scoped ComplexOrder ENNReal

namespace QuantumLogEnergy

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Actual finite continuous spectral entropy is bounded above on a nonempty closed
convex family of positive trace-one operators. It has a unique global maximizer in
that family, with a trace-norm quadratic deficit. No compactness, separability,
energy condition or previously bounded entropy is assumed. -/
theorem exists_unique_entropy_maximizer {A : Set (TraceClass H)}
    (hne : A.Nonempty) (hclosed : IsClosed A) (hconv : Convex ℝ A)
    (hp : ∀ rho ∈ A, 0 ≤ rho.1)
    (ht : ∀ rho ∈ A, (trace rho.1 (TraceClass.isTraceClass_coe rho)).re = 1)
    (hf : ∀ (rho) (h : rho ∈ A), spectralEntropy
      (⟨rho, hp rho h, density_le_one rho (hp rho h) (ht rho h)⟩ : Reference H) ≠ ∞)
    (hcont : ContinuousOn realEntropy A) :
    BddAbove (realEntropy '' A) ∧
      ∃ gamma ∈ A, IsMaxOn realEntropy A gamma ∧
        (∀ rho ∈ A, (1 / 8 : ℝ) * ‖rho - gamma‖ ^ 2 ≤
          realEntropy gamma - realEntropy rho) ∧
        ∀ rho ∈ A, IsMaxOn realEntropy A rho → rho = gamma := by
  classical
  have hstrong := strongConcaveOn_realEntropy hconv hp ht hf
  have hnorm (rho : TraceClass H) (hr : rho ∈ A) : ‖rho‖ = 1 := by
    rw [TraceClass.norm_eq_traceNorm, traceNorm_eq_re_trace _ (hp rho hr), ht rho hr]
  have hnonneg (rho : TraceClass H) : 0 ≤ realEntropy rho := by
    unfold realEntropy
    split
    · exact ENNReal.toReal_nonneg
    · exact le_rfl
  have hbdd : BddAbove (realEntropy '' A) := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨δ, hδ, hlocal⟩ := Metric.continuousWithinAt_iff.mp (hcont x hx) 1 zero_lt_one
    let t : ℝ := min (1 / 2) (δ / 4)
    have htpos : 0 < t := lt_min (by norm_num) (by positivity)
    have htone : t ≤ 1 / 2 := min_le_left _ _
    have htδ : t ≤ δ / 4 := min_le_right _ _
    have hta : 0 ≤ 1 - t := by linarith
    refine ⟨(realEntropy x + 1) / t, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    let z : TraceClass H := (1 - t) • x + t • y
    have hz : z ∈ A := hconv hx hy hta htpos.le (by ring)
    have hdiff : z - x = t • (y - x) := by
      dsimp [z]
      rw [sub_smul, one_smul, smul_sub]
      abel
    have hdist : dist z x < δ := by
      rw [dist_eq_norm, hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
      have hdiam : ‖y - x‖ ≤ 2 := by
        calc
          ‖y - x‖ ≤ ‖y‖ + ‖x‖ := norm_sub_le _ _
          _ = 2 := by rw [hnorm y hy, hnorm x hx]; norm_num
      have hmul := mul_le_mul_of_nonneg_left hdiam htpos.le
      nlinarith
    have hlocal' : realEntropy z < realEntropy x + 1 := by
      have hd := hlocal hz hdist
      rw [Real.dist_eq] at hd
      have := (abs_lt.mp hd).2
      linarith
    have hconc := hstrong.2 hx hy hta htpos.le (show (1 - t) + t = 1 by ring)
    change (1 - t) * realEntropy x + t * realEntropy y +
      (1 - t) * t * ((1 / 2 : ℝ) / 2 * ‖x - y‖ ^ 2) ≤ realEntropy z at hconc
    have hbase := mul_nonneg hta (hnonneg x)
    have hreward : 0 ≤ (1 - t) * t * ((1 / 2 : ℝ) / 2 * ‖x - y‖ ^ 2) := by
      positivity
    apply (le_div_iff₀ htpos).mpr
    nlinarith
  refine ⟨hbdd, ?_⟩
  obtain ⟨gamma, hg, hmax, hgap, huniq⟩ :=
    D5.S3.Analytic.Convexity.StrongConcavityAttainment.exists_unique_maximizer
      hne hclosed.isComplete (by norm_num : (0 : ℝ) < 1 / 2) hstrong
      hcont.upperSemicontinuousOn hbdd
  refine ⟨gamma, hg, hmax, ?_, huniq⟩
  intro rho hr
  simpa only [show (1 / 2 : ℝ) / 4 = 1 / 8 by norm_num] using hgap rho hr

#print axioms exists_unique_entropy_maximizer

end QuantumLogEnergy
