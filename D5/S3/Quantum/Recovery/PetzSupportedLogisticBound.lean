/- GID: D5/S3/Quantum/Recovery/PetzSupportedLogisticBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PetzSupportedLogisticBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact logistic evaluation halves the supported ordinary Petz trace bound. -/

import D5.S3.Analytic.PetzLogisticEvaluation
import D5.S3.Quantum.Recovery.PetzSupportedStinespringGram

/-!
# Supported ordinary Petz recovery with the exact upper weight

Coordinatewise logistic evaluation bounds the zero-phase Stinespring
amplitude error. The physical Gram lift and the supported strip loss then
give the trace bound for the actual ordinary recovery.
-/

set_option autoImplicit false

noncomputable section

universe u

open Matrix MeasureTheory
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open D5.S3.Quantum.Divergence.CanonicalChannelDPI
open D5.S3.Quantum.Recovery.PetzSupportedChannelStrip
open D5.S3.Quantum.Recovery.PetzSupportedStinespringGram (recoveredState supported_stinespring_gram)
open D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability (traceNorm_isometry)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction (act)
open PetzExponentialBoundaryEvaluation
open ExponentialGramWeightedEvaluation (exponentialSum frequency)

open private frobenius_sq sum_evaluations traceNorm_gram_sub_le from
  D5.S3.Quantum.Recovery.PetzExponentialBoundaryEvaluation
open private block outer coefficients boundary_eq sourceAmplitude completed sourceAmplitude_unit
  complete_gram sourceBlock physicalFactor dilationColumns phaseMatrix dilationColumns_isometry
  phase_unitary physicalFactor_unitTrace Us columns_isometry upperIntegral_le_loss
  exists_retainedFirst_stinespring card_positive_eigenvalues from
  D5.S3.Quantum.Recovery.PetzSupportedStinespringGram

namespace D5.S3.Quantum.Recovery.PetzSupportedLogisticBound

private theorem boundary_evaluation
    {r c β P Q : Type*} [Fintype r] [Fintype c] [Fintype P] [Fintype Q]
    (b : r → c → β) (o : β → ℝ) (q : Q → ℝ) (p : P → ℝ)
    (A : Matrix r c ℂ) (C : Q × P → Matrix r c ℂ)
    (m : ℕ) (hm : ∀ l, (distinctFrequencies (retainedFrequency (o l) q p)).card ≤ m) :
    let E := petzBoundary b o q p A C
    ‖E 0‖ ^ 2 ≤ (m : ℝ) * ∫ t : ℝ, petzWeight t * ‖E t‖ ^ 2 := by
  dsimp only
  let E := petzBoundary b o q p A C
  let ω (i : r) (j : c) := retainedFrequency (o (b i j)) q p
  let coeff (i : r) (j : c) : Option (Q × P) → ℂ
    | none => A i j
    | some k => -((Real.sqrt (o (b i j) / (q k.1 / p k.2)) : ℂ) * C k i j)
  have hEntry (i : r) (j : c) (t : ℝ) :
      E t i j = exponentialSum (ω i j) (coeff i j) (t : ℂ) := by
    simp only [E, petzBoundary, Matrix.of_apply, exponentialSum, Fintype.sum_option,
      ω, coeff, retainedFrequency, frequency, Complex.ofReal_zero, mul_zero, zero_mul,
      Complex.exp_zero, mul_one, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]
  have hsum (t : ℝ) : ‖E t‖ ^ 2 = ∑ ij : r × c, ‖E t ij.1 ij.2‖ ^ 2 := by
    rw [frobenius_sq, Fintype.sum_prod_type]
  have hDensity : (fun t : ℝ => petzWeight t * ‖E t‖ ^ 2) =
      fun t => ∑ ij : r × c, petzWeight t * ‖E t ij.1 ij.2‖ ^ 2 := by
    funext t
    rw [hsum, Finset.mul_sum]
  change ‖E 0‖ ^ 2 ≤ _
  rw [hsum, hDensity]
  refine (sum_evaluations (m : ℝ) _ _ (fun ij : r × c => ?_)).2
  simp only [hEntry]
  have h := PetzLogisticEvaluation.weighted_evaluation (ω ij.1 ij.2) (coeff ij.1 ij.2)
  have hEnergy : 0 ≤ ∫ t : ℝ, petzWeight t *
      ‖exponentialSum (ω ij.1 ij.2) (coeff ij.1 ij.2) (t : ℂ)‖ ^ 2 :=
    integral_nonneg (fun t => mul_nonneg (petzWeight_pos t).le (sq_nonneg _))
  exact ⟨h.1, h.2.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hm (b ij.1 ij.2))) hEnergy)⟩

set_option maxHeartbeats 800000 in
private theorem trace_bound_of_dilation
    {a b e : Type u} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b] [Fintype e]
    {Φ : QuantumChannel a b} {ρ σ : DensityState a}
    (M : SupportedRelativeModularModel Φ ρ σ) (W : Matrix (b × e) a ℂ) (hW : Wᴴ * W = 1)
    (hAction : ∀ X : Matrix a a ℂ, partialTraceRight (W * X * Wᴴ) = act Φ X)
    (m : ℕ) (hm : let D := M.data
      ∀ l, (distinctFrequencies (retainedFrequency (outer D l) D.ql D.pk)).card ≤ m) :
    let D := M.data
    traceNorm (D.R - recoveredState D) ^ 2 ≤ (4 * (m : ℝ)) *
      (finiteTraceLogRelativeEntropy ρ σ -
        finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ)) := by
  classical
  let D := M.data
  let A : Matrix D.J (D.I ⊕ (b × e)) ℂ := sourceAmplitude D
  let B := completed D W
  let E := petzBoundary (block (e := e) D) (outer D) D.ql D.pk A (coefficients D W)
  have hE (t : ℝ) : E t = A - B t := boundary_eq D W t
  obtain ⟨hd, hSource, hRecovery⟩ := supported_stinespring_gram M W hW hAction
  have hAu : ‖A‖ = 1 := sourceAmplitude_unit M
  have hBu : ‖B 0‖ = 1 :=
    (complete_gram (sourceBlock D) (physicalFactor D W 0) (dilationColumns D W)
      (phaseMatrix D 0) (dilationColumns_isometry D W hW) (phase_unitary D 0)
      (physicalFactor_unitTrace W M hAction 0)).2.1
  have hpoint (t : ℝ) : ‖E t‖ ^ 2 = deficit D (1 / 2) t := by
    rw [hE]
    exact (hd t).1
  have hEval : ‖E 0‖ ^ 2 ≤ (m : ℝ) * ∫ t : ℝ, petzWeight t * deficit D (1 / 2) t := by
    have h := boundary_evaluation (block (e := e) D) (outer D) D.ql D.pk A
      (coefficients D W) m hm
    change ‖E 0‖ ^ 2 ≤ (m : ℝ) * ∫ t : ℝ, petzWeight t * ‖E t‖ ^ 2 at h
    simpa only [hpoint] using h
  have hTrace : traceNorm (B 0 * (B 0)ᴴ - A * Aᴴ) ≤ 2 * ‖E 0‖ := by
    simpa only [hAu, hBu, one_add_one_eq_two, hE, ← neg_sub (A) (B 0),
      norm_neg] using traceNorm_gram_sub_le A (B 0)
  have hLift : Us D * (B 0 * (B 0)ᴴ - A * Aᴴ) * (Us D)ᴴ = recoveredState D - D.R := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
    exact congrArg₂ (· - ·) hRecovery hSource
  have hIsometry := traceNorm_isometry (Us D) (columns_isometry D.hS.1)
    (B 0 * (B 0)ᴴ - A * Aᴴ)
  rw [hLift, ← neg_sub, Foundation.FiniteTraceDistance.traceNorm_neg] at hIsometry
  change traceNorm (D.R - recoveredState D) ^ 2 ≤ _
  calc
    _ = traceNorm (B 0 * (B 0)ᴴ - A * Aᴴ) ^ 2 := by rw [hIsometry]
    _ ≤ (2 * ‖E 0‖) ^ 2 := pow_le_pow_left₀ (traceNorm_nonneg _) hTrace 2
    _ = 4 * ‖E 0‖ ^ 2 := by ring
    _ ≤ (4 * (m : ℝ)) * (∫ t : ℝ, petzWeight t * deficit D (1 / 2) t) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hEval (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_left (upperIntegral_le_loss M) (by positivity)

/-- For the supported finite CPTP model, the ordinary Petz squared trace
error is bounded by the actual finite Umegaki loss times four times one
plus the product of the two output ranks. -/
theorem ordinary_petz_traceNorm_sq_le_entropy_loss
    {a b : Type u} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    {Φ : QuantumChannel a b} {ρ σ : DensityState a}
    (M : SupportedRelativeModularModel Φ ρ σ) :
    let D := M.data
    traceNorm (D.R - recoveredState D) ^ 2 ≤
      (4 * (↑(1 + D.T.rank * D.Q.rank) : ℝ)) *
        (finiteTraceLogRelativeEntropy ρ σ -
          finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ)) := by
  classical
  obtain ⟨W, hW, hAction⟩ := exists_retainedFirst_stinespring Φ
  let D := M.data
  refine trace_bound_of_dilation M W hW hAction (1 + D.T.rank * D.Q.rank) ?_
  change ∀ l : (D.J × D.I) ⊕ D.J,
    (distinctFrequencies (retainedFrequency (outer D l) D.ql D.pk)).card ≤ _
  intro l
  have hcard := Finset.card_image_le
    (s := (Finset.univ : Finset (Option (D.L × D.K))))
    (f := retainedFrequency (outer D l) D.ql D.pk)
  simpa only [distinctFrequencies, Finset.card_univ, Fintype.card_option, Fintype.card_prod,
    card_positive_eigenvalues D.hT, card_positive_eigenvalues D.hQ,
    Nat.mul_comm D.Q.rank D.T.rank, Nat.add_comm (D.T.rank * D.Q.rank) 1] using hcard

#print axioms ordinary_petz_traceNorm_sq_le_entropy_loss

end D5.S3.Quantum.Recovery.PetzSupportedLogisticBound
