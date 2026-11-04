/- GID: D5/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation.claim; result=D5/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation.result; claim=D5/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation.claim
   digest: A binary coherent-state mixture violates the covariance-corrected entropy bound. -/

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

namespace D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation

/-- The one-mode Gaussian Wigner density, in units with Planck's constant equal to one. -/
def gaussianWigner (μx μp a b c x p : ℝ) : ℝ :=
  (2 * Real.pi * Real.sqrt (a * c - b ^ 2))⁻¹ *
    Real.exp (-(c * (x - μx) ^ 2 - 2 * b * (x - μx) * (p - μp) +
      a * (p - μp) ^ 2) / (2 * (a * c - b ^ 2)))

/-- The Wigner function of a finite mixture of Gaussian states. -/
def mixtureWigner (n : ℕ) (w μx μp a b c : Fin n → ℝ) (x p : ℝ) : ℝ :=
  ∑ i, w i * gaussianWigner (μx i) (μp i) (a i) (b i) (c i) x p

def marginalX (W : ℝ → ℝ → ℝ) (x : ℝ) : ℝ := ∫ p, W x p

def marginalP (W : ℝ → ℝ → ℝ) (p : ℝ) : ℝ := ∫ x, W x p

def densityEntropy (f : ℝ → ℝ) : ℝ := -(∫ x, f x * Real.log (f x))

def meanX (W : ℝ → ℝ → ℝ) : ℝ := ∫ r : ℝ × ℝ, r.1 * W r.1 r.2

def meanP (W : ℝ → ℝ → ℝ) : ℝ := ∫ r : ℝ × ℝ, r.2 * W r.1 r.2

def covarianceXX (W : ℝ → ℝ → ℝ) : ℝ :=
  ∫ r : ℝ × ℝ, (r.1 - meanX W) ^ 2 * W r.1 r.2

def covariancePP (W : ℝ → ℝ → ℝ) : ℝ :=
  ∫ r : ℝ × ℝ, (r.2 - meanP W) ^ 2 * W r.1 r.2

def covarianceXP (W : ℝ → ℝ → ℝ) : ℝ :=
  ∫ r : ℝ × ℝ, (r.1 - meanX W) * (r.2 - meanP W) * W r.1 r.2

/-- The covariance-corrected entropy-power uncertainty inequality for all finite Gaussian
mixtures, with finite quadrature entropies and finite phase-space second moments. -/
def claim : Prop :=
  ∀ (n : ℕ) (w μx μp a b c : Fin n → ℝ),
    (∀ i, 0 ≤ w i) → (∑ i, w i) = 1 →
    (∀ i, 0 < a i) → (∀ i, 0 < c i) →
    (∀ i, (1 : ℝ) / 4 ≤ a i * c i - b i ^ 2) →
    let W := mixtureWigner n w μx μp a b c
    Integrable (fun x => marginalX W x * Real.log (marginalX W x)) →
    Integrable (fun p => marginalP W p * Real.log (marginalP W p)) →
    Integrable (fun r : ℝ × ℝ => (r.1 ^ 2 + r.2 ^ 2) * W r.1 r.2) →
    Real.log (Real.pi * Real.exp 1) ≤
      densityEntropy (marginalX W) + densityEntropy (marginalP W) -
        1 / 2 * Real.log (covarianceXX W * covariancePP W /
          (covarianceXX W * covariancePP W - covarianceXP W ^ 2))

private def q (d x : ℝ) : ℝ :=
  (gaussianPDFReal d (1 / 2) x + gaussianPDFReal (-d) (1 / 2) x) / 2

private def witnessW (d x p : ℝ) : ℝ :=
  (gaussianWigner d d (1 / 2) 0 (1 / 2) x p +
    gaussianWigner (-d) (-d) (1 / 2) 0 (1 / 2) x p) / 2

private lemma component_factor (u v x p : ℝ) :
    gaussianWigner u v (1 / 2) 0 (1 / 2) x p =
      gaussianPDFReal u (1 / 2) x * gaussianPDFReal v (1 / 2) p := by
  sorry

private lemma gaussian_moments (m : ℝ) :
    Integrable (fun x => x * gaussianPDFReal m (1 / 2) x) ∧
    Integrable (fun x => x ^ 2 * gaussianPDFReal m (1 / 2) x) ∧
    (∫ x, x * gaussianPDFReal m (1 / 2) x) = m ∧
    (∫ x, x ^ 2 * gaussianPDFReal m (1 / 2) x) = m ^ 2 + 1 / 2 ∧
    (∫ x, (x - m) ^ 2 * gaussianPDFReal m (1 / 2) x) = 1 / 2 := by
  sorry

private lemma gaussian_entropy (m : ℝ) :
    Integrable (fun x => gaussianPDFReal m (1 / 2) x *
      Real.log (gaussianPDFReal m (1 / 2) x)) ∧
    densityEntropy (gaussianPDFReal m (1 / 2)) =
      1 / 2 * Real.log (Real.pi * Real.exp 1) := by
  sorry

private lemma binary_entropy_bound (f g : ℝ → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfi : Integrable f) (hgi : Integrable g)
    (hfm : (∫ x, f x) = 1) (hgm : (∫ x, g x) = 1)
    (hfl : Integrable (fun x => f x * Real.log (f x)))
    (hgl : Integrable (fun x => g x * Real.log (g x)))
    (hql : Integrable (fun x => (f x + g x) / 2 * Real.log ((f x + g x) / 2))) :
    densityEntropy (fun x => (f x + g x) / 2) ≤
      (densityEntropy f + densityEntropy g) / 2 + Real.log 2 := by
  sorry

private lemma mixture_entropy_integrable (d : ℝ) :
    Integrable (fun x => q d x * Real.log (q d x)) := by
  sorry

private lemma marginals (d : ℝ) :
    marginalX (witnessW d) = q d ∧ marginalP (witnessW d) = q d := by
  sorry

private lemma moments (d : ℝ) :
    meanX (witnessW d) = 0 ∧ meanP (witnessW d) = 0 ∧
    covarianceXX (witnessW d) = d ^ 2 + 1 / 2 ∧
    covariancePP (witnessW d) = d ^ 2 + 1 / 2 ∧
    covarianceXP (witnessW d) = d ^ 2 := by
  sorry

private lemma second_integrable (d : ℝ) :
    Integrable (fun r : ℝ × ℝ => (r.1 ^ 2 + r.2 ^ 2) * witnessW d r.1 r.2) := by
  sorry

private lemma entropy_upper (d : ℝ) :
    densityEntropy (q d) + densityEntropy (q d) ≤
      Real.log (Real.pi * Real.exp 1) + 2 * Real.log 2 := by
  have h := binary_entropy_bound (gaussianPDFReal d (1 / 2))
    (gaussianPDFReal (-d) (1 / 2)) (gaussianPDFReal_nonneg _ _)
    (gaussianPDFReal_nonneg _ _) (integrable_gaussianPDFReal _ _)
    (integrable_gaussianPDFReal _ _)
    (integral_gaussianPDFReal_eq_one _ (by norm_num))
    (integral_gaussianPDFReal_eq_one _ (by norm_num))
    (gaussian_entropy d).1 (gaussian_entropy (-d)).1 (mixture_entropy_integrable d)
  change densityEntropy (q d) ≤ _ at h
  rw [(gaussian_entropy d).2, (gaussian_entropy (-d)).2] at h
  linarith

private lemma correction_violation :
    2 * Real.log 2 < 1 / 2 * Real.log
      (((6 : ℝ) ^ 2 + 1 / 2) * (6 ^ 2 + 1 / 2) /
        (((6 : ℝ) ^ 2 + 1 / 2) * (6 ^ 2 + 1 / 2) - (6 ^ 2) ^ 2)) := by
  sorry

/-- The equal mixture of coherent states with means `(6,6)` and `(-6,-6)` refutes
the universal covariance-corrected quadrature entropy inequality. -/
theorem result : ¬ claim := by
  intro h
  let m : Fin 2 → ℝ := ![6, -6]
  have hw : mixtureWigner 2 (fun _ => 1 / 2) m m
      (fun _ => 1 / 2) (fun _ => 0) (fun _ => 1 / 2) = witnessW 6 := by
    funext x p
    simp only [mixtureWigner, Fin.sum_univ_two, m, Matrix.cons_val_zero,
      Matrix.cons_val_one, witnessW]
    ring
  have hc := h 2 (fun _ => 1 / 2) m m (fun _ => 1 / 2) (fun _ => 0)
    (fun _ => 1 / 2) (fun _ => by norm_num) (by norm_num [Fin.sum_univ_two])
    (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num)
  dsimp only at hc
  rw [hw, (marginals 6).1, (marginals 6).2] at hc
  have hc := hc (mixture_entropy_integrable 6) (mixture_entropy_integrable 6)
    (second_integrable 6)
  rw [(moments 6).2.2.1, (moments 6).2.2.2.1, (moments 6).2.2.2.2] at hc
  have hu := entropy_upper 6
  have hv := correction_violation
  linarith

end D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation
