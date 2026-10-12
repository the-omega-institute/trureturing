/- GID: D5/S3/Entropy/ProductGenerator/EntropyTruncation
   generality: G
   mirror-B: D5/B/S3/Entropy/ProductGenerator/EntropyTruncation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Entropy truncation for exact finite product sources of an interior parity law. -/

import D5.S3.Entropy.MaxEntropy
import D5.S3.Analytic.ReflectedSpectrum.ParityConditionedMoments

set_option autoImplicit false
open scoped BigOperators

namespace D5.S3.Entropy.ProductGenerator.EntropyTruncation
noncomputable section

open D5.S3.Entropy.MaxEntropy
open D5.S3.Analytic.ReflectedSpectrum.ParityConditionedMoments (paritySign)

local notation "σ" b => ((paritySign b : ℤ) : ℝ)

/-- Density of independent binary coordinates with the specified means. -/
def productChannel {n : ℕ} (m : Fin n → ℝ) (x : Fin n → Fin 2) : ℝ :=
  ∏ i, (1 + m i * σ (x i)) / 2

/-- The interior parity law, including its fair normalization. -/
def parityMass {n : ℕ} (κ : ℝ) (x : Fin n → Fin 2) : ℝ :=
  (2 : ℝ)⁻¹ ^ n * (1 + κ * ∏ i, σ (x i))

/-- All parameters of one exact finite product-source realization. -/
structure ExactGenerator (n : ℕ) (κ : ℝ) (Z : Type*) [Fintype Z] where
  weight : Z → ℝ
  mean : Z → Fin n → ℝ
  weight_pos : ∀ z, 0 < weight z
  weight_sum : ∑ z, weight z = 1
  mean_bound : ∀ z i, |mean z i| ≤ 1
  exact_mass : ∀ x, ∑ z, weight z * productChannel (mean z) x = parityMass κ x

/-- The full signed product moment of a source component. -/
def componentMoment {n : ℕ} (m : Fin n → ℝ) : ℝ := ∏ i, m i

/-- The total absolute parity charge in one realized generator. -/
def absoluteCharge {n : ℕ} {κ : ℝ} {Z : Type*} [Fintype Z]
    (G : ExactGenerator n κ Z) : ℝ :=
  ∑ z, G.weight z * |componentMoment (G.mean z)|

/-- The parity defect carried by labels below the entropy cutoff. -/
def smallDefect {n : ℕ} {κ : ℝ} {Z : Type*} [Fintype Z]
    (G : ExactGenerator n κ Z) (L : ℝ) : ℝ :=
  ∑ z, if G.weight z < Real.exp (-L) then
    G.weight z * (1 - |componentMoment (G.mean z)|) else 0

end
end D5.S3.Entropy.ProductGenerator.EntropyTruncation
