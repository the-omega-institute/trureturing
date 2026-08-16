/- GID: D5/S3/Quantum/Sharpness/SpectralPairingCapacity
   generality: G
   mirror-B: D5/B/S3/Quantum/Sharpness/SpectralPairingCapacity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Doubly stochastic mixing cannot increase spectral pairing capacity. -/

import D5.S3.Weil.ZetaLinear.VonNeumann

/-!
# Spectral Pairing Capacity

For decreasing state and observable spectra, majorization is witnessed by a doubly stochastic
matrix. The spectral pairing capacity cannot increase under that mixing.
-/

noncomputable section

open Finset Matrix

namespace D5.S3.Quantum.Sharpness.SpectralPairingCapacity

/-- The capacity obtained by pairing a state spectrum with the difference between an observable
spectrum and its reversal. -/
def spectralPairingCapacity {n : ℕ} (r a : Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, r i * (a i - a (Fin.rev i))

/-- Spectral pairing capacity is monotone under majorization witnessed by a doubly stochastic
matrix: mixing a decreasing spectrum cannot increase its capacity against a decreasing observable
spectrum. -/
theorem spectral_pairing_capacity_monotone_of_doubly_stochastic
    {n : ℕ} {r r' a : Fin n → ℝ} {S : Matrix (Fin n) (Fin n) ℝ}
    (hr' : Antitone r') (ha : Antitone a)
    (hS : S ∈ doublyStochastic ℝ (Fin n)) (hr : r = S *ᵥ r') :
    spectralPairingCapacity r a ≤ spectralPairingCapacity r' a := by
  have hgap : Antitone (fun i => a i - a (Fin.rev i)) := by
    intro i j hij
    have hforward := ha hij
    have hreverse := ha (Fin.rev_le_rev.mpr hij)
    linarith
  have hcore :
      ∑ i, (S *ᵥ r') i * (a i - a (Fin.rev i)) ≤
        ∑ i, r' i * (a i - a (Fin.rev i)) := by
    have h := RHLinalg.bilinear_doublyStochastic_le_of_monovary
      (hgap.monovary_antitone hr') hS
    simpa [Matrix.mulVec, dotProduct, mul_sum, mul_comm, mul_left_comm, mul_assoc] using h
  unfold spectralPairingCapacity
  rw [hr]
  exact mul_le_mul_of_nonneg_left hcore (by norm_num)

end D5.S3.Quantum.Sharpness.SpectralPairingCapacity
