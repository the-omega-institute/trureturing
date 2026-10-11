/- GID: D5/S3/Quantum/Petz/SpectralPetz
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Petz spectral curvature is monotone under finite prefix mixing of faithful ordered spectra. -/

import D5.S3.Quantum.Petz.DittmannLemmaFourComplete
import D5.S3.Quantum.Petz.SpectralKernel
import D5.S3.Quantum.Petz.OrderedMixingReduction

namespace D5.S3.Quantum.Petz.SpectralPetz

open Set BigOperators
open D5.S3.Quantum.Petz.SpectralKernel
open D5.S3.Quantum.Petz.OrderedMixingReduction
open D5.S3.Quantum.Petz.MixingIteration
open D5.S3.Quantum.Petz.DittmannLemmaFourComplete

def claim : Prop := ∀ n : ℕ, 1 ≤ n → ∀ lam mu : Fin n → ℝ,
  (∀ i, 0 < lam i) → (∀ i, 0 < mu i) → (∑ i, lam i) = 1 → (∑ i, mu i) = 1 →
  Antitone lam → Antitone mu →
  (∀ k : ℕ, k ≤ n → D5.S3.Quantum.Petz.MixingIteration.prefixSum mu k ≤
    D5.S3.Quantum.Petz.MixingIteration.prefixSum lam k) →
  D5.S3.Quantum.Petz.SpectralKernel.spectralS lam ≤
    D5.S3.Quantum.Petz.SpectralKernel.spectralS mu

theorem result : claim := by
  intro n hn lam mu hlam hmu hsum_lam hsum_mu hlam_order hmu_order hprefix
  rw [D5.S3.Quantum.Petz.SpectralKernel.spectralS_eq_spectralHs lam hlam,
    D5.S3.Quantum.Petz.SpectralKernel.spectralS_eq_spectralHs mu hmu]
  obtain ⟨h62, h63, h64, h65⟩ := lemma4
  apply D5.S3.Quantum.Petz.OrderedMixingReduction.derivative_pair_transfer_reduction
    D5.S3.Quantum.Petz.SpectralKernel.spectralHs
  · intro x σ
    exact spectralHs_perm x σ
  · intro x hx i j hij t ht
    let z : Fin n → ℝ := transfer x i j t
    have hz : ∀ a, 0 < z a := by
      intro a
      by_cases hai : a = i
      · subst a
        simp [z, transfer, hij, hij.symm]
        nlinarith [hx i, hx j, ht.1, ht.2]
      · by_cases haj : a = j
        · subst a
          simp [z, transfer, hij, hij.symm]
          nlinarith [hx i, hx j, ht.1, ht.2]
        · simpa [z, transfer, hai, haj] using hx a
    have hbase := spectralHs_transfer_hasDerivAt z hz i j
    have hscale : HasDerivAt (fun r : ℝ => (r - t) * (x j - x i))
        (x j - x i) t := by
      simpa using ((hasDerivAt_id t).sub_const t).mul_const (x j - x i)
    have hcomp := hbase.comp_of_eq t hscale (by simp)
    have heq : (fun r : ℝ => spectralHs (pairTransfer z i j ((r - t) * (x j - x i)))) =
        (fun r : ℝ => spectralHs (transfer x i j r)) := by
      funext r
      congr 1
      funext a
      by_cases hai : a = i
      · subst a
        simp [z, transfer, pairTransfer, hij, hij.symm]
        ring
      · by_cases haj : a = j
        · subst a
          simp [z, transfer, pairTransfer, hij, hij.symm]
          ring
        · simp [z, transfer, pairTransfer, hai, haj, hij, hij.symm]
    have hcomp' := hcomp
    change HasDerivAt
      (fun r => spectralHs (pairTransfer z i j ((r - t) * (x j - x i))))
      _ t at hcomp'
    rw [heq] at hcomp'
    exact hcomp'.differentiableAt
  · intro x hx i j hij horder
    have hderiv := spectralHs_transfer_hasDerivAt x hx i j
    have hnonneg := spectralHs_transfer_monotone h62 h63 h64 h65 x hx i j horder
    rw [hderiv.deriv] at hnonneg
    have heq : (fun r : ℝ => spectralHs (pairTransfer x i j r)) =
        (fun r : ℝ => spectralHs (fun a => x a + r * pairDirection i j a)) := by
      funext r
      congr 1
      funext a
      by_cases hai : a = i
      · subst a
        simp [pairTransfer, pairDirection, hij]
      · by_cases haj : a = j
        · subst a
          simp [pairTransfer, pairDirection, hij, hij.symm]
        · simp [pairTransfer, pairDirection, hai, haj]
    rw [heq] at hderiv
    refine ⟨_, hderiv, ?_⟩
    exact hnonneg
  · exact hlam
  · exact hmu
  · exact hmu_order
  · have hsum : (∑ a, lam a) = ∑ a, mu a := by linarith
    exact hsum
  · exact hprefix

end D5.S3.Quantum.Petz.SpectralPetz
