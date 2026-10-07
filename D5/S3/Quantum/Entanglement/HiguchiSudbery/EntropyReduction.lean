/- GID: D5/S3/Quantum/Entanglement/HiguchiSudbery/EntropyReduction
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/HiguchiSudbery/EntropyReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: EntropyReduction for the sharp four-qubit marginal entropy bound. -/

/-
The private declarations are auxiliary steps consumed by the entropy maximum proof.
admission_basis: escape-witness
Same-delivery prerequisite: D5.S3.Quantum.Entanglement.HiguchiSudbery.HermiteEntropy.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Quantum.Entanglement.HiguchiSudbery.HermiteEntropy
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

noncomputable section
namespace D5.S3.Quantum.Entanglement.HiguchiSudbery

open private
  c0 c1 c2 c3
  from D5.S3.Quantum.Entanglement.HiguchiSudbery.HermiteEntropy

open Real
open scoped BigOperators
set_option maxHeartbeats 0

private def A : ℝ := (11 + 2*log 2 - 9*log 3)/2

private def B : ℝ := 3*(5*log 3-6)/2

private def C : ℝ := 54*(log 3-1)

private lemma coefficient_signs /- proof_shape: bind-only; consumer: EntropyReduction.entropy_three_spectra -/ : B < 0 ∧ 0 < C := by
  have hlo : 1 < log 3 := (lt_log_iff_exp_lt (by norm_num)).mpr exp_one_lt_three
  have hup : log 3 < 6/5 := by
    apply (log_lt_iff_lt_exp (by norm_num)).mpr
    have h := sum_le_exp_of_nonneg (x := (6/5 : ℝ)) (by norm_num) 4
    norm_num [Finset.sum_range_succ] at h
    linarith
  dsimp [B,C]
  constructor <;> linarith

private lemma polynomial_spectral_sum /- proof_shape: bind-only; consumer: EntropyReduction.entropy_spectral_bound -/ (v : Fin 4 → ℝ) (hv : ∑ i, v i = 1) :
    ∑ i, pNat (v i) = A + B*(fun v => dotProduct v v) v +
      C*(fun v => (Multiset.ofList [v 0, v 1, v 2, v 3]).esymm 3) v := by
  norm_num [Fin.sum_univ_succ] at hv
  change v 0 + (v 1 + (v 2 + v 3)) = 1 at hv
  have h3 : v 3 = 1-v 0-v 1-v 2 := by linarith
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, dotProduct, Multiset.esymm, Multiset.powersetCard, Multiset.powersetCardAux, List.sublistsLenAux]
  change pNat (v 0) + (pNat (v 1) + (pNat (v 2) + pNat (v 3))) = _
  unfold pNat A B C
  norm_num [Fin.sum_univ_succ]
  simp [h3, dotProduct, Fin.sum_univ_succ, Multiset.esymm, Multiset.powersetCard, Multiset.powersetCardAux, List.sublistsLenAux]
  ring

private lemma entropy_spectral_bound /- proof_shape: content; escape_witness: HermiteMajorant.double_contact_nonnegative; consumer: EntropyReduction.entropy_three_spectra -/ (v : Fin 4 → ℝ)
    (hv : ∑ i, v i = 1) (hpos : ∀ i, 0 ≤ v i) :
    (∑ i, negMulLog (v i)) ≤ A + B*(fun v => dotProduct v v) v +
      C*(fun v => (Multiset.ofList [v 0, v 1, v 2, v 3]).esymm 3) v := by
  rw [← polynomial_spectral_sum v hv]
  exact Finset.sum_le_sum (fun i _ => hermite_majorant (v i) (hpos i))

private lemma entropy_three_spectra /- proof_shape: content; escape_witness: HermiteMajorant.double_contact_nonnegative; consumer: HS4Assembly.hs4_of_spectral_e3 -/ (v : Fin 3 → Fin 4 → ℝ)
    (hv : ∀ k, ∑ i, v k i = 1) (hpos : ∀ k i, 0 ≤ v k i)
    (hP : 1 ≤ ∑ k, (fun v => dotProduct v v) (v k))
    (hE : (∑ k, (fun v => (Multiset.ofList [v 0, v 1, v 2, v 3]).esymm 3) (v k)) ≤ 5/36) :
    (∑ k, ∑ i, negMulLog (v k i)) / (3*log 2) ≤ 1 + (1/2)*logb 2 3 := by
  have h := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) =>
    entropy_spectral_bound (v k) (hv k) (hpos k))
  have hs : (∑ k, (A + B*(fun v => dotProduct v v) (v k) +
      C*(fun v => (Multiset.ofList [v 0, v 1, v 2, v 3]).esymm 3) (v k))) =
      3*A + B*(∑ k, (fun v => dotProduct v v) (v k)) +
        C*(∑ k, (fun v => (Multiset.ofList [v 0, v 1, v 2, v 3]).esymm 3) (v k)) := by
    simp [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hs] at h
  have hB := mul_le_mul_of_nonpos_left hP coefficient_signs.1.le
  have hC := mul_le_mul_of_nonneg_left hE coefficient_signs.2.le
  have hl : 0 < log 2 := log_pos (by norm_num)
  rw [div_le_iff₀ (mul_pos (by norm_num) hl), logb]
  have ht : (1+(1/2)*(log 3/log 2))*(3*log 2) = 3*log 2 + (3/2)*log 3 := by
    field_simp <;> ring
  rw [ht]
  dsimp [A,B,C] at *
  nlinarith

end D5.S3.Quantum.Entanglement.HiguchiSudbery
