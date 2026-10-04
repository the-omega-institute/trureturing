/- GID: D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight
   generality: G
   mirror-B: D5/B/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The block Bloch state strictly maximizes HKNN weight at every positive even size. -/

/-
proof_shape: result: bind-only
escape_witness: none for this binding conclusion; the foundation content is on its live path.
admission_basis: open-problem-resolution (#12736; Proved)
Direct frozen dependencies: none on immutable baseline; foundation imports belong to this delivery.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Quantum.SpinChains.HKNNBlockBlochLargestWeight.SpectralComparison
import D5.S3.Quantum.SpinChains.HKNNBlockBlochLargestWeight.PairingCoefficients
import D5.S1.Phase.SeatTowerCombinatorics

noncomputable section
open scoped BigOperators ComplexConjugate
open Fin.NatCast
open D5.S1.Phase.SeatTowerCombinatorics (Stationing)
open D5.S3.Zeros.Convolution.PerfectMatchingCount

namespace D5.S3.Quantum.SpinChains.HKNNBlockBlochLargestWeight

def claim : Prop := ∀ (m : ℕ) (hm : 1 ≤ m),
  let middle : Fin (2 * m) := ⟨m, by omega⟩
  bloch m (block m) middle ≠ 0 ∧
  ∀ (σ : Stationing (2 * m)) (t : Fin (2 * m)), bloch m σ t ≠ 0 →
    ¬ ((∃ j : ℕ, σ = ((shift m)^[j]) (block m)) ∧ t.val = m) →
    weight m σ t < weight m (block m) middle

theorem result : claim := by
  classical
  have psiVector_ne_zero (m : ℕ) : psiVector m ≠ 0 := by
    intro he
    have hc := congrArg (fun v : State m => v (block m)) he
    have hp : psi m (block m) = 0 := by
      have hh : (psi m (block m) : ℂ) = 0 := by simpa [psiVector] using hc
      exact_mod_cast hh
    have ha := (pairing_data m).2.1.2.1
    rw [hp] at ha
    have hk := (pairing_data m).2.1.1
    norm_cast at ha
    omega
  intro m hm
  have : NeZero (2 * m) := ⟨by omega⟩
  dsimp only
  let middle : Fin (2 * m) := ⟨m, by omega⟩
  change bloch m (block m) middle ≠ 0 ∧ _
  have hweight := (spectral_comparison m hm).2.1 middle rfl
  have hpos : 0 < weight m (block m) middle := by
    rw [hweight]
    apply div_pos
    · have hn : (0 : ℝ) < (2 * m : ℕ) := by exact_mod_cast (by omega : 0 < 2 * m)
      have hk : (0 : ℝ) < (K m : ℝ) := by exact_mod_cast (pairing_data m).2.1.1
      exact mul_pos hn (sq_pos_of_pos hk)
    · exact sq_pos_of_pos (norm_pos_iff.mpr (psiVector_ne_zero m))
  constructor
  · intro he
    have hn := (spectral_comparison m hm).1 middle
    rw [he, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hn
    norm_cast at hn
    omega
  · intro σ t hb hneq
    by_cases ht : t.val = m
    · have hσ : ¬ isArc m σ := fun h => hneq ⟨h, ht⟩
      rw [hweight]
      exact (spectral_comparison m hm).2.2.1 σ t hb hσ
    · rw [(spectral_comparison m hm).2.2.2 σ t ht]
      exact hpos

#print axioms result

end D5.S3.Quantum.SpinChains.HKNNBlockBlochLargestWeight
