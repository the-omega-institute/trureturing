/- GID: D5/S3/Quantum/Schatten/FractionalSchattenAlignmentRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Schatten/FractionalSchattenAlignmentRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Schatten/FractionalSchattenAlignmentRefutation.claim; result=D5/S3/Quantum/Schatten/FractionalSchattenAlignmentRefutation.result; claim=D5/S3/Quantum/Schatten/FractionalSchattenAlignmentRefutation.claim
   digest: Word-trace domination fails to order Schatten norms at exponent three halves. -/

import D5.S3.Quantum.Schatten.Holder
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Schatten.FractionalSchattenAlignmentRefutation

def wordProduct {m : ℕ} (a₀ a₁ : Matrix (Fin m) (Fin m) ℂ) (s : List Bool) :=
  (s.map (fun b => if b then a₁ else a₀)).prod

def claim : Prop :=
  ∀ (m : ℕ) (a₀ a₁ b₀ b₁ : Matrix (Fin m) (Fin m) ℂ),
    a₀.PosSemidef → a₁.PosSemidef → b₀.PosSemidef → b₁.PosSemidef →
    a₀.charpoly = b₀.charpoly → a₁.charpoly = b₁.charpoly →
    (∀ s : List Bool, (wordProduct a₀ a₁ s).trace.im = 0 ∧
      ‖(wordProduct b₀ b₁ s).trace‖ ≤ (wordProduct a₀ a₁ s).trace.re) →
    ∀ p : ℝ, 1 ≤ p → schattenNorm (b₀ + b₁) p ≤ schattenNorm (a₀ + a₁) p

private def a₀ : Matrix (Fin 4) (Fin 4) ℂ := diagonal ![0, 1, 1, 2]
private def a₁ : Matrix (Fin 4) (Fin 4) ℂ := diagonal ![1, 0, 1, 2]
private def b₁ : Matrix (Fin 4) (Fin 4) ℂ := diagonal ![0, 1, 2, 1]

private lemma word_diagonal {m : ℕ} (d₀ d₁ : Fin m → ℂ) (s : List Bool) :
    wordProduct (diagonal d₀) (diagonal d₁) s =
      diagonal (fun k => d₀ k ^ s.count false * d₁ k ^ s.count true) := by
  sorry

private lemma trace_forms (s : List Bool) :
    (wordProduct a₀ a₁ s).trace =
      ((0 ^ s.count false + 0 ^ s.count true + 1 + 2 ^ (s.count false + s.count true) : ℕ) : ℂ) ∧
    (wordProduct a₀ b₁ s).trace =
      ((0 ^ (s.count false + s.count true) + 1 + 2 ^ s.count false +
        2 ^ s.count true : ℕ) : ℂ) := by
  sorry

private lemma nat_gap (m n : ℕ) :
    0 ^ (m + n) + 1 + 2 ^ m + 2 ^ n ≤ 0 ^ m + 0 ^ n + 1 + 2 ^ (m + n) := by
  sorry

private lemma witness_psd : a₀.PosSemidef ∧ a₁.PosSemidef ∧ b₁.PosSemidef := by
  sorry

private lemma witness_spectra : a₁.charpoly = b₁.charpoly := by
  sorry

private lemma word_bounds (s : List Bool) :
    (wordProduct a₀ a₁ s).trace.im = 0 ∧
      ‖(wordProduct a₀ b₁ s).trace‖ ≤ (wordProduct a₀ a₁ s).trace.re := by
  obtain ⟨ha, hb⟩ := trace_forms s
  rw [ha, hb]
  simpa using nat_gap (s.count false) (s.count true)

private lemma norm_diagonal {m : ℕ} (d : Fin m → ℝ) (hd : ∀ k, 0 ≤ d k) (p : ℝ) :
    schattenNorm (diagonal (fun k => (d k : ℂ))) p = (∑ k, d k ^ p) ^ (1 / p) := by
  sorry

private lemma norm_reverse : schattenNorm (a₀ + a₁) (3 / 2) <
    schattenNorm (a₀ + b₁) (3 / 2) := by
  sorry

theorem result : ¬ claim := by
  intro h
  obtain ⟨h₀, h₁, h₂⟩ := witness_psd
  exact (not_le_of_gt norm_reverse)
    (h 4 a₀ a₁ a₀ b₁ h₀ h₁ h₀ h₂ rfl witness_spectra word_bounds (3 / 2) (by norm_num))

end D5.S3.Quantum.Schatten.FractionalSchattenAlignmentRefutation
