/- GID: D5/S3/Quantum/PureState/NoRepetitionSequenceUnambiguousDiscrimination
   generality: I
   mirror-B: D5/B/S3/Quantum/PureState/NoRepetitionSequenceUnambiguousDiscrimination
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Optimal unambiguous discrimination of injectively labelled product sequences. -/

import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace D5.S3.Quantum.PureState.NoRepetitionSequenceUnambiguousDiscrimination

open scoped ComplexOrder Matrix MatrixOrder
open Matrix
open Classical

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Ordered sequences of distinct labels. -/
abbrev Label (N k : ℕ) := {x : Fin k → Fin N // Function.Injective x}

/-- Normalized single-system states with common real overlap. -/
def IsEquiangular {N : ℕ} (ψ : Fin N → Fin N → ℂ) (s : ℝ) : Prop :=
  (∀ i, star (ψ i) ⬝ᵥ ψ i = 1) ∧
  ∀ i j, i ≠ j → star (ψ i) ⬝ᵥ ψ j = (s : ℂ)

/-- The tensor product in the coordinate basis. -/
def productState {N k : ℕ} (ψ : Fin N → Fin N → ℂ)
    (x : Label N k) (a : Fin k → Fin N) : ℂ := ∏ j, ψ (x.val j) (a j)

/-- Positive effects, including the inconclusive effect, with no erroneous output. -/
def IsUnambiguousMeasurement {N k : ℕ}
    (φ : Label N k → (Fin k → Fin N) → ℂ)
    (E : Label N k → Matrix (Fin k → Fin N) (Fin k → Fin N) ℂ)
    (E₀ : Matrix (Fin k → Fin N) (Fin k → Fin N) ℂ) : Prop :=
  (∀ x, (E x).PosSemidef) ∧ E₀.PosSemidef ∧
  (∑ x, E x) + E₀ = 1 ∧
  ∀ x y, y ≠ x → star (φ y) ⬝ᵥ ((E x) *ᵥ φ y) = 0

/-- Uniform average probability of a conclusive correct output. -/
def averageSuccess {N k : ℕ}
    (φ : Label N k → (Fin k → Fin N) → ℂ)
    (E : Label N k → Matrix (Fin k → Fin N) (Fin k → Fin N) ℂ) : ℝ :=
  (1 / (Fintype.card (Label N k) : ℝ)) *
    ∑ x, (star (φ x) ⬝ᵥ ((E x) *ᵥ φ x)).re

/-- The effect of a tuple of independent single-system outcomes. -/
def productEffect {N k : ℕ}
    (F : Option (Fin N) → Matrix (Fin N) (Fin N) ℂ)
    (o : Fin k → Option (Fin N)) : Matrix (Fin k → Fin N) (Fin k → Fin N) ℂ :=
  fun a b => ∏ j, F (o j) (a j) (b j)

/-- Classical processing sums the product effects assigned to the same output. -/
noncomputable def inducedEffect {N k : ℕ}
    (F : Option (Fin N) → Matrix (Fin N) (Fin N) ℂ)
    (d : (Fin k → Option (Fin N)) → Option (Label N k))
    (z : Option (Label N k)) : Matrix (Fin k → Fin N) (Fin k → Fin N) ℂ :=
  ∑ o, if d o = z then productEffect F o else 0

/-- The same single-system POVM is applied at each position, then processed classically. -/
def IsProductProtocol {N k : ℕ}
    (F : Option (Fin N) → Matrix (Fin N) (Fin N) ℂ)
    (d : (Fin k → Option (Fin N)) → Option (Label N k))
    (E : Label N k → Matrix (Fin k → Fin N) (Fin k → Fin N) ℂ)
    (E₀ : Matrix (Fin k → Fin N) (Fin k → Fin N) ℂ) : Prop :=
  (∀ o, (F o).PosSemidef) ∧ (∑ o, F o) = 1 ∧
  (∀ x, E x = inducedEffect F d (some x)) ∧ E₀ = inducedEffect F d none

/-- The proposed optimum, including the forced final label for a full permutation. -/
def value (N k : ℕ) (s : ℝ) : ℝ :=
  if k < N then (1 - s) ^ k else (1 - s) ^ (N - 1) * (1 + (N - 1 : ℕ) * s)

/-- The global upper bound and attainment by an independent product measurement. -/
def claim : Prop :=
  ∀ (N k : ℕ), 3 ≤ N → 2 ≤ k → k ≤ N →
  ∀ s : ℝ, 0 < s → s < 1 →
  ∀ ψ : Fin N → Fin N → ℂ, IsEquiangular ψ s →
    (∀ E E₀, IsUnambiguousMeasurement (productState (k := k) ψ) E E₀ →
      averageSuccess (productState (k := k) ψ) E ≤ value N k s) ∧
    ∃ F d E E₀, IsProductProtocol (k := k) F d E E₀ ∧
      IsUnambiguousMeasurement (productState (k := k) ψ) E E₀ ∧
      averageSuccess (productState (k := k) ψ) E = value N k s

private def gram {N k : ℕ} (φ : Label N k → (Fin k → Fin N) → ℂ) :
    Matrix (Label N k) (Label N k) ℂ := fun x y => star (φ x) ⬝ᵥ φ y

private def probabilities {N k : ℕ}
    (φ : Label N k → (Fin k → Fin N) → ℂ)
    (E : Label N k → Matrix (Fin k → Fin N) (Fin k → Fin N) ℂ) : Label N k → ℝ :=
  fun x => (star (φ x) ⬝ᵥ ((E x) *ᵥ φ x)).re

private def kernel {N k : ℕ} (s : ℝ) : Matrix (Label N k) (Label N k) ℂ :=
  fun x y => ∏ j, if x.val j = y.val j then 1 else (s : ℂ)

private lemma product_gram {N k : ℕ} (ψ : Fin N → Fin N → ℂ) (s : ℝ)
    (hψ : IsEquiangular ψ s) : gram (productState (k := k) ψ) = kernel s := by
  sorry

private lemma measurement_gram_bound {N k : ℕ}
    (φ : Label N k → (Fin k → Fin N) → ℂ)
    (E : Label N k → Matrix (Fin k → Fin N) (Fin k → Fin N) ℂ)
    (E₀ : Matrix (Fin k → Fin N) (Fin k → Fin N) ℂ)
    (hE : IsUnambiguousMeasurement φ E E₀) :
    (gram φ - diagonal (fun x => (probabilities φ E x : ℂ))).PosSemidef := by
  sorry

private lemma symmetrized_bound {N k : ℕ} (hk : k ≤ N) (s : ℝ)
    (q : Label N k → ℝ)
    (hq : (kernel s - diagonal (fun x => (q x : ℂ))).PosSemidef) :
    (kernel s - (((1 / (Fintype.card (Label N k) : ℝ)) * ∑ x, q x : ℝ) : ℂ) •
      (1 : Matrix (Label N k) (Label N k) ℂ)).PosSemidef := by
  sorry

private lemma kernel_eigenvector {N k : ℕ} (hN : 3 ≤ N) (hk : 2 ≤ k)
    (hkN : k ≤ N) (s : ℝ) :
    ∃ w : Label N k → ℂ, w ≠ 0 ∧ kernel s *ᵥ w = (value N k s : ℂ) • w := by
  sorry

private lemma eigenvalue_bound {N k : ℕ} (s a v : ℝ)
    (h : (kernel (N := N) (k := k) s - (a : ℂ) • 1).PosSemidef)
    (w : Label N k → ℂ) (hw : w ≠ 0) (he : kernel s *ᵥ w = (v : ℂ) • w) :
    a ≤ v := by
  sorry

private lemma upper_bound {N k : ℕ} (hN : 3 ≤ N) (hk : 2 ≤ k)
    (hkN : k ≤ N) (s : ℝ) (ψ : Fin N → Fin N → ℂ) (hψ : IsEquiangular ψ s)
    (E : Label N k → Matrix (Fin k → Fin N) (Fin k → Fin N) ℂ)
    (E₀ : Matrix (Fin k → Fin N) (Fin k → Fin N) ℂ)
    (hE : IsUnambiguousMeasurement (productState (k := k) ψ) E E₀) :
    averageSuccess (productState (k := k) ψ) E ≤ value N k s := by
  have hg := measurement_gram_bound (productState (k := k) ψ) E E₀ hE
  rw [product_gram ψ s hψ] at hg
  have hb := symmetrized_bound hkN s (probabilities (productState (k := k) ψ) E) hg
  obtain ⟨w, hw, he⟩ := kernel_eigenvector hN hk hkN s
  exact eigenvalue_bound s (averageSuccess (productState (k := k) ψ) E) (value N k s) hb w hw he

private lemma product_attainment {N k : ℕ} (hN : 3 ≤ N) (hk : 2 ≤ k)
    (hkN : k ≤ N) (s : ℝ) (hs : 0 < s) (hs1 : s < 1)
    (ψ : Fin N → Fin N → ℂ) (hψ : IsEquiangular ψ s) :
    ∃ F d E E₀, IsProductProtocol (k := k) F d E E₀ ∧
      IsUnambiguousMeasurement (productState (k := k) ψ) E E₀ ∧
      averageSuccess (productState (k := k) ψ) E = value N k s := by
  sorry

theorem result : claim := by
  intro N k hN hk hkN s hs hs1 ψ hψ
  exact ⟨fun E E₀ hE => upper_bound hN hk hkN s ψ hψ E E₀ hE,
    product_attainment hN hk hkN s hs hs1 ψ hψ⟩

end

end D5.S3.Quantum.PureState.NoRepetitionSequenceUnambiguousDiscrimination
