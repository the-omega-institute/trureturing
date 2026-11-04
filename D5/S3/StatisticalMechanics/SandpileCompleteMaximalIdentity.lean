/- GID: D5/S3/StatisticalMechanics/SandpileCompleteMaximalIdentity
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/SandpileCompleteMaximalIdentity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Gao–Li's complete maximal identity conjecture for clique–path products. -/

import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open scoped BigOperators

namespace D5.S3.StatisticalMechanics.SandpileCompleteMaximalIdentity

/-- The maximal stable configuration belongs to the reduced integer Laplacian image. -/
def maximalIdentityAt (i j : ℕ) (s : Fin i × Fin j) : Prop :=
  ∃ f : {v : Fin i × Fin j // v ≠ s} → ℤ,
    ∀ v : {v : Fin i × Fin j // v ≠ s},
      ∑ w : {v : Fin i × Fin j // v ≠ s},
        ((⊤ : SimpleGraph (Fin i)).boxProd (SimpleGraph.pathGraph j)).lapMatrix ℤ v.1 w.1 *
          f w =
        (((⊤ : SimpleGraph (Fin i)).boxProd (SimpleGraph.pathGraph j)).degree v.1 : ℤ) - 1

/-- Gao–Li's classification under the reduced-Laplacian image reading. -/
def claim : Prop :=
  ∀ i j : ℕ, 2 ≤ i → 2 ≤ j →
    ((∀ s : Fin i × Fin j, maximalIdentityAt i j s) ↔ (i = 4 ∧ j = 2))

private lemma path_reduction (i j : ℕ) (hi : 2 ≤ i) (hj : 2 ≤ j)
    (h : maximalIdentityAt i j (⟨0, by omega⟩, ⟨0, by omega⟩)) :
    ∃ x : ℕ → ℤ,
      x 1 = (i + 1 : ℤ) * x 0 ∧
      (∀ k : ℕ, k + 2 < j → x (k + 2) = (i + 2 : ℤ) * x (k + 1) - x k) ∧
      (i + 1 : ℤ) * x (j - 1) - x (j - 2) = -(i : ℤ) * ((i : ℤ) * j - 2) := by
  sorry

private lemma path_elimination (i j : ℕ) (hj : 2 ≤ j) (x : ℕ → ℤ)
    (h0 : x 1 = (i + 1 : ℤ) * x 0)
    (hr : ∀ k : ℕ, k + 2 < j → x (k + 2) = (i + 2 : ℤ) * x (k + 1) - x k) :
    (i + 1 : ℤ) * x (j - 1) - x (j - 2) =
      (i : ℤ) * (Polynomial.Chebyshev.S ℤ ((j : ℤ) - 1)).eval (i + 2) * x 0 := by
  sorry

private lemma identity_divisibility (i j : ℕ) (hi : 2 ≤ i) (hj : 2 ≤ j)
    (h : maximalIdentityAt i j (⟨0, by omega⟩, ⟨0, by omega⟩)) :
    (Polynomial.Chebyshev.S ℤ ((j : ℤ) - 1)).eval (i + 2) ∣ (i : ℤ) * j - 2 := by
  obtain ⟨x, h0, hr, he⟩ := path_reduction i j hi hj h
  have hx := path_elimination i j hj x h0 hr
  have hi0 : (i : ℤ) ≠ 0 := by omega
  refine ⟨-x 0, ?_⟩
  apply mul_left_cancel₀ hi0
  nlinarith [he, hx]

private lemma continuant_growth (i j : ℕ) (hi : 2 ≤ i) (hj : 3 ≤ j) :
    (i : ℤ) * j - 2 < (Polynomial.Chebyshev.S ℤ ((j : ℤ) - 1)).eval (i + 2) := by
  sorry

private lemma divisibility_classification (i j : ℕ) (hi : 2 ≤ i) (hj : 2 ≤ j)
    (h : (Polynomial.Chebyshev.S ℤ ((j : ℤ) - 1)).eval (i + 2) ∣ (i : ℤ) * j - 2) :
    i = 4 ∧ j = 2 := by
  sorry

private lemma exceptional_identity : ∀ s : Fin 4 × Fin 2, maximalIdentityAt 4 2 s := by
  sorry

theorem result : claim := by
  intro i j hi hj
  constructor
  · intro h
    exact divisibility_classification i j hi hj
      (identity_divisibility i j hi hj (h (⟨0, by omega⟩, ⟨0, by omega⟩)))
  · rintro ⟨rfl, rfl⟩
    exact exceptional_identity

end D5.S3.StatisticalMechanics.SandpileCompleteMaximalIdentity
