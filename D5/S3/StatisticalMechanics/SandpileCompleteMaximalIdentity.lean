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

/-! The complete maximal identity property for Cartesian products of cliques and paths. -/

open scoped BigOperators
open Polynomial Chebyshev

namespace D5.S3.StatisticalMechanics.SandpileCompleteMaximalIdentity

/-- The maximal stable configuration belongs to the reduced integer Laplacian image. -/
def maximalIdentityAt (i j : ℕ) (s : Fin i × Fin j) : Prop := by
  classical
  exact ∃ f : {v : Fin i × Fin j // v ≠ s} → ℤ,
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
      (i : ℤ) * (Polynomial.Chebyshev.S ℤ ((j : ℤ) - 1)).eval (i + 2 : ℤ) * x 0 := by
  have hf : ∀ k : ℕ, k < j → x k =
      ((S ℤ (k : ℤ)).eval (i + 2 : ℤ) -
        (S ℤ ((k : ℤ) - 1)).eval (i + 2 : ℤ)) * x 0 := by
    intro k
    induction k using Nat.twoStepInduction with
    | zero => intro hk; simp
    | one => intro hk; simpa only [Nat.cast_one, S_one, S_zero, sub_self, eval_X, eval_one, show (i + 2 : ℤ) - 1 = i + 1 by ring] using h0
    | more k ha hb =>
      intro hk
      rw [hr k hk, hb (by omega), ha (by omega)]
      have hs := congrArg (Polynomial.eval (i + 2 : ℤ)) (S_add_two ℤ (k : ℤ))
      have ht := congrArg (Polynomial.eval (i + 2 : ℤ)) (S_add_one ℤ (k : ℤ))
      simp only [eval_sub, eval_mul, eval_X] at hs ht
      push_cast
      rw [show (k : ℤ) + 2 - 1 = (k : ℤ) + 1 by ring]
      rw [show (k : ℤ) + 1 - 1 = (k : ℤ) by ring]
      linear_combination -x 0 * hs + x 0 * ht
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = n + 2 := ⟨j - 2, by omega⟩
  rw [show n + 2 - 1 = n + 1 by omega, show n + 2 - 2 = n by omega,
    hf (n + 1) (by omega), hf n (by omega)]
  have ht := congrArg (Polynomial.eval (i + 2 : ℤ)) (S_add_one ℤ (n : ℤ))
  simp only [eval_sub, eval_mul, eval_X] at ht
  push_cast
  rw [show (n : ℤ) + 1 - 1 = (n : ℤ) by ring,
    show (n : ℤ) + 2 - 1 = (n : ℤ) + 1 by ring]
  linear_combination x 0 * ht

private lemma identity_divisibility (i j : ℕ) (hi : 2 ≤ i) (hj : 2 ≤ j)
    (h : maximalIdentityAt i j (⟨0, by omega⟩, ⟨0, by omega⟩)) :
    (Polynomial.Chebyshev.S ℤ ((j : ℤ) - 1)).eval (i + 2 : ℤ) ∣ (i : ℤ) * j - 2 := by
  obtain ⟨x, h0, hr, he⟩ := path_reduction i j hi hj h
  have hx := path_elimination i j hj x h0 hr
  have hi0 : (i : ℤ) ≠ 0 := by omega
  refine ⟨-x 0, ?_⟩
  apply mul_left_cancel₀ hi0
  nlinarith [he, hx]

private lemma continuant_growth (i j : ℕ) (hi : 2 ≤ i) (hj : 3 ≤ j) :
    (i : ℤ) * j - 2 < (Polynomial.Chebyshev.S ℤ ((j : ℤ) - 1)).eval (i + 2 : ℤ) := by
  have hi' : (2 : ℤ) ≤ i := by omega
  have hg : ∀ n : ℕ, 1 ≤ (S ℤ (n : ℤ)).eval (i + 2 : ℤ) ∧
      (i : ℤ) < (S ℤ ((n : ℤ) + 1)).eval (i + 2 : ℤ) -
        (S ℤ (n : ℤ)).eval (i + 2 : ℤ) := by
    intro n
    induction n with
    | zero => simp; omega
    | succ n hn =>
      have hs := congrArg (Polynomial.eval (i + 2 : ℤ)) (S_add_two ℤ (n : ℤ))
      simp only [eval_sub, eval_mul, eval_X] at hs
      push_cast
      rw [show (n : ℤ) + 1 + 1 = (n : ℤ) + 2 by ring]
      constructor <;> nlinarith [hn.1, hn.2]
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = n + 3 := ⟨j - 3, by omega⟩
  clear hj
  induction n with
  | zero =>
    norm_num [S_two]
    nlinarith
  | succ n hn =>
    have hs := (hg (n + 2)).2
    push_cast at hn hs ⊢
    rw [show (n : ℤ) + 1 + 3 - 1 = (n : ℤ) + 2 + 1 by ring]
    rw [show (n : ℤ) + 3 - 1 = (n : ℤ) + 2 by ring] at hn
    nlinarith

private lemma divisibility_classification (i j : ℕ) (hi : 2 ≤ i) (hj : 2 ≤ j)
    (h : (Polynomial.Chebyshev.S ℤ ((j : ℤ) - 1)).eval (i + 2 : ℤ) ∣ (i : ℤ) * j - 2) :
    i = 4 ∧ j = 2 := by
  by_cases hj2 : j = 2
  · subst j
    norm_num at h
    have h6 : (i + 2 : ℤ) ∣ 6 := by
      convert dvd_sub (dvd_mul_right (i + 2 : ℤ) 2) h using 1 <;> ring
    have hb := Int.le_of_dvd (by norm_num : (0 : ℤ) < 6) h6
    have hc : i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases hc with rfl | rfl | rfl
    · norm_num at h
    · norm_num at h
    · exact ⟨rfl, rfl⟩
  · have hg := continuant_growth i j hi (by omega)
    have hp : (0 : ℤ) < (i : ℤ) * j - 2 := by
      have hi' : (2 : ℤ) ≤ i := by omega
      have hj' : (3 : ℤ) ≤ j := by omega
      nlinarith
    have hb := Int.le_of_dvd hp h
    omega

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
