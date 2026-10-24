/- GID: D5/S3/QuantumBounds/NetworkCoherenceClassicalBound
   generality: I
   mirror-B: D5/B/S3/QuantumBounds/NetworkCoherenceClassicalBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The sharp classical coherence bound for mixtures of two binary product laws. -/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

open scoped BigOperators

noncomputable section

namespace D5.S3.QuantumBounds.NetworkCoherenceClassicalBound

def parity {n : ℕ} (a : Fin n → Bool) : ℕ := (∑ i, (a i).toNat) % 2

def IsBitDistribution (p : Bool → ℝ) : Prop :=
  0 ≤ p false ∧ 0 ≤ p true ∧ p false + p true = 1

def classicalMixture (n : ℕ) (γ : ℝ) (p q : Fin n → Bool → ℝ) :
    (Fin n → Bool) → ℝ :=
  fun a => γ * ∏ i, p i (a i) + (1 - γ) * ∏ i, q i (a i)

def coherenceMerit (n : ℕ) (r : (Fin n → Bool) → ℝ) : ℝ :=
  (1 / 2) * |(∑ a ∈ Finset.univ.filter (fun a => parity a = 0),
    ∑ b ∈ Finset.univ.filter (fun b => parity b = 0),
      if a ≠ b then r a * r b else 0) -
    ∑ a ∈ Finset.univ.filter (fun a => parity a = 1),
    ∑ b ∈ Finset.univ.filter (fun b => parity b = 1),
      if a ≠ b then r a * r b else 0|

def claim : Prop := ∀ n : ℕ, 2 ≤ n →
  IsGreatest {c : ℝ | ∃ γ ∈ Set.Icc (0 : ℝ) 1, ∃ p q : Fin n → Bool → ℝ,
    (∀ i, IsBitDistribution (p i)) ∧ (∀ i, IsBitDistribution (q i)) ∧
      c = coherenceMerit n (classicalMixture n γ p q)} (1 / 4)

private lemma parity_reduction (n : ℕ) (r : (Fin n → Bool) → ℝ)
    (hr : ∑ a, r a = 1) :
    coherenceMerit n r = (1 / 2) * |(∑ a, (-1 : ℝ) ^ (∑ i, (a i).toNat) * r a) -
      ∑ a, (-1 : ℝ) ^ (∑ i, (a i).toNat) * (r a) ^ 2| := by
  sorry

private lemma mixture_factorization (n : ℕ) (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (p q : Fin n → Bool → ℝ) (hp : ∀ i, IsBitDistribution (p i))
    (hq : ∀ i, IsBitDistribution (q i)) :
    coherenceMerit n (classicalMixture n γ p q) = γ * (1 - γ) / 2 *
      |(∏ i, (p i false - p i true)) + (∏ i, (q i false - q i true)) -
        2 * ∏ i, ((p i false - p i true + (q i false - q i true)) / 2)| := by
  sorry

private lemma cube_bound (n : ℕ) (x y : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (-1 : ℝ) 1)
    (hy : ∀ i, y i ∈ Set.Icc (-1 : ℝ) 1) :
    |(∏ i, x i) + (∏ i, y i) - 2 * ∏ i, ((x i + y i) / 2)| ≤ 2 := by
  sorry

private lemma upper_bound (n : ℕ) (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (p q : Fin n → Bool → ℝ) (hp : ∀ i, IsBitDistribution (p i))
    (hq : ∀ i, IsBitDistribution (q i)) :
    coherenceMerit n (classicalMixture n γ p q) ≤ 1 / 4 := by
  rw [mixture_factorization n γ hγ p q hp hq]
  have hb := cube_bound n (fun i => p i false - p i true)
    (fun i => q i false - q i true)
    (fun i => by have hi := hp i; constructor <;> linarith [hi.1, hi.2.1, hi.2.2])
    (fun i => by have hi := hq i; constructor <;> linarith [hi.1, hi.2.1, hi.2.2])
  have hnon : 0 ≤ γ * (1 - γ) := mul_nonneg hγ.1 (sub_nonneg.mpr hγ.2)
  nlinarith [sq_nonneg (γ - 1 / 2)]

private lemma attainment (n : ℕ) (hn : 2 ≤ n) :
    ∃ γ ∈ Set.Icc (0 : ℝ) 1, ∃ p q : Fin n → Bool → ℝ,
      (∀ i, IsBitDistribution (p i)) ∧ (∀ i, IsBitDistribution (q i)) ∧
        (1 / 4 : ℝ) = coherenceMerit n (classicalMixture n γ p q) := by
  sorry

theorem result : claim := by
  intro n hn
  refine ⟨attainment n hn, ?_⟩
  rintro c ⟨γ, hγ, p, q, hp, hq, rfl⟩
  exact upper_bound n γ hγ p q hp hq

end D5.S3.QuantumBounds.NetworkCoherenceClassicalBound
