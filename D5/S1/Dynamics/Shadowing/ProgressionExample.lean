/- GID: D5/S1/Dynamics/Shadowing/ProgressionExample
   generality: I
   mirror-B: D5/B/S1/Dynamics/Shadowing/ProgressionExample
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The full natural-time progression example for Meddaugh--Stephens Question 5.6. -/

import D5.S1.Dynamics.Shadowing.ProgressionTwoShadowing

/-! Weak mixing is stated as transitivity of the square map on all nonempty
open subsets of the product. The periodic-set obstruction explicitly excludes
only nonempty sets and is stronger than exclusion of compact periodic sets. -/

open Set Function

namespace D5.S1.Dynamics.Shadowing

/-- Product transitivity on arbitrary relatively open sets, not just cylinders. -/
theorem progression_shift_product_transitive {ℓ : ℕ → ℕ}
    (hℓ : ∀ p, 0 < p → 3 ≤ ℓ p)
    (U V : Set (ProgressionPoint ℓ × ProgressionPoint ℓ))
    (hU : IsOpen U) (hV : IsOpen V) (hUn : U.Nonempty) (hVn : V.Nonempty) :
    ∃ n : ℕ, ∃ z ∈ U,
      (((progressionShift ℓ)^[n] z.1), ((progressionShift ℓ)^[n] z.2)) ∈ V := by
  obtain ⟨⟨x₀, x₁⟩, hx⟩ := hUn
  obtain ⟨⟨y₀, y₁⟩, hy⟩ := hVn
  obtain ⟨U₀, U₁, hU₀, hU₁, hx₀, hx₁, hUU⟩ := isOpen_prod_iff.mp hU x₀ x₁ hx
  obtain ⟨V₀, V₁, hV₀, hV₁, hy₀, hy₁, hVV⟩ := isOpen_prod_iff.mp hV y₀ y₁ hy
  obtain ⟨N₀, hN₀⟩ := progression_shift_mixing hℓ U₀ V₀ hU₀ hV₀ ⟨x₀, hx₀⟩ ⟨y₀, hy₀⟩
  obtain ⟨N₁, hN₁⟩ := progression_shift_mixing hℓ U₁ V₁ hU₁ hV₁ ⟨x₁, hx₁⟩ ⟨y₁, hy₁⟩
  obtain ⟨z₀, hz₀, ht₀⟩ := hN₀ (max N₀ N₁) (le_max_left _ _)
  obtain ⟨z₁, hz₁, ht₁⟩ := hN₁ (max N₀ N₁) (le_max_right _ _)
  exact ⟨max N₀ N₁, (z₀, z₁), hUU ⟨hz₀, hz₁⟩, hVV ⟨ht₀, ht₁⟩⟩

/-- A nonempty compact metric system, continuous and onto, weakly mixing,
with one fixed tracing bound two and a nonempty clopen set containing no
nonempty compact periodic set. The stronger forward-invariance obstruction
is included, so nonemptiness cannot be supplied by the empty set. -/
theorem quadratic_progression_example :
    Nonempty (ProgressionPoint quadraticProgressionLength) ∧
    CompactSpace (ProgressionPoint quadraticProgressionLength) ∧
    Continuous (progressionShift quadraticProgressionLength) ∧
    Surjective (progressionShift quadraticProgressionLength) ∧
    (∀ U V : Set (ProgressionPoint quadraticProgressionLength ×
        ProgressionPoint quadraticProgressionLength),
      IsOpen U → IsOpen V → U.Nonempty → V.Nonempty →
      ∃ n : ℕ, ∃ z ∈ U,
        (((progressionShift quadraticProgressionLength)^[n] z.1),
         ((progressionShift quadraticProgressionLength)^[n] z.2)) ∈ V) ∧
    NeighborhoodTwoShadowing (progressionShift quadraticProgressionLength) ∧
    ∃ U : Set (ProgressionPoint quadraticProgressionLength),
      IsClopen U ∧ U.Nonempty ∧
      (∀ p : ℕ, 0 < p → ∀ B : Set (ProgressionPoint quadraticProgressionLength),
        B ⊆ U → MapsTo ((progressionShift quadraticProgressionLength)^[p]) B B →
        ¬ B.Nonempty) ∧
      ¬ ∃ B : Set (ProgressionPoint quadraticProgressionLength),
        B.Nonempty ∧ IsCompact B ∧ B ⊆ U ∧
          ∃ p : ℕ, 0 < p ∧ (progressionShift quadraticProgressionLength)^[p] '' B = B := by
  have hℓ (p : ℕ) (_ : 0 < p) : 3 ≤ quadraticProgressionLength p := by
    simp [quadraticProgressionLength]
  have hℓ₂ (p : ℕ) (hp : 0 < p) : 2 ≤ quadraticProgressionLength p := (by omega : 2 ≤ 3).trans (hℓ p hp)
  have hℓ₀ (p : ℕ) (hp : 0 < p) : 0 < quadraticProgressionLength p := by have := hℓ p hp; omega
  refine ⟨⟨⟨_, progression_zero_legal hℓ₀⟩⟩, inferInstance,
    progression_shift_continuous _, progression_shift_surjective hℓ₀,
    progression_shift_product_transitive hℓ,
    quadratic_progression_neighborhood_two_shadowing, progressionOneCylinder _,
    progression_one_cylinder_clopen _, progression_one_cylinder_nonempty hℓ₂,
    progression_no_invariant_subset _, ?_⟩
  rintro ⟨B, hB, _, hBU, p, hp, hperiod⟩
  exact progression_no_invariant_subset _ p hp B hBU
    (fun x hx => hperiod ▸ ⟨x, hx, rfl⟩) hB

end D5.S1.Dynamics.Shadowing
