/- GID: D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture15
   generality: I
   mirror-B: D5/B/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture15
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The primitive relative density contradicts Conjecture 15. -/

import D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjecture11

/-! Prime avoidance and primitive radical-component relative density. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Finset Real Filter
open scoped BigOperators Topology

namespace D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjecture15

open ZelinskyZhangDoublePrimitive (PrimitiveNonDeficient rough_primitive_lower_bound)
open ZelinskyRadicalComponentDensity (radicalComponentSet count)

attribute [local instance] Classical.propDecidable

/-- Conjecture 15, including the source's nonempty finite prime-set quantifier. -/
def claim : Prop :=
  ∀ M : Finset ℕ, M.Nonempty → (∀ p ∈ M, p.Prime) →
    Tendsto (fun X : ℕ =>
      (count (radicalComponentSet 2 ∩
        {n | PrimitiveNonDeficient n ∧ ∀ p ∈ M, ¬ p ∣ n}) X : ℝ) /
        count {n | PrimitiveNonDeficient n ∧ ∀ p ∈ M, ¬ p ∣ n} X) atTop (𝓝 0)

/-- The required universal zero limit already fails for the singleton prime set {2}. -/
theorem result : ¬ claim := by
  intro hclaim
  let M : Finset ℕ := {2}
  have hprime : ∀ p ∈ M, p.Prime := by
    intro p hp
    have hp2 : p = 2 := by simpa only [M, mem_singleton] using hp
    subst p
    exact Nat.prime_two
  have hzero := hclaim M (by simp [M]) hprime
  have hlower : ∀ᶠ X : ℕ in atTop, (X : ℝ) ^ (79 / 80 : ℝ) ≤
      (count {n | PrimitiveNonDeficient n ∧ ∀ p ∈ M, ¬ p ∣ n} X : ℝ) := by
    obtain ⟨X₀, hX₀⟩ := rough_primitive_lower_bound M hprime
    filter_upwards [eventually_ge_atTop X₀] with X hX
    have hcard : ((Icc 1 X).filter (fun n =>
        Odd n ∧ Squarefree n ∧ PrimitiveNonDeficient n ∧ ∀ p ∈ M, ¬ p ∣ n)).card ≤
        count {n | PrimitiveNonDeficient n ∧ ∀ p ∈ M, ¬ p ∣ n} X := by
      unfold count
      apply card_le_card
      intro n hn
      simp only [mem_filter, Set.mem_setOf_eq] at hn ⊢
      exact ⟨hn.1, hn.2.2.2.1, hn.2.2.2.2⟩
    exact (hX₀ X hX).trans (by exact_mod_cast hcard)
  have hone := ZelinskyRadicalComponentConjecture11.relative_density_one
    {n | PrimitiveNonDeficient n ∧ ∀ p ∈ M, ¬ p ∣ n} (fun _ hn => hn.1) hlower
  have hbad : (1 : ℝ) = 0 := tendsto_nhds_unique hone hzero
  norm_num at hbad

end D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjecture15
