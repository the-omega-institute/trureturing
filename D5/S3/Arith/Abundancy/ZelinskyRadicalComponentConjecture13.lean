/- GID: D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture13
   generality: G
   mirror-B: D5/B/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture13
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture13.claim; result=D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture13.result; claim=D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture13.claim
   digest: The primitive relative density contradicts Conjecture 13. -/

import D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjecture11

/-! Odd primitive non-deficient integers and their radical-component relative density. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Finset Real Filter
open scoped BigOperators Topology

namespace D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjecture13

open ZelinskyZhangDoublePrimitive (PrimitiveNonDeficient rough_primitive_lower_bound)
open ZelinskyRadicalComponentDensity (radicalComponentSet count)

attribute [local instance] Classical.propDecidable

/-- Conjecture 13 in the source, with denominator C_O(X). -/
def claim : Prop :=
  Tendsto (fun X : ℕ =>
    (count (radicalComponentSet 2 ∩ {n | PrimitiveNonDeficient n ∧ Odd n}) X : ℝ) /
      count {n | PrimitiveNonDeficient n ∧ Odd n} X) atTop (𝓝 0)

/-- Odd primitive non-deficient integers have relative density one in B. -/
theorem result : ¬ claim := by
  intro hclaim
  have hlower : ∀ᶠ X : ℕ in atTop, (X : ℝ) ^ (79 / 80 : ℝ) ≤
      (count {n | PrimitiveNonDeficient n ∧ Odd n} X : ℝ) := by
    obtain ⟨X₀, hX₀⟩ := rough_primitive_lower_bound ∅ (by simp)
    filter_upwards [eventually_ge_atTop X₀] with X hX
    have hcard : ((Icc 1 X).filter (fun n =>
        Odd n ∧ Squarefree n ∧ PrimitiveNonDeficient n ∧
          ∀ p ∈ (∅ : Finset ℕ), ¬ p ∣ n)).card ≤
        count {n | PrimitiveNonDeficient n ∧ Odd n} X := by
      apply card_le_card
      intro n hn
      obtain ⟨hnI, hnodd, _, hnC, _⟩ := mem_filter.mp hn
      exact mem_filter.mpr ⟨hnI, hnC, hnodd⟩
    exact (hX₀ X hX).trans (by exact_mod_cast hcard)
  have hone := ZelinskyRadicalComponentConjecture11.relative_density_one
    {n | PrimitiveNonDeficient n ∧ Odd n} (fun _ hn => hn.1) hlower
  have hbad : (1 : ℝ) = 0 := tendsto_nhds_unique hone hclaim
  norm_num at hbad

end D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjecture13
