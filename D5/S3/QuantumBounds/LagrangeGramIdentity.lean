/- GID: D5/S3/QuantumBounds/LagrangeGramIdentity
   generality: G
   mirror-B: D5/B/S3/QuantumBounds/LagrangeGramIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The Cauchy–Schwarz defect (Σuᵢ²)(Σvᵢ²)−(Σuᵢvᵢ)² equals the manifestly nonnegative sum of squares ½ΣᵢΣⱼ(uᵢvⱼ−uⱼvᵢ)² — the coordinate Gram wedge-remainder underlying the Cauchy–Schwarz inequality. -/

import Mathlib

namespace D5.S3.QuantumBounds.LagrangeGramIdentity

open Finset

/-- The Lagrange identity (coordinate Gram remainder): the Cauchy–Schwarz defect
`(Σ uᵢ²)(Σ vᵢ²) − (Σ uᵢvᵢ)²` equals the manifestly nonnegative sum of squares
`½ Σᵢ Σⱼ (uᵢvⱼ − uⱼvᵢ)²`. -/
theorem lagrange_gram_identity {ι : Type*} (s : Finset ι) (u v : ι → ℝ) :
    (∑ i ∈ s, u i ^ 2) * (∑ i ∈ s, v i ^ 2) - (∑ i ∈ s, u i * v i) ^ 2
      = (∑ i ∈ s, ∑ j ∈ s, (u i * v j - u j * v i) ^ 2) / 2 := by
  have key : (∑ i ∈ s, ∑ j ∈ s, (u i * v j - u j * v i) ^ 2)
      = 2 * ((∑ i ∈ s, u i ^ 2) * (∑ i ∈ s, v i ^ 2) - (∑ i ∈ s, u i * v i) ^ 2) := by
    have e1 : (∑ i ∈ s, u i ^ 2) * (∑ i ∈ s, v i ^ 2)
        = ∑ i ∈ s, ∑ j ∈ s, u i ^ 2 * v j ^ 2 := Finset.sum_mul_sum s s _ _
    have e2 : (∑ i ∈ s, u i * v i) ^ 2
        = ∑ i ∈ s, ∑ j ∈ s, (u i * v i) * (u j * v j) := by
      rw [sq]; exact Finset.sum_mul_sum s s _ _
    have expand : (∑ i ∈ s, ∑ j ∈ s, (u i * v j - u j * v i) ^ 2)
        = (∑ i ∈ s, ∑ j ∈ s, u i ^ 2 * v j ^ 2)
          + (∑ i ∈ s, ∑ j ∈ s, u j ^ 2 * v i ^ 2)
          - 2 * (∑ i ∈ s, ∑ j ∈ s, (u i * v i) * (u j * v j)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    have hsymm : (∑ i ∈ s, ∑ j ∈ s, u j ^ 2 * v i ^ 2)
        = (∑ i ∈ s, ∑ j ∈ s, u i ^ 2 * v j ^ 2) := Finset.sum_comm
    rw [expand, hsymm, e1, e2]; ring
  rw [key]; ring

end D5.S3.QuantumBounds.LagrangeGramIdentity
