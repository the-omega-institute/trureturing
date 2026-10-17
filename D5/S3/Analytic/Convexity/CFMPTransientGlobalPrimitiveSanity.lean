import D5.S3.Analytic.Convexity.CFMPTransientGlobalPrimitive
import Mathlib.Analysis.Convex.Contractible
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
Transient consumers, not additional admitted mathematical content.
These exercise additive offsets, a nonempty normalized analytic application,
the empty branch, dimension zero, and the original inner-product application.
None has been elaborated or executed in this source-only attempt.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped Classical unitInterval

namespace CFMP137Transient.Sanity

/-- Two unequal chart primitives, with the preferred chart deliberately true. -/
def offsetAtlas : AdditiveAtlas Bool ℝ where
  domain := fun _ => univ
  isOpen_domain := fun _ => isOpen_univ
  indexAt := fun _ => true
  mem_domain := fun _ => mem_univ _
  q := fun i x => x + if i then 7 else 0
  overlap := by
    intro i j
    refine ⟨(if i then 7 else 0) - (if j then 7 else 0), ?_⟩
    intro x hx
    ring

/-- The preferred offset 5 becomes 12 in the other chart; the value stays 15.
This checks the transition orientation and retention of the additive fiber. -/
theorem offset_readout_sanity :
    let p : offsetAtlas.core.TotalSpace := ⟨3, WithTopology.toTopology ⊥ (5 : ℝ)⟩
    ((offsetAtlas.core.localTriv false) p).2.ofTopology = 12 ∧
      offsetAtlas.value p = 15 ∧
      offsetAtlas.value p = offsetAtlas.q false p.1 +
        ((offsetAtlas.core.localTriv false) p).2.ofTopology := by
  dsimp only
  refine ⟨?_, ?_, offsetAtlas.value_eq_chart false _⟩
  · rw [FiberBundleCore.localTriv_apply]
    change (5 : ℝ) + (3 + 7) - (3 + 0) = 12
    norm_num
  · change (3 : ℝ) + 7 + 5 = 15
    norm_num

/-- Each local primitive has a different additive constant, q_a(z)=z+a. -/
theorem shifted_local_primitive_sanity :
    ∃ Q : ℝ → ℝ, Q 0 = 0 ∧
      ∀ z : ℝ, HasFDerivAt Q (ContinuousLinearMap.id ℝ ℝ) z := by
  letI : ContractibleSpace (univ : Set ℝ) :=
    (convex_univ : Convex ℝ (univ : Set ℝ)).contractibleSpace univ_nonempty
  have hsc : IsSimplyConnected (univ : Set ℝ) :=
    (inferInstance : SimplyConnectedSpace (univ : Set ℝ))
  obtain ⟨Q, hQ₀, hQ⟩ := exists_global_primitive_normalized
    (ω := fun _ : ℝ => ContinuousLinearMap.id ℝ ℝ)
    isOpen_univ hsc (⟨0, mem_univ 0⟩ : (univ : Set ℝ)) (by
      intro a ha
      refine ⟨1, zero_lt_one, fun z => z + a, subset_univ _, ?_⟩
      intro z hz
      simpa only [id_eq] using (hasFDerivAt_id (𝕜 := ℝ) z).add_const a)
  exact ⟨Q, hQ₀, fun z => hQ z (mem_univ z)⟩

/-- No basepoint is passed to the empty branch, for any covector field. -/
theorem empty_domain_sanity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ω : E → E →L[ℝ] ℝ) :
    ∃ Q : E → ℝ, ∀ z ∈ (∅ : Set E), HasFDerivAt Q (ω z) z := by
  apply exists_global_primitive isOpen_empty (Or.inl rfl)
  intro a ha
  exact False.elim ha

/-- A concrete zero-dimensional ambient space uses the same global theorem. -/
theorem dimension_zero_sanity :
    ∃ Q : PUnit → ℝ, ∀ z : PUnit, HasFDerivAt Q (0 : PUnit →L[ℝ] ℝ) z := by
  letI : ContractibleSpace (univ : Set PUnit) :=
    (convex_univ : Convex ℝ (univ : Set PUnit)).contractibleSpace univ_nonempty
  have hsc : IsSimplyConnected (univ : Set PUnit) :=
    (inferInstance : SimplyConnectedSpace (univ : Set PUnit))
  obtain ⟨Q, hQ⟩ := exists_global_primitive
    (ω := fun _ : PUnit => (0 : PUnit →L[ℝ] ℝ)) isOpen_univ (Or.inr hsc) (by
      intro a ha
      refine ⟨1, zero_lt_one, fun _ => 0, subset_univ _, ?_⟩
      intro z hz
      exact hasFDerivAt_const 0 z)
  exact ⟨Q, fun z => hQ z (mem_univ z)⟩

section OriginalApplication

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {D Ω : Set E}

/-- Ambient version of the supplied inverse, using zero only outside Ω. -/
def inverseExtension (T : D ≃ₜ Ω) : E → E :=
  fun z => if hz : z ∈ Ω then (T.symm ⟨z, hz⟩ : E) else 0

/-- Original finite-dimensional, open-convex-source setting as a transient
consumer. Finite dimension and source openness occur only in this compatibility
consumer; the stronger global theorem above does not require either.

The covector field is literally innerSL composed with the supplied inverse.
The local primitive certificates are inputs, and this makes no assertion that
the separate open-image, inverse, or weak-Poincare work has been validated. -/
theorem original_inner_product_application [FiniteDimensional ℝ E]
    (_hDopen : IsOpen D) (hD : Convex ℝ D) (hne : D.Nonempty)
    (hΩ : IsOpen Ω) (T : D ≃ₜ Ω)
    (hlocal : ∀ a ∈ Ω, ∃ r > 0, ∃ q : E → ℝ,
      ball a r ⊆ Ω ∧ ∀ z ∈ ball a r,
        HasFDerivAt q (innerSL ℝ (inverseExtension T z)) z) :
    ∃ Q : E → ℝ, ∀ z ∈ Ω,
      HasFDerivAt Q (innerSL ℝ (inverseExtension T z)) z := by
  exact exists_global_primitive_of_homeomorph hΩ hD hne T hlocal

end OriginalApplication

end CFMP137Transient.Sanity

end
