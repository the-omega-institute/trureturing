/- GID: D5/S3/Quantum/Dynamics/BaseNormContraction
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/BaseNormContraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Positive normalization-preserving dynamics contract the cone base norm. -/

import Mathlib.Geometry.Convex.Cone.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/- Library-search audit trail (2026-08-24):
   * Exact repository searches found no base-norm construction or contraction
     theorem. Existing contraction modules concern unrelated ambient norms.
   * Pinned Mathlib exact hit `ConvexCone` supplies the source's positive cone
     closure under addition and positive scalar multiplication.
   * Pinned Mathlib has no packaged base norm. The definition below follows the
     source verbatim as the infimum of positive decomposition costs.
   * Exact Mathlib hit `csInf_le_csInf` supplies reversed infimum monotonicity
     from the mapped-decomposition subset. `loogle` and `leansearch` are absent
     from PATH. -/

noncomputable section

namespace D5.S3.Quantum.Dynamics.BaseNormContraction

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Costs of writing a vector as the difference of two vectors in the source
positive cone. -/
def coneDecompositionCosts
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (C : ConvexCone ℝ V) (u : V →ₗ[ℝ] ℝ) (x : V) : Set ℝ :=
  {cost | ∃ a b : V, a ∈ C ∧ b ∈ C ∧ x = a - b ∧ cost = u a + u b}

/-- The base norm constructed from the generating cone and its strictly
positive normalization functional. -/
def baseNorm
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (C : ConvexCone ℝ V) (u : V →ₗ[ℝ] ℝ) (x : V) : ℝ :=
  sInf (coneDecompositionCosts C u x)

private theorem functional_nonneg_on_cone
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (C : ConvexCone ℝ V) (u : V →ₗ[ℝ] ℝ)
    (hStrictPositive : ∀ a : V, a ∈ C → a ≠ 0 → 0 < u a)
    {a : V} (ha : a ∈ C) :
    0 ≤ u a := by
  by_cases haZero : a = 0
  · subst a
    simp
  · exact (hStrictPositive a ha haZero).le

private theorem cone_decomposition_costs_nonempty
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (C : ConvexCone ℝ V) (u : V →ₗ[ℝ] ℝ)
    (hGenerating : ∀ x : V, ∃ a b : V, a ∈ C ∧ b ∈ C ∧ x = a - b)
    (x : V) :
    (coneDecompositionCosts C u x).Nonempty := by
  rcases hGenerating x with ⟨a, b, ha, hb, hx⟩
  exact ⟨u a + u b, ⟨a, b, ha, hb, hx, rfl⟩⟩

private theorem cone_decomposition_costs_bddBelow
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (C : ConvexCone ℝ V) (u : V →ₗ[ℝ] ℝ)
    (hStrictPositive : ∀ a : V, a ∈ C → a ≠ 0 → 0 < u a)
    (x : V) :
    BddBelow (coneDecompositionCosts C u x) := by
  refine ⟨0, ?_⟩
  rintro cost ⟨a, b, ha, hb, _, rfl⟩
  exact add_nonneg
    (functional_nonneg_on_cone C u hStrictPositive ha)
    (functional_nonneg_on_cone C u hStrictPositive hb)

/-- A real-linear dynamics family that preserves the generating positive cone
and the normalization functional cannot increase the source-defined base norm. -/
theorem positive_normalization_preserving_dynamics_contracts_base_norm
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (C : ConvexCone ℝ V) (u : V →ₗ[ℝ] ℝ)
    (hGenerating : ∀ x : V, ∃ a b : V, a ∈ C ∧ b ∈ C ∧ x = a - b)
    (hStrictPositive : ∀ a : V, a ∈ C → a ≠ 0 → 0 < u a)
    (T : ℝ → V →ₗ[ℝ] V)
    (hPositive : ∀ t : ℝ, ∀ a : V, a ∈ C → T t a ∈ C)
    (hPreservesNormalization : ∀ t : ℝ, u.comp (T t) = u)
    (t : ℝ) (x : V) :
    baseNorm C u (T t x) ≤ baseNorm C u x := by
  apply csInf_le_csInf
  · exact cone_decomposition_costs_bddBelow C u hStrictPositive (T t x)
  · exact cone_decomposition_costs_nonempty C u hGenerating x
  · rintro cost ⟨a, b, ha, hb, hx, hcost⟩
    refine ⟨T t a, T t b, hPositive t a ha, hPositive t b hb, ?_, ?_⟩
    · rw [hx, map_sub]
    · rw [hcost]
      have haPreserved := LinearMap.congr_fun (hPreservesNormalization t) a
      have hbPreserved := LinearMap.congr_fun (hPreservesNormalization t) b
      simpa only [LinearMap.comp_apply] using
        (congrArg₂ (· + ·) haPreserved hbPreserved).symm

#print axioms positive_normalization_preserving_dynamics_contracts_base_norm

end D5.S3.Quantum.Dynamics.BaseNormContraction
