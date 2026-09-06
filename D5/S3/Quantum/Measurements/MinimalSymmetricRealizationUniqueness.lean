/- GID: D5/S3/Quantum/Measurements/MinimalSymmetricRealizationUniqueness
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurements/MinimalSymmetricRealizationUniqueness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equal moments give an orthogonal intertwiner between minimal symmetric realizations. -/

import D5.S3.Observer.LinearMemory.ReachableObservableQuotientReachability
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Measurements.MinimalSymmetricRealizationUniqueness

open D5.S3.Observer.LinearMemory.ReachableObservableQuotientReachability
open scoped InnerProductSpace

variable {U E E' : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']

private def combination (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E) :
    (ℕ →₀ U) →ₗ[ℝ] E :=
  Finsupp.lsum ℝ fun k => (A ^ k).comp B

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ E] in
private theorem combination_single (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E)
    (k : ℕ) (v : U) : combination A B (Finsupp.single k v) = (A ^ k) (B v) := by
  simp [combination]

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ E] in
private theorem combination_surjective (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E)
    (minimal : reachableSubspace A B = ⊤) : Function.Surjective (combination A B) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← minimal]
  apply Submodule.span_le.mpr
  rintro x ⟨k, v, rfl⟩
  exact ⟨Finsupp.single k v, combination_single A B k v⟩

private theorem generator_inner (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E)
    (hA : A.IsSymmetric) (k l : ℕ) (v w : U) :
    inner ℝ ((A ^ k) (B v)) ((A ^ l) (B w)) =
      inner ℝ v ((B.adjoint.comp ((A ^ (k + l)).comp B)) w) := by
  rw [(hA.pow k) (B v) ((A ^ l) (B w))]
  simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_right,
    pow_add, Module.End.mul_apply]

-- The Gram equality is derived for arbitrary realizations, before any quotient is formed.
private theorem combination_gram (A : E →ₗ[ℝ] E) (A' : E' →ₗ[ℝ] E')
    (B : U →ₗ[ℝ] E) (B' : U →ₗ[ℝ] E')
    (hA : A.IsSymmetric) (hA' : A'.IsSymmetric)
    (moments : ∀ k : ℕ, B.adjoint.comp ((A ^ k).comp B) =
      B'.adjoint.comp ((A' ^ k).comp B')) (v w : ℕ →₀ U) :
    inner ℝ (combination A B v) (combination A B w) =
      inner ℝ (combination A' B' v) (combination A' B' w) := by
  classical
  simp only [combination, Finsupp.lsum_apply, Finsupp.sum, LinearMap.comp_apply,
    sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  rw [generator_inner A B hA, generator_inner A' B' hA', moments]

private theorem combination_kernel (A : E →ₗ[ℝ] E) (A' : E' →ₗ[ℝ] E')
    (B : U →ₗ[ℝ] E) (B' : U →ₗ[ℝ] E')
    (hA : A.IsSymmetric) (hA' : A'.IsSymmetric)
    (moments : ∀ k : ℕ, B.adjoint.comp ((A ^ k).comp B) =
      B'.adjoint.comp ((A' ^ k).comp B')) :
    (combination A B).ker = (combination A' B').ker := by
  ext v
  simp only [LinearMap.mem_ker]
  calc
    combination A B v = 0 ↔
        inner ℝ (combination A B v) (combination A B v) = 0 :=
      (inner_self_eq_zero (𝕜 := ℝ)).symm
    _ ↔ inner ℝ (combination A' B' v) (combination A' B' v) = 0 := by
      rw [combination_gram A A' B B' hA hA' moments]
    _ ↔ combination A' B' v = 0 := inner_self_eq_zero (𝕜 := ℝ)

/-- Minimal symmetric real realizations with equal moments are orthogonally equivalent.
The reachable subspace is the repository's span of all nonnegative input iterates. -/
theorem minimal_symmetric_realization_uniqueness
    (A : E →ₗ[ℝ] E) (A' : E' →ₗ[ℝ] E') (B : U →ₗ[ℝ] E) (B' : U →ₗ[ℝ] E')
    (hA : A.IsSymmetric) (hA' : A'.IsSymmetric)
    (moments : ∀ k : ℕ, B.adjoint.comp ((A ^ k).comp B) =
      B'.adjoint.comp ((A' ^ k).comp B'))
    (minimal : reachableSubspace A B = ⊤) (minimal' : reachableSubspace A' B' = ⊤) :
    ∃ Q : E ≃ₗᵢ[ℝ] E', Q.toLinearMap.comp A = A'.comp Q.toLinearMap ∧
      Q.toLinearMap.comp B = B' := by
  let F := combination A B
  let G := combination A' B'
  have hF : Function.Surjective F := combination_surjective A B minimal
  have hG : Function.Surjective G := combination_surjective A' B' minimal'
  have kernels : F.ker = G.ker := combination_kernel A A' B B' hA hA' moments
  let descent := F.ker.liftQ G kernels.le
  let transport : E →ₗ[ℝ] E' :=
    descent.comp (F.quotKerEquivOfSurjective hF).symm.toLinearMap
  have transport_combination (v : ℕ →₀ U) : transport (F v) = G v := by
    simp [transport, descent]
  have transport_inner (x y : E) :
      inner ℝ (transport x) (transport y) = inner ℝ x y := by
    obtain ⟨v, rfl⟩ := hF x
    obtain ⟨w, rfl⟩ := hF y
    rw [transport_combination, transport_combination]
    exact (combination_gram A A' B B' hA hA' moments v w).symm
  have transport_surjective : Function.Surjective transport := by
    intro y
    obtain ⟨v, rfl⟩ := hG y
    exact ⟨F v, transport_combination v⟩
  let equivalence : E ≃ₗ[ℝ] E' := LinearEquiv.ofBijective transport
    ⟨(transport.isometryOfInner transport_inner).injective, transport_surjective⟩
  let Q : E ≃ₗᵢ[ℝ] E' := equivalence.isometryOfInner transport_inner
  have Q_generator (k : ℕ) (v : U) : Q ((A ^ k) (B v)) = (A' ^ k) (B' v) := by
    change transport ((A ^ k) (B v)) = (A' ^ k) (B' v)
    simpa only [F, G, combination_single] using transport_combination (Finsupp.single k v)
  refine ⟨Q, ?_, ?_⟩
  · apply LinearMap.ext_on minimal
    rintro x ⟨k, v, rfl⟩
    change Q (A ((A ^ k) (B v))) = A' (Q ((A ^ k) (B v)))
    rw [← Module.End.mul_apply, ← pow_succ', Q_generator, Q_generator,
      pow_succ', Module.End.mul_apply]
  · ext v
    simpa using Q_generator 0 v

#print axioms minimal_symmetric_realization_uniqueness

example : Nonempty (ℝ →ₗ[ℝ] ℝ) ∧ Nonempty (ℕ →₀ ℝ) :=
  ⟨⟨LinearMap.id⟩, ⟨0⟩⟩

example :
    let A : ℝ →ₗ[ℝ] ℝ := 2 • LinearMap.id
    let B : ℝ →ₗ[ℝ] ℝ := LinearMap.id
    A.IsSymmetric ∧ A.IsSymmetric ∧
      (∀ k : ℕ, B.adjoint.comp ((A ^ k).comp B) =
        B.adjoint.comp ((A ^ k).comp B)) ∧
      reachableSubspace A B = ⊤ ∧ reachableSubspace A B = ⊤ := by
  dsimp only
  have symmetric : (2 • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)).IsSymmetric := by
    intro x y
    simp [mul_left_comm, mul_comm]
  have minimal : reachableSubspace (2 • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) LinearMap.id = ⊤ := by
    apply top_unique
    intro x _
    apply Submodule.subset_span
    exact ⟨0, x, by simp⟩
  exact ⟨symmetric, symmetric, fun _ => rfl, minimal, minimal⟩

end D5.S3.Quantum.Measurements.MinimalSymmetricRealizationUniqueness
