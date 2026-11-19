/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/AllPartitionExpansion
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/AllPartitionExpansion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite-label tuples enumerate every collision partition with an explicit configuration bound. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.PartitionCollisionExpansion
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.PairingPartitionCorrespondence

/-! An index-independent finite enumeration of all equality partitions. -/

open scoped BigOperators

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

/-- Every partition of `Fin k` is realized by a tuple valued in `Fin k`. -/
theorem tupleKernelPatterns_fin_universal {k : ℕ} (σ : Setoid (Fin k)) :
    σ ∈ tupleKernelPatterns k (Fin k) := by
  classical
  have hc : Fintype.card (Quotient σ) ≤ k := by
    simpa only [Fintype.card_fin] using Fintype.card_quotient_le σ
  let enc : Quotient σ → Fin k := fun B =>
    Fin.castLE hc ((Fintype.equivFin (Quotient σ)) B)
  have hinj : Function.Injective enc :=
    (Fin.castLE_injective hc).comp (Fintype.equivFin (Quotient σ)).injective
  refine Finset.mem_image.mpr ⟨enc ∘ Quotient.mk σ, Finset.mem_univ _, ?_⟩
  ext i j
  exact ⟨fun h => Quotient.exact (hinj h), fun h => congrArg enc (Quotient.sound h)⟩

/-- Summing a function of the partial pairing over all zero-degree partition
configurations counts each partial pairing exactly once. -/
theorem sum_pairing_partition_configurations {k : ℕ}
    (G : {P : Finset (Finset (Fin k)) // IsPartialPairing Finset.univ P} → ℝ) :
    (∑ σ ∈ tupleKernelPatterns k (Fin k), ∑ S : Finset (Quotient σ),
      if hs : ∀ B, mult (Quotient.mk σ) B = if B ∈ S then 1 else 2 then
        G ⟨pairingPartitionPairs ⟨σ, S, hs⟩,
          pairingPartitionPairs_isPartial ⟨σ, S, hs⟩⟩ else 0) = ∑ P, G P := by
  classical
  let configs : Finset (Σ σ : Setoid (Fin k), Finset (Quotient σ)) :=
    (tupleKernelPatterns k (Fin k)).sigma (fun _ => Finset.univ)
  let good := configs.filter (fun x =>
    ∀ B, mult (Quotient.mk x.1) B = if B ∈ x.2 then 1 else 2)
  let term (x : Σ σ : Setoid (Fin k), Finset (Quotient σ)) : ℝ :=
    if hs : ∀ B, mult (Quotient.mk x.1) B = if B ∈ x.2 then 1 else 2 then
      G ⟨pairingPartitionPairs ⟨x.1, x.2, hs⟩,
        pairingPartitionPairs_isPartial ⟨x.1, x.2, hs⟩⟩ else 0
  change (∑ σ ∈ tupleKernelPatterns k (Fin k), ∑ S : Finset (Quotient σ),
    term ⟨σ, S⟩) = _
  rw [Finset.sum_sigma']
  change (∑ x ∈ configs, term x) = _
  have hfilter : (∑ x ∈ configs, term x) = ∑ x ∈ good, term x := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro x hx hnot
    have hbad : ¬(∀ B, mult (Quotient.mk x.1) B = if B ∈ x.2 then 1 else 2) := by
      intro h
      exact hnot (Finset.mem_filter.mpr ⟨hx, h⟩)
    simp only [term, dif_neg hbad]
  rw [hfilter]
  let data (x) (hx : x ∈ good) : PairingPartitionData k :=
    ⟨x.1, x.2, (Finset.mem_filter.mp hx).2⟩
  apply Finset.sum_bij (fun x hx =>
    (⟨pairingPartitionPairs (data x hx), pairingPartitionPairs_isPartial (data x hx)⟩ :
      {P : Finset (Finset (Fin k)) // IsPartialPairing Finset.univ P}))
  · intro x hx
    exact Finset.mem_univ _
  · intro x hx y hy hxy
    have hD := pairingPartitionPairs_bijective.1.injective hxy
    exact congrArg (fun D : PairingPartitionData k =>
      (⟨D.partition, D.retained⟩ : Σ σ : Setoid (Fin k), Finset (Quotient σ))) hD
  · intro P hP
    obtain ⟨D, hD⟩ := pairingPartitionPairs_bijective.1.surjective P
    have hx : (⟨D.partition, D.retained⟩ : Σ σ : Setoid (Fin k), Finset (Quotient σ)) ∈
        good := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_sigma.mpr
        ⟨tupleKernelPatterns_fin_universal D.partition, Finset.mem_univ _⟩, D.sizes⟩
    exact ⟨⟨D.partition, D.retained⟩, hx, hD⟩
  · intro x hx
    dsimp only [term]
    rw [dif_pos (Finset.mem_filter.mp hx).2]

/-- Unavailable partitions contribute zero, so the moment expansion may use the
same finite set of all partitions for every underlying index type. -/
theorem quadratic_moment_eq_all_partition_expansion {ι A : Type*} [Fintype ι]
    [CommRing A] [Algebra ℝ A] {k : ℕ}
    (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (a b : ℝ)
    (hquad : ∀ d, Y d ^ 2 = a • Y d + b • (1 : A))
    (f : Fin k → ι → ℝ) :
    quadraticFamilyMoment ℓ Y f =
      ∑ σ ∈ tupleKernelPatterns k (Fin k), ∑ S : Finset (Quotient σ),
        ((∏ B ∈ S, (quadraticPowerCoeffs a b (mult (Quotient.mk σ) B)).1) *
         (∏ B ∈ Sᶜ, (quadraticPowerCoeffs a b (mult (Quotient.mk σ) B)).2)) *
        kernelDistinctMoment ℓ Y f σ S := by
  classical
  rw [quadratic_moment_eq_partition_expansion ℓ Y a b hquad f]
  apply Finset.sum_subset (fun σ _ => tupleKernelPatterns_fin_universal σ)
  intro σ hσ hnot
  apply Finset.sum_eq_zero
  intro S hS
  have hz : kernelDistinctMoment ℓ Y f σ S = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    exact False.elim (hnot (Finset.mem_image.mpr
      ⟨d, Finset.mem_univ _, (Finset.mem_filter.mp hd).2⟩))
  rw [hz, mul_zero]

/-- At degree zero, the quadratic reduction coefficient is one factor of
`b` for each edge of the corresponding partial pairing. -/
theorem pairingPartition_coefficient {k : ℕ} (D : PairingPartitionData k) (a b : ℝ) :
    (∏ B ∈ D.retained,
        (quadraticPowerCoeffs a b (mult (Quotient.mk D.partition) B)).1) *
      (∏ B ∈ D.retainedᶜ,
        (quadraticPowerCoeffs a b (mult (Quotient.mk D.partition) B)).2) =
      b ^ (pairingPartitionPairs D).card := by
  classical
  have hu : (∏ B ∈ D.retained,
      (quadraticPowerCoeffs a b (mult (Quotient.mk D.partition) B)).1) = 1 := by
    apply Finset.prod_eq_one
    intro B hB
    rw [D.sizes B, if_pos hB]
    simp [quadraticPowerCoeffs]
  have hv : (∏ B ∈ D.retainedᶜ,
      (quadraticPowerCoeffs a b (mult (Quotient.mk D.partition) B)).2) =
      b ^ D.retainedᶜ.card := by
    calc
      _ = ∏ _B ∈ D.retainedᶜ, b := by
        apply Finset.prod_congr rfl
        intro B hB
        rw [D.sizes B, if_neg (Finset.mem_compl.mp hB)]
        simp [quadraticPowerCoeffs, pow_two, QuadraticAlgebra.omega_mul_omega_eq_mk]
      _ = _ := by simp
  rw [hu, one_mul, hv, pairingPartitionPairs_bijective.2 D]

/-- There are at most `k^k * 2^k` partition and retained-subset configurations,
including the empty order. -/
theorem all_partition_configuration_bound (k : ℕ) :
    (∑ σ ∈ tupleKernelPatterns k (Fin k), Fintype.card (Finset (Quotient σ))) ≤
      k ^ k * 2 ^ k := by
  classical
  have hpart : (tupleKernelPatterns k (Fin k)).card ≤ k ^ k := by
    calc
      _ ≤ (Finset.univ : Finset (Fin k → Fin k)).card := Finset.card_image_le
      _ = _ := by simp
  calc
    _ = ∑ σ ∈ tupleKernelPatterns k (Fin k), 2 ^ Fintype.card (Quotient σ) := by
      simp only [Fintype.card_finset]
    _ ≤ ∑ _σ ∈ tupleKernelPatterns k (Fin k), 2 ^ k := by
      apply Finset.sum_le_sum
      intro σ hσ
      apply pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ))
      simpa only [Fintype.card_fin] using Fintype.card_quotient_le σ
    _ = (tupleKernelPatterns k (Fin k)).card * 2 ^ k := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ hpart

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
