/- GID: D5/S3/StatisticalMechanics/HardCore/OccupationMoments
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/HardCore/OccupationMoments
   mirror-E: none(waiver:exact-configuration-moment-identities)
   anchors: []
   utility: none
   digest: Actual independent configurations give marked sums and the Euler moment hierarchy. -/

import D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.StatisticalMechanics.HardCore.OccupationMoments

open scoped BigOperators
open D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion

variable {α R 𝕜 : Type*} [DecidableEq α]
variable (G : SimpleGraph α) [DecidableRel G.Adj]

/-- Actual configurations omitting a vertex are exactly those on the erased
vertex domain. The marked vertex need not belong to the domain. -/
theorem configurations_erase_eq_filter (V : Finset α) (v : α) :
    configurations G (V.erase v) = (configurations G V).filter (fun S => v ∉ S) := by
  ext S
  simp only [configurations, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨hsub, hind⟩
    refine ⟨⟨fun u hu => Finset.mem_of_mem_erase (hsub hu), hind⟩, ?_⟩
    intro hv
    exact Finset.notMem_erase v V (hsub hv)
  · rintro ⟨⟨hsub, hind⟩, hv⟩
    refine ⟨?_, hind⟩
    intro u hu
    exact Finset.mem_erase.mpr ⟨fun h => hv (h ▸ hu), hsub hu⟩

/-- Partition the full configuration weight by actual root occupancy, before
any division. This semiring identity also holds at zeros of a partition. -/
theorem occupied_weight_add_erased [CommSemiring R]
    (V : Finset α) (v : α) (w : α → R) :
    (∑ S ∈ configurations G V, if v ∈ S then ∏ u ∈ S, w u else 0) +
      partition G (V.erase v) w = partition G V w := by
  unfold partition
  rw [configurations_erase_eq_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hv : v ∈ S <;> simp [hv]

/-- Count each weighted independent configuration once per occupied vertex.
This is an exact finite double-counting identity; no independence of vertex
indicators is assumed. -/
theorem weighted_cardinality_eq_marked_sum [CommSemiring R]
    (V : Finset α) (w : α → R) :
    (∑ S ∈ configurations G V, (S.card : R) * ∏ u ∈ S, w u) =
      ∑ v ∈ V, ∑ S ∈ configurations G V,
        if v ∈ S then ∏ u ∈ S, w u else 0 := by
  calc
    _ = ∑ S ∈ configurations G V, ∑ v ∈ V,
          if v ∈ S then ∏ u ∈ S, w u else 0 := by
      apply Finset.sum_congr rfl
      intro S hS
      have hsub : S ⊆ V := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
      have hf : V.filter (fun v => v ∈ S) = S := by
        ext v
        simp only [Finset.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
      rw [← Finset.sum_filter, hf]
      simp [nsmul_eq_mul]
    _ = _ := Finset.sum_comm

/-- The first weighted cardinality sum equals the sum of actual deletion
partition differences. The identity is over every commutative ring. -/
theorem weighted_cardinality_eq_partition_differences [CommRing R]
    (V : Finset α) (w : α → R) :
    (∑ S ∈ configurations G V, (S.card : R) * ∏ u ∈ S, w u) =
      ∑ v ∈ V, (partition G V w - partition G (V.erase v) w) := by
  rw [weighted_cardinality_eq_marked_sum]
  apply Finset.sum_congr rfl
  intro v _
  exact eq_sub_iff_add_eq.mpr (occupied_weight_add_erased G V v w)

/-- Unnormalized occupation moment on the original configuration family.
Order zero is the existing partition; no replacement graph model is introduced. -/
def moment [CommSemiring R] (V : Finset α) (k : ℕ) (z : R) : R :=
  ∑ S ∈ configurations G V, (S.card : R) ^ k * z ^ S.card

/-- The zeroth moment is exactly the existing constant-activity partition. -/
theorem moment_zero_order [CommSemiring R] (V : Finset α) (z : R) :
    moment G V 0 z = partition G V (fun _ => z) := by
  simp [moment, partition]

/-- The first moment has a local-deletion expression at every activity,
including activity zero and partition zeros. -/
theorem moment_one_eq_deletions [CommRing R] (V : Finset α) (z : R) :
    moment G V 1 z =
      ∑ v ∈ V, (partition G V (fun _ => z) - partition G (V.erase v) (fun _ => z)) := by
  simpa [moment] using weighted_cardinality_eq_partition_differences G V (fun _ => z)

/-- Every positive-order occupation moment vanishes at zero activity. -/
theorem moment_succ_at_zero [CommSemiring R] (V : Finset α) (k : ℕ) :
    moment G V (k + 1) (0 : R) = 0 := by
  apply Finset.sum_eq_zero
  intro S _
  by_cases he : S = ∅
  · simp [he]
  · have hc : S.card ≠ 0 := by simpa using he
    simp [zero_pow hc]

/-- Direct termwise differentiation of the actual finite configuration sum.
The natural predecessor in the exponent is harmless at the empty configuration. -/
theorem moment_hasDerivAt [NontriviallyNormedField 𝕜]
    (V : Finset α) (k : ℕ) (z : 𝕜) :
    HasDerivAt (moment G V k)
      (∑ S ∈ configurations G V,
        (S.card : 𝕜) ^ k * ((S.card : 𝕜) * z ^ (S.card - 1))) z := by
  unfold moment
  exact HasDerivAt.fun_sum (fun S _ => by
    convert!
      ((hasDerivAt_id z).pow S.card).const_mul ((S.card : 𝕜) ^ k) using 1 <;> simp)

/-- Euler differentiation raises the occupation moment order. No division by
activity or nonzero-activity assumption occurs, for any order k. -/
theorem euler_moment [NontriviallyNormedField 𝕜]
    (V : Finset α) (k : ℕ) (z : 𝕜) :
    z * deriv (moment G V k) z = moment G V (k + 1) z := by
  rw [(moment_hasDerivAt G V k z).deriv, moment, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  cases hn : S.card with
  | zero => simp [hn]
  | succ n =>
      simp only [hn, Nat.add_sub_cancel, pow_succ]
      ring

/-- The targeted observable identity for every finite domain of every simple
graph. It holds over the real or complex numbers even at a partition zero. -/
theorem partition_euler_occupation [NontriviallyNormedField 𝕜]
    (V : Finset α) (z : 𝕜) :
    z * deriv (fun t : 𝕜 => partition G V (fun _ => t)) z =
      ∑ v ∈ V, (partition G V (fun _ => z) - partition G (V.erase v) (fun _ => z)) := by
  have h := euler_moment G V 0 z
  have hf : (moment G V 0 : 𝕜 → 𝕜) =
      (fun t : 𝕜 => partition G V (fun _ => t)) := by
    funext t
    exact moment_zero_order G V t
  rw [hf] at h
  simpa only [zero_add, moment_one_eq_deletions] using h

/-- Normalized moments satisfy a covariance-type response hierarchy wherever
the actual partition is nonzero. Activity zero is retained in this formula. -/
theorem normalized_moment_response [NontriviallyNormedField 𝕜]
    (V : Finset α) (k : ℕ) (z : 𝕜)
    (hne : moment G V 0 z ≠ 0) :
    z * deriv (fun t : 𝕜 => moment G V k t / moment G V 0 t) z =
      moment G V (k + 1) z / moment G V 0 z -
        (moment G V k z / moment G V 0 z) * (moment G V 1 z / moment G V 0 z) := by
  have hk := (moment_hasDerivAt G V k z).differentiableAt.hasDerivAt
  have h0 := (moment_hasDerivAt G V 0 z).differentiableAt.hasDerivAt
  have hd := (hk.div h0 hne).deriv
  change deriv (fun t : 𝕜 => moment G V k t / moment G V 0 t) z = _ at hd
  rw [hd]
  calc
    _ = ((z * deriv (moment G V k) z) * moment G V 0 z -
          moment G V k z * (z * deriv (moment G V 0) z)) / (moment G V 0 z) ^ 2 := by ring
    _ = (moment G V (k + 1) z * moment G V 0 z -
          moment G V k z * moment G V 1 z) / (moment G V 0 z) ^ 2 := by
      rw [euler_moment, euler_moment]
    _ = _ := by field_simp [hne]

#print axioms weighted_cardinality_eq_partition_differences
#print axioms euler_moment
#print axioms partition_euler_occupation
#print axioms normalized_moment_response

end D5.S3.StatisticalMechanics.HardCore.OccupationMoments
