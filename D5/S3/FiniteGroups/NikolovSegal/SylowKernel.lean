/- GID: D5/S3/FiniteGroups/NikolovSegal/SylowKernel
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/SylowKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The simple-section obstruction in a Sylow normalizer. -/

import D5.S3.FiniteGroups.NikolovSegal.Sections

set_option autoImplicit false

namespace NikolovSegal

universe u v
variable {A : Type u} {G : Type v} [Group A] [Group G]

/-- The normalizer of a Sylow p-subgroup has no simple section whose order is
divisible by p but which is not itself a p-group. -/
theorem not_involves_sylow_normalizer [Finite G] [IsSimpleGroup A]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hA : ¬IsPGroup p A) (hcard : p ∣ Nat.card A) :
    ¬Involves A (Subgroup.normalizer (P : Set G)) := by
  let K : Subgroup (Subgroup.normalizer (P : Set G)) :=
    (P : Subgroup G).subgroupOf (Subgroup.normalizer (P : Set G))
  have : K.Normal := Subgroup.normal_in_normalizer
  have hK : IsPGroup p K := P.isPGroup'.comap_subtype
  have hodd : ¬p ∣ Nat.card ((Subgroup.normalizer (P : Set G)) ⧸ K) := by
    change ¬p ∣ (P : Subgroup G).relIndex (Subgroup.normalizer (P : Set G))
    intro h
    exact P.not_dvd_index
      (h.trans (Subgroup.relIndex_dvd_index_of_le Subgroup.le_normalizer))
  intro h
  rcases simple_involves_map_or_kernel (QuotientGroup.mk' K) h with hq | hk
  · exact not_involves_of_prime_dvd hcard hodd hq
  · have hk' : Involves A K := by
      rw [QuotientGroup.ker_mk'] at hk
      exact hk
    exact not_involves_pGroup hK hA hk'

end NikolovSegal
