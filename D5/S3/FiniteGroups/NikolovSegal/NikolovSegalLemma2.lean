/- GID: D5/S3/FiniteGroups/NikolovSegal/NikolovSegalLemma2
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/NikolovSegalLemma2
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A supplement controlling every large alternating section and its maximum. -/

import D5.S3.FiniteGroups.NikolovSegal.SylowKernel
import D5.S3.FiniteGroups.NikolovSegal.AlternatingBounds
import D5.S3.FiniteGroups.NikolovSegal.Alpha

set_option autoImplicit false

namespace NikolovSegal

universe u v
variable {G : Type u} [Group G] [Finite G]

/-- Every appropriate simple section of the Sylow normalizer descends through
the map to G/N. The kernel embeds in the Sylow normalizer inside N. -/
theorem sylow_normalizer_section_transfer
    (N : Subgroup G) [N.Normal] {p : ℕ} [Fact p.Prime] (P : Sylow p N)
    {A : Type v} [Group A] [IsSimpleGroup A]
    (hA : ¬IsPGroup p A) (hcard : p ∣ Nat.card A)
    (h : Involves A (Subgroup.normalizer (((P : Subgroup N).map N.subtype) : Set G))) :
    Involves A (G ⧸ N) := by
  let L : Subgroup G := Subgroup.normalizer (((P : Subgroup N).map N.subtype) : Set G)
  let q : L →* G ⧸ N := (QuotientGroup.mk' N).comp L.subtype
  rcases simple_involves_map_or_kernel q h with hq | hk
  · exact hq
  · have heq : L.comap N.subtype = Subgroup.normalizer (P : Set N) := by
      have heq₀ := Subgroup.comap_normalizer_eq_of_le_range
        ((P : Subgroup N).map_le_range N.subtype)
      have hP : ((P : Subgroup N).map N.subtype).comap N.subtype = (P : Subgroup N) :=
        Subgroup.comap_map_eq_self_of_injective N.subtype_injective _
      exact heq₀.trans (congrArg (fun H : Subgroup N => Subgroup.normalizer (H : Set N)) hP)
    let j : q.ker →* N :=
      (L.subtype.comp q.ker.subtype).codRestrict N (fun x =>
        (QuotientGroup.eq_one_iff (x.val : G)).mp (MonoidHom.mem_ker.mp x.property))
    have hj : ∀ x : q.ker, j x ∈ Subgroup.normalizer (P : Set N) := by
      intro x
      rw [← heq]
      exact x.val.property
    let i : q.ker →* Subgroup.normalizer (P : Set N) :=
      j.codRestrict _ hj
    have hi : Function.Injective i := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : Subgroup.normalizer (P : Set N) => ((z : N) : G)) hxy
    exact (not_involves_sylow_normalizer P hA hcard)
      (involves_of_injective i hi hk) |>.elim

/-- Complete section form of Nikolov--Segal (2011), p. 504, Lemma 2.
The same supplement works for every alternating degree k ≥ 5. -/
theorem exists_supplement_preserving_alternating_sections
    (N : Subgroup G) [N.Normal] :
    ∃ L : Subgroup G, N ⊔ L = ⊤ ∧
      ∀ k : ℕ, 5 ≤ k →
        Involves (alternatingGroup (Fin k)) L →
        Involves (alternatingGroup (Fin k)) (G ⧸ N) := by
  classical
  let P : Sylow 2 N := Sylow.nonempty.some
  refine ⟨Subgroup.normalizer (((P : Subgroup N).map N.subtype) : Set G), ?_, ?_⟩
  · simpa only [sup_comm] using P.normalizer_sup_eq_top
  · intro k hk h
    have : IsSimpleGroup (alternatingGroup (Fin k)) :=
      alternatingGroup.isSimpleGroup (by simpa using hk)
    exact sylow_normalizer_section_transfer N P
      (alternating_not_twoGroup hk) (two_dvd_card_alternating hk) h

/-- The paper's exact maximum inequality with alpha verified as a true maximum. -/
theorem exists_supplement_alpha_le (N : Subgroup G) [N.Normal] :
    ∃ L : Subgroup G, N ⊔ L = ⊤ ∧ alpha L ≤ max (alpha (G ⧸ N)) 4 := by
  obtain ⟨L, hL, htransfer⟩ := exists_supplement_preserving_alternating_sections N
  exact ⟨L, hL, alpha_le_max_of_section_transfer htransfer⟩

end NikolovSegal
