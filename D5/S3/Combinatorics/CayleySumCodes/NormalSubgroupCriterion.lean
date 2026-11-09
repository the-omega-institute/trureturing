/- GID: D5/S3/Combinatorics/CayleySumCodes/NormalSubgroupCriterion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CayleySumCodes/NormalSubgroupCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The full corrected existential total-code criterion for normal subgroups. -/

import D5.S3.Combinatorics.CayleySumCodes.PerfectCodeTransversal
import D5.S3.Combinatorics.CayleySumCodes.CodeCentralizers
import Mathlib.Data.Set.Card

set_option autoImplicit false

namespace D5.S3.Combinatorics.CayleySumCodes.NormalSubgroupCriterion

open D5.S3.Combinatorics.CayleySumCodes.TotalPerfectCriterion
open D5.S3.Combinatorics.CayleySumCodes.PerfectCodeTransversal

variable {G : Type*} [Group G]

private theorem square_one (H : Subgroup G) : (1 : G) ∈ squares H :=
  ⟨1, H.one_mem, by simp⟩

private theorem coset_not_internal (H : Subgroup G) (g y : G) (hg : g ∉ H)
    (hh : g⁻¹ * y ∈ H) : y ∉ H := by
  intro hy
  apply hg
  have he : g = y * (g⁻¹ * y)⁻¹ := by simp [mul_assoc]
  rw [he]
  exact H.mul_mem hy (H.inv_mem hh)

private theorem transversal_internal (H : Subgroup G) (T : Set G)
    (ht : Subgroup.IsComplement T (H : Set G)) (h1 : (1 : G) ∈ T)
    (y : G) (hy : y ∈ T) (hyH : y ∈ H) : y = 1 := by
  obtain ⟨t, hh, hu⟩ := Subgroup.isComplement_iff_existsUnique_inv_mul_mem.mp ht 1
  exact congrArg Subtype.val ((hu ⟨y, hy⟩ (by simpa using H.inv_mem hyH)).trans
    (hu ⟨1, h1⟩ (by simp)).symm)

private theorem coset_card [Finite G] (H : Subgroup G) (T : Set G)
    (ht : Subgroup.IsComplement T (H : Set G)) (g : G) :
    Nat.card {y : G // y ∈ T ∧ g⁻¹ * y ∈ H} = 1 := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  obtain ⟨t, hh, hu⟩ := Subgroup.isComplement_iff_existsUnique_inv_mul_mem.mp ht g
  have inverse_mem (x : G) : x⁻¹ * g ∈ H ↔ g⁻¹ * x ∈ H := by
    simpa only [mul_inv_rev, inv_inv] using
      (H.inv_mem_iff : (x⁻¹ * g)⁻¹ ∈ H ↔ x⁻¹ * g ∈ H).symm
  have hx : ∃! y : G, y ∈ T ∧ g⁻¹ * y ∈ H := by
    refine ⟨t.1, ⟨t.2, (inverse_mem t.1).mp hh⟩, ?_⟩
    intro y hy
    exact congrArg Subtype.val (hu ⟨y, hy.1⟩ ((inverse_mem y).mpr hy.2))
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using
    (Fintype.existsUnique_iff_card_one _).mp hx

private theorem normal_erase (T : Set G) (hn : NormalSubset T) :
    NormalSubset (T \ {1}) := by
  intro a x hx
  refine ⟨hn a x hx.1, ?_⟩
  intro he
  apply hx.2
  apply Set.mem_singleton_iff.mpr
  have hh := congrArg (fun z : G => a⁻¹ * z * a) (Set.mem_singleton_iff.mp he)
  simpa [mul_assoc] using hh

private theorem attach [Finite G] (H : Subgroup G) (T S : Set G)
    (hn : NormalSubset T) (ht : Subgroup.IsComplement T (H : Set G)) (h1 : (1 : G) ∈ T)
    (hsn : NormalSubset S) (hsH : S ⊆ H)
    (hs : (∃ z : G, z ∈ H ∧ z ∉ squares H ∧ S = {z}) ∨
      (Nat.card S = 2 ∧ squares H ⊆ S)) :
    ∃ (Y : Set G) (hY : NormalSubset Y), IsTotalPerfectCode (sumGraph Y hY) H := by
  let Y := (T \ {1}) ∪ S
  have hY : NormalSubset Y := by
    intro a x hx
    exact hx.elim (fun h => Or.inl (normal_erase T hn a x h))
      (fun h => Or.inr (hsn a x h))
  refine ⟨Y, hY, (TotalPerfectCriterion.result H Y hY).mpr ⟨?_, ?_⟩⟩
  · intro g hg
    have he : {y : G | y ∈ Y ∧ g⁻¹ * y ∈ H} =
        {y : G | y ∈ T ∧ g⁻¹ * y ∈ H} := by
      ext y
      constructor
      · rintro ⟨hy | hy, hh⟩
        · exact ⟨hy.1, hh⟩
        · exact (coset_not_internal H g y hg hh (hsH hy)).elim
      · rintro ⟨hy, hh⟩
        have hne : y ≠ 1 := by
          intro he
          exact coset_not_internal H g y hg hh (he.symm ▸ H.one_mem)
        exact ⟨Or.inl ⟨hy, hne⟩, hh⟩
    change Nat.card ↥{y : G | y ∈ Y ∧ g⁻¹ * y ∈ H} = 1
    rw [he]
    exact coset_card H T ht g
  · have he : Y ∩ (H : Set G) = S := by
      ext y
      constructor
      · rintro ⟨hy | hy, hh⟩
        · exact (hy.2 (Set.mem_singleton_iff.mpr
            (transversal_internal H T ht h1 y hy.1 hh))).elim
        · exact hy
      · intro hy
        exact ⟨Or.inr hy, hsH hy⟩
    rcases hs with hs | hs
    · obtain ⟨z, hzH, hzs, hz⟩ := hs
      exact Or.inl ⟨z, hzH, hzs, he.trans hz⟩
    · refine Or.inr ⟨?_, ?_⟩
      · change Nat.card ↥(Y ∩ (H : Set G)) = 2
        rw [he]
        exact hs.1
      · exact he.symm ▸ hs.2

/-- For every normal subgroup of every finite group, existential total
perfect coding is equivalent to existential perfect coding together with
a central nonsquare in H or a square set of cardinality two. Both branches
of the corrected criterion are retained. -/
theorem result [Finite G] (H : Subgroup G) [H.Normal] :
    (∃ (Y : Set G) (hn : NormalSubset Y), IsTotalPerfectCode (sumGraph Y hn) H) ↔
    (∃ (X : Set G) (hn : NormalSubset X), IsPerfectCode (sumGraph X hn) H) ∧
      ((∃ z : G, z ∈ Subgroup.center G ∧ z ∈ H ∧ z ∉ squares H) ∨
        Nat.card (squares H) = 2) := by
  classical
  constructor
  · rintro ⟨Y, hn, hc⟩
    refine ⟨(normal_exists_iff H).mpr (NormalTransversal.result H Y hn hc), ?_⟩
    have hcent := CodeCentralizers.normal_inter_central H Y hn hc
    obtain ⟨_, ha | hb⟩ := (TotalPerfectCriterion.result H Y hn).mp hc
    · obtain ⟨z, hzH, hzs, he⟩ := ha
      have hz : z ∈ Y ∩ (H : Set G) := he.symm ▸ Set.mem_singleton z
      exact Or.inl ⟨z, hcent hz, hzH, hzs⟩
    · by_cases hs : Nat.card (squares H) = 2
      · exact Or.inr hs
      · have hle : Nat.card (squares H) ≤ 2 := by
          have he : Nat.card ↥(Y ∩ (H : Set G)) = 2 := hb.1
          have hh := Set.ncard_le_ncard hb.2
          change Nat.card (squares H) ≤ Nat.card ↥(Y ∩ (H : Set G)) at hh
          omega
        letI : Fintype (squares H) := Fintype.ofFinite (squares H)
        have hsub : Subsingleton (squares H) :=
          Fintype.card_le_one_iff_subsingleton.mp (by
            rw [← Nat.card_eq_fintype_card]
            omega)
        have hone : (1 : G) ∈ Y ∩ (H : Set G) := hb.2 (square_one H)
        have htw : Nat.card ↥(Y ∩ (H : Set G)) = 2 := hb.1
        letI : Fintype ↥(Y ∩ (H : Set G)) := Fintype.ofFinite _
        letI : Nontrivial ↥(Y ∩ (H : Set G)) :=
          Fintype.one_lt_card_iff_nontrivial.mp (by
            rw [← Nat.card_eq_fintype_card, htw]
            decide)
        obtain ⟨z, hz⟩ := exists_ne (⟨1, hone⟩ : ↥(Y ∩ (H : Set G)))
        refine Or.inl ⟨z.1, hcent z.2, z.2.2, ?_⟩
        intro hzS
        have he : z.1 = 1 := congrArg Subtype.val (hsub.elim ⟨z.1, hzS⟩ ⟨1, square_one H⟩)
        exact hz (Subtype.ext he)
  · rintro ⟨hpc, hz | hs⟩
    · obtain ⟨T, hn, h1, ht⟩ := (exists_iff H).mp hpc
      obtain ⟨z, hzc, hzH, hzs⟩ := hz
      have hzn : NormalSubset ({z} : Set G) := by
        intro a x hx
        have he : x = z := Set.mem_singleton_iff.mp hx
        subst x
        apply Set.mem_singleton_iff.mpr
        rw [Subgroup.mem_center_iff.mp hzc a]
        simp [mul_assoc]
      exact attach H T {z} hn ht h1 hzn (by intro x hx; exact (Set.mem_singleton_iff.mp hx).symm ▸ hzH)
        (Or.inl ⟨z, hzH, hzs, rfl⟩)
    · obtain ⟨T, hn, h1, ht⟩ := (exists_iff H).mp hpc
      have hsn : NormalSubset (squares H) := by
        rintro a _ ⟨h, hh, rfl⟩
        refine ⟨a * h * a⁻¹,
          Subgroup.Normal.conj_mem (inferInstance : H.Normal) h hh a, ?_⟩
        simp [mul_assoc]
      have hsH : squares H ⊆ H := by
        rintro _ ⟨h, hh, rfl⟩
        exact H.mul_mem hh hh
      exact attach H T (squares H) hn ht h1 hsn hsH (Or.inr ⟨hs, Set.Subset.rfl⟩)

#print axioms result

end D5.S3.Combinatorics.CayleySumCodes.NormalSubgroupCriterion
