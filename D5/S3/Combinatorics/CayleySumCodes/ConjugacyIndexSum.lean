/- GID: D5/S3/Combinatorics/CayleySumCodes/ConjugacyIndexSum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CayleySumCodes/ConjugacyIndexSum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The exact centralizer-index sum in both total-code cases. -/

import D5.S3.Combinatorics.CayleySumCodes.CodeCentralizers
import Mathlib.GroupTheory.Index
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Combinatorics.CayleySumCodes.ConjugacyIndexSum

open D5.S3.Combinatorics.CayleySumCodes.TotalPerfectCriterion

variable {G : Type*} [Group G]

private theorem partition_card [Finite G] {ι : Type*} [Fintype ι]
    (Y : Set G) (y : ι → G) (hcover : Y = ⋃ i, conjugatesOf (y i))
    (hdisj : Pairwise (fun i j => Disjoint (conjugatesOf (y i)) (conjugatesOf (y j)))) :
    Nat.card Y = ∑ i, (conjugatesOf (y i)).ncard := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  let f : (Σ i, ↥(conjugatesOf (y i))) → Y := fun z =>
    ⟨z.2.1, hcover.symm ▸ Set.mem_iUnion.mpr ⟨z.1, z.2.2⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨i, x⟩ ⟨j, z⟩ he
      have hxz : x.1 = z.1 := congrArg Subtype.val he
      have hij : i = j := by
        by_contra hn
        exact Set.disjoint_left.mp (hdisj hn) x.2 (hxz.symm ▸ z.2)
      subst j
      exact congrArg (Sigma.mk i) (Subtype.ext hxz)
    · intro z
      have hz : z.1 ∈ ⋃ i, conjugatesOf (y i) := hcover ▸ z.2
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
      exact ⟨⟨i, ⟨z.1, hi⟩⟩, Subtype.ext rfl⟩
  have hc := Nat.card_congr (Equiv.ofBijective f hf)
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma] at hc
  simpa only [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using hc.symm

open scoped Classical in
/-- For an arbitrary complete disjoint decomposition of the actual normal
connection set into conjugacy classes, the centralizer indices are legitimate
because normal H centralizes every connection element. Their reciprocal sum
is exactly 1 or 1+1/[G:H], according to identity membership in Y. -/
theorem result [Finite G] (H : Subgroup G) [H.Normal] (Y : Set G)
    (hn : NormalSubset Y) (hc : IsTotalPerfectCode (sumGraph Y hn) H)
    {ι : Type*} [Fintype ι] (y : ι → G)
    (hcover : Y = ⋃ i, conjugatesOf (y i))
    (hdisj : Pairwise (fun i j => Disjoint (conjugatesOf (y i)) (conjugatesOf (y j)))) :
    (∀ i, H ≤ Subgroup.centralizer {y i}) ∧
    (∑ i, (1 : ℚ) / (H.relIndex (Subgroup.centralizer {y i}) : ℚ)) =
      1 + (if (1 : G) ∈ Y then (1 : ℚ) / (H.index : ℚ) else 0) := by
  classical
  have hle (i : ι) : H ≤ Subgroup.centralizer {y i} := by
    intro h hh z hz
    have hcy : h ∈ Subgroup.centralizer Y := CodeCentralizers.core H Y hn hc
      (H.normalCore_eq_self.symm ▸ hh)
    have hy : y i ∈ Y := hcover.symm ▸ Set.mem_iUnion.mpr ⟨i, mem_conjugatesOf_self⟩
    simpa only [Set.mem_singleton_iff.mp hz] using hcy (y i) hy
  refine ⟨hle, ?_⟩
  have hi : (H.index : ℚ) ≠ 0 := by
    exact_mod_cast H.index_ne_zero_of_finite
  have hterm (i : ι) :
      (1 : ℚ) / (H.relIndex (Subgroup.centralizer {y i}) : ℚ) =
        ((conjugatesOf (y i)).ncard : ℚ) / (H.index : ℚ) := by
    have he := H.relIndex_mul_index (hle i)
    have hri : (H.relIndex (Subgroup.centralizer {y i}) : ℚ) ≠ 0 := by
      have hn : H.relIndex (Subgroup.centralizer {y i}) ≠ 0 := by
        intro hz
        rw [hz, zero_mul] at he
        exact H.index_ne_zero_of_finite he.symm
      exact_mod_cast hn
    have heq : (H.relIndex (Subgroup.centralizer {y i}) : ℚ) *
        ((Subgroup.centralizer {y i}).index : ℚ) = (H.index : ℚ) := by
      exact_mod_cast he
    rw [← Subgroup.index_centralizer_eq_ncard]
    field_simp
    exact heq.symm
  simp_rw [hterm]
  rw [← Finset.sum_div, ← Nat.cast_sum, ← partition_card Y y hcover hdisj,
    NormalTransversal.cardinal H Y hn hc]
  by_cases h1 : (1 : G) ∈ Y
  · simp only [if_pos h1, Nat.cast_add, Nat.cast_one]
    field_simp
  · simp only [if_neg h1, Nat.add_zero, add_zero]
    exact div_self hi

#print axioms result

end D5.S3.Combinatorics.CayleySumCodes.ConjugacyIndexSum
