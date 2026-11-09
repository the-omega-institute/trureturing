/- GID: D5/S3/Combinatorics/CayleySumCodes/NormalTransversal
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CayleySumCodes/NormalTransversal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Both total-code cases supply an actual normal left transversal. -/

import D5.S3.Combinatorics.CayleySumCodes.TotalPerfectCriterion

set_option autoImplicit false

namespace D5.S3.Combinatorics.CayleySumCodes.NormalTransversal

open D5.S3.Combinatorics.CayleySumCodes.TotalPerfectCriterion

variable {G : Type*} [Group G]

/-- A conjugation-invariant left transversal, using the existing bijective
multiplication definition of a subgroup complement. No square restriction
is included in this property. -/
def NLT (H : Subgroup G) : Prop :=
  ∃ T : Set G, NormalSubset T ∧ Subgroup.IsComplement T (H : Set G)

private theorem normal_without_one (Y : Set G) (hY : NormalSubset Y) :
    NormalSubset (Y \ {1}) := by
  intro a x hx
  refine ⟨hY a x hx.1, ?_⟩
  intro he
  have eqone : a * x * a⁻¹ = 1 := Set.mem_singleton_iff.mp he
  apply hx.2
  apply Set.mem_singleton_iff.mpr
  have := congrArg (fun y => a⁻¹ * y * a) eqone
  simpa [mul_assoc] using this

private theorem complement_of_card_one [Finite G] (H : Subgroup G) (T : Set G)
    (ht : ∀ g : G, Nat.card {y : G // y ∈ T ∧ g⁻¹ * y ∈ H} = 1) :
    Subgroup.IsComplement T (H : Set G) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  apply Subgroup.isComplement_iff_existsUnique_inv_mul_mem.mpr
  intro g
  have hu : ∃! y : G, y ∈ T ∧ g⁻¹ * y ∈ H := by
    apply Fintype.existsUnique_iff_card_one.mpr
    simpa only [Nat.card_eq_fintype_card] using ht g
  obtain ⟨y, ⟨hy, hh⟩, hu⟩ := hu
  have inverse_mem (z : G) : z⁻¹ * g ∈ H ↔ g⁻¹ * z ∈ H := by
    simpa only [mul_inv_rev, inv_inv] using
      (H.inv_mem_iff : (z⁻¹ * g)⁻¹ ∈ H ↔ z⁻¹ * g ∈ H).symm
  refine ⟨⟨y, hy⟩, (inverse_mem y).mpr hh, ?_⟩
  intro z hz
  exact Subtype.ext (hu z.1 ⟨z.2, (inverse_mem z.1).mp hz⟩)

/-- A total perfect subgroup code always has a normal left transversal.
In the singleton case it is Y itself. In the two-element case it is Y with
the identity removed, rather than an incorrect singleton-case assumption. -/
theorem result [Finite G] (H : Subgroup G) (Y : Set G) (hY : NormalSubset Y)
    (hc : IsTotalPerfectCode (sumGraph Y hY) H) : NLT H := by
  classical
  let : Fintype G := Fintype.ofFinite G
  obtain ⟨ho, ha | hb⟩ := (TotalPerfectCriterion.result H Y hY).mp hc
  · refine ⟨Y, hY, complement_of_card_one H Y ?_⟩
    intro g
    by_cases hg : g ∈ H
    · obtain ⟨z, hzH, _, hz⟩ := ha
      have he : {y : G | y ∈ Y ∧ g⁻¹ * y ∈ H} = {z} := by
        ext y
        have iffH : g⁻¹ * y ∈ H ↔ y ∈ H := H.mul_mem_cancel_left (H.inv_mem hg)
        simp only [Set.mem_setOf_eq, iffH]
        change y ∈ Y ∩ (H : Set G) ↔ y ∈ ({z} : Set G)
        rw [hz]
      rw [show {y : G // y ∈ Y ∧ g⁻¹ * y ∈ H} = {y : G // y ∈ ({z} : Set G)} from
        congrArg (fun S : Set G => ↥S) he]
      simp
    · exact ho g hg
  · refine ⟨Y \ {1}, normal_without_one Y hY, complement_of_card_one H (Y \ {1}) ?_⟩
    intro g
    have h1 : (1 : G) ∈ Y ∧ (1 : G) ∈ H := hb.2 ⟨1, H.one_mem, by simp⟩
    by_cases hg : g ∈ H
    · have he : (Finset.univ.filter (fun y : G => y ∈ Y ∧ y ∈ H)).card = 2 := by
        simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using hb.1
      have hm : (1 : G) ∈ Finset.univ.filter (fun y : G => y ∈ Y ∧ y ∈ H) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact h1
      have hcount := Finset.card_erase_of_mem hm
      rw [he] at hcount
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      convert hcount using 1
      congr 1
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_diff,
        Set.mem_singleton_iff, Finset.mem_erase]
      rw [H.mul_mem_cancel_left (H.inv_mem hg)]
      tauto
    · have no_one : g⁻¹ * (1 : G) ∉ H := by
        simpa only [mul_one, H.inv_mem_iff] using hg
      have he : {y : G | y ∈ Y \ {1} ∧ g⁻¹ * y ∈ H} =
          {y : G | y ∈ Y ∧ g⁻¹ * y ∈ H} := by
        ext y
        simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_singleton_iff]
        constructor
        · exact fun h => ⟨h.1.1, h.2⟩
        · rintro ⟨hy, hh⟩
          exact ⟨⟨hy, fun h => no_one (h ▸ hh)⟩, hh⟩
      change Nat.card ↥{y : G | y ∈ Y \ {1} ∧ g⁻¹ * y ∈ H} = 1
      rw [he]
      exact ho g hg

#print axioms result

end D5.S3.Combinatorics.CayleySumCodes.NormalTransversal
