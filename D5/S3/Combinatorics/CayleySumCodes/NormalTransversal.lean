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

/-- Restrict an actual normal transversal to any intermediate subgroup. The
subgroup need not be subnormal. This is NLT inheritance, not code inheritance. -/
theorem restrict (H M : Subgroup G) (hHM : H ≤ M) (hH : NLT H) :
    NLT (H.subgroupOf M) := by
  obtain ⟨T, hn, ht⟩ := hH
  refine ⟨{m : M | m.1 ∈ T}, ?_, ?_⟩
  · intro a x hx
    exact hn a.1 x.1 hx
  · apply Subgroup.isComplement_iff_existsUnique_inv_mul_mem.mpr
    intro g
    obtain ⟨s, hs, hu⟩ := Subgroup.isComplement_iff_existsUnique_inv_mul_mem.mp ht g.1
    have sm : s.1 ∈ M := by
      have hm : s.1⁻¹ * g.1 ∈ M := hHM hs
      have he : s.1 = g.1 * (s.1⁻¹ * g.1)⁻¹ := by simp [mul_assoc]
      rw [he]
      exact M.mul_mem g.2 (M.inv_mem hm)
    refine ⟨⟨⟨s.1, sm⟩, s.2⟩, hs, ?_⟩
    intro z hz
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : T => x.1) (hu ⟨z.1.1, z.2⟩ hz)

/-- A surjective group homomorphism carries a normal transversal to a normal
transversal whenever its kernel lies in H. In particular this applies to
G/N and H/N for any normal N contained in H. It does not assert quotient
inheritance of total perfect coding. -/
theorem map {K : Type*} [Group K] (f : G →* K) (hf : Function.Surjective f)
    (H : Subgroup G) (hk : f.ker ≤ H) (hH : NLT H) : NLT (H.map f) := by
  obtain ⟨T, hn, ht⟩ := hH
  refine ⟨f '' T, ?_, ?_⟩
  · rintro a _ ⟨x, hx, rfl⟩
    obtain ⟨g, rfl⟩ := hf a
    refine ⟨g * x * g⁻¹, hn g x hx, ?_⟩
    simp only [map_mul, map_inv]
  · apply Subgroup.isComplement_iff_existsUnique_inv_mul_mem.mpr
    intro k
    obtain ⟨g, rfl⟩ := hf k
    obtain ⟨t, hh, hu⟩ := Subgroup.isComplement_iff_existsUnique_inv_mul_mem.mp ht g
    have mem_map (x : G) : f x ∈ H.map f ↔ x ∈ H := by
      change x ∈ (H.map f).comap f ↔ x ∈ H
      rw [Subgroup.comap_map_eq_self hk]
    refine ⟨⟨f t.1, ⟨t.1, t.2, rfl⟩⟩, ?_, ?_⟩
    · change (f t.1)⁻¹ * f g ∈ H.map f
      simpa only [map_mul, map_inv] using (mem_map (t.1⁻¹ * g)).mpr hh
    · rintro z hz
      obtain ⟨u, huT, huZ⟩ := z.2
      change z.1⁻¹ * f g ∈ H.map f at hz
      have hmem : u⁻¹ * g ∈ H := by
        apply (mem_map _).mp
        simpa only [map_mul, map_inv, huZ] using hz
      have eqt : (⟨u, huT⟩ : T) = t := hu ⟨u, huT⟩ hmem
      apply Subtype.ext
      exact huZ.symm.trans (congrArg (fun x : T => f x.1) eqt)

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
    apply (Fintype.existsUnique_iff_card_one (fun y : G => y ∈ T ∧ g⁻¹ * y ∈ H)).mpr
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using ht g
  obtain ⟨y, ⟨hy, hh⟩, hu⟩ := hu
  have inverse_mem (z : G) : z⁻¹ * g ∈ H ↔ g⁻¹ * z ∈ H := by
    simpa only [mul_inv_rev, inv_inv] using
      (H.inv_mem_iff : (z⁻¹ * g)⁻¹ ∈ H ↔ z⁻¹ * g ∈ H).symm
  refine ⟨⟨y, hy⟩, (inverse_mem y).mpr hh, ?_⟩
  intro z hz
  exact Subtype.ext (hu z.1 ⟨z.2, (inverse_mem z.1).mp hz⟩)

/-- The actual connection set supplies a transversal exactly according to
its identity membership: Y in case (a), and Y without 1 in case (b). -/
theorem transversal_cases [Finite G] (H : Subgroup G) (Y : Set G) (hY : NormalSubset Y)
    (hc : IsTotalPerfectCode (sumGraph Y hY) H) :
    ((1 : G) ∉ Y ∧ Subgroup.IsComplement Y (H : Set G)) ∨
      ((1 : G) ∈ Y ∧ Subgroup.IsComplement (Y \ {1}) (H : Set G)) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  obtain ⟨ho, ha | hb⟩ := (TotalPerfectCriterion.result H Y hY).mp hc
  · refine Or.inl ⟨?_, complement_of_card_one H Y ?_⟩
    · intro h1
      obtain ⟨z, _, hzs, hz⟩ := ha
      have hm : (1 : G) ∈ Y ∩ (H : Set G) := ⟨h1, H.one_mem⟩
      rw [hz] at hm
      have he : (1 : G) = z := Set.mem_singleton_iff.mp hm
      exact hzs ⟨1, H.one_mem, by simpa using he⟩
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
  · have h1 : (1 : G) ∈ Y ∧ (1 : G) ∈ H := hb.2 ⟨1, H.one_mem, by simp⟩
    refine Or.inr ⟨h1.1, complement_of_card_one H (Y \ {1}) ?_⟩
    intro g
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

/-- A total perfect subgroup code always has a normal left transversal.
In the two-element branch the identity must be removed from Y. -/
theorem result [Finite G] (H : Subgroup G) (Y : Set G) (hY : NormalSubset Y)
    (hc : IsTotalPerfectCode (sumGraph Y hY) H) : NLT H := by
  rcases transversal_cases H Y hY hc with ha | hb
  · exact ⟨Y, hY, ha.2⟩
  · exact ⟨Y \ {1}, normal_without_one Y hY, hb.2⟩

open scoped Classical in
/-- The total connection-set size is the subgroup index in case (a) and
one more than that index in case (b). The extra identity is counted, even
though self-neighbors are excluded by the graph. -/
theorem cardinal [Finite G] (H : Subgroup G) (Y : Set G) (hY : NormalSubset Y)
    (hc : IsTotalPerfectCode (sumGraph Y hY) H) :
    Nat.card Y = H.index + if (1 : G) ∈ Y then 1 else 0 := by
  classical
  rcases transversal_cases H Y hY hc with ha | hb
  · simpa only [if_neg ha.1, Nat.add_zero] using ha.2.card_left
  · rw [if_pos hb.1]
    have hi := hb.2.card_left
    let : Fintype G := Fintype.ofFinite G
    have hm : (1 : G) ∈ Finset.univ.filter (fun y : G => y ∈ Y) := by simp [hb.1]
    have he := Finset.card_erase_of_mem hm
    have hi' : (Finset.univ.filter (fun y : G => y ∈ Y)).card - 1 = H.index := by
      rw [← hi, Nat.card_eq_fintype_card, Fintype.card_subtype]
      rw [← he]
      congr 1
      ext y
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_diff, Set.mem_singleton_iff]
      tauto
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hp := Finset.card_pos.mpr ⟨1, hm⟩
    omega

#print axioms transversal_cases
#print axioms cardinal

#print axioms result
#print axioms restrict
#print axioms map

end D5.S3.Combinatorics.CayleySumCodes.NormalTransversal
