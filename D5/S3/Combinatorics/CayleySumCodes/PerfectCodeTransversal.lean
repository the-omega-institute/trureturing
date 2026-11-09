/- GID: D5/S3/Combinatorics/CayleySumCodes/PerfectCodeTransversal
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CayleySumCodes/PerfectCodeTransversal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Perfect subgroup codes and normalized normal transversals, with abelian existence. -/

import D5.S3.Combinatorics.CayleySumCodes.NormalTransversal

set_option autoImplicit false

namespace D5.S3.Combinatorics.CayleySumCodes.PerfectCodeTransversal

open D5.S3.Combinatorics.CayleySumCodes.TotalPerfectCriterion
open D5.S3.Combinatorics.CayleySumCodes.NormalTransversal

variable {G : Type*} [Group G]

/-- Exactly one member of C in each closed neighborhood, including the vertex
itself when it belongs to C. This differs from a total perfect code. -/
def IsPerfectCode (graph : SimpleGraph G) (C : Set G) : Prop :=
  ∀ g : G, ∃! h : G, h ∈ C ∧ (g = h ∨ graph.Adj g h)

private theorem inverse_mem (H : Subgroup G) (g t : G) :
    t⁻¹ * g ∈ H ↔ g⁻¹ * t ∈ H := by
  simpa only [mul_inv_rev, inv_inv] using
    (H.inv_mem_iff : (t⁻¹ * g)⁻¹ ∈ H ↔ t⁻¹ * g ∈ H).symm

private theorem normal_erase (T : Set G) (hn : NormalSubset T) :
    NormalSubset (T \ {1}) := by
  intro a x hx
  refine ⟨hn a x hx.1, ?_⟩
  intro he
  apply hx.2
  apply Set.mem_singleton_iff.mpr
  have hh := congrArg (fun z : G => a⁻¹ * z * a) (Set.mem_singleton_iff.mp he)
  simpa [mul_assoc] using hh

private theorem normal_normalize (Y : Set G) (hn : NormalSubset Y) :
    NormalSubset (insert 1 (Y \ {1})) := by
  intro a x hx
  rcases Set.mem_insert_iff.mp hx with hx | hx
  · subst x
    simp
  · exact Set.mem_insert_of_mem 1 (normal_erase Y hn a x hx)

private theorem transversal_inter (H : Subgroup G) (T : Set G)
    (hc : Subgroup.IsComplement T (H : Set G)) (h1 : 1 ∈ T)
    (t : G) (ht : t ∈ T) (hh : t ∈ H) : t = 1 := by
  obtain ⟨s, hs, hu⟩ := Subgroup.isComplement_iff_existsUnique_inv_mul_mem.mp hc 1
  have he := (hu ⟨t, ht⟩ (by simpa using H.inv_mem hh)).trans
    (hu ⟨1, h1⟩ (by simp)).symm
  exact congrArg Subtype.val he

/-- A specified identity-containing normal transversal gives a perfect code
after deleting the identity. This is an existential witness construction, not
an assertion that deleting 1 preserves an arbitrary sum graph. -/
theorem of_transversal (H : Subgroup G) (T : Set G) (hn : NormalSubset T)
    (hc : Subgroup.IsComplement T (H : Set G)) (h1 : 1 ∈ T) :
    IsPerfectCode (sumGraph (T \ {1}) (normal_erase T hn)) H := by
  intro g
  by_cases hg : g ∈ H
  · refine ⟨g, ⟨hg, Or.inl rfl⟩, ?_⟩
    rintro h ⟨hh, he | he⟩
    · exact he.symm
    · have eqone := transversal_inter H T hc h1 (g * h) he.2.1 (H.mul_mem hg hh)
      exact (he.2.2 (Set.mem_singleton_iff.mpr eqone)).elim
  · obtain ⟨t, ht, hu⟩ := Subgroup.isComplement_iff_existsUnique_inv_mul_mem.mp hc g
    have hH : g⁻¹ * t.1 ∈ H := (inverse_mem H g t.1).mp ht
    have hne : g ≠ g⁻¹ * t.1 := fun he => hg (he.symm ▸ hH)
    have tn : t.1 ≠ 1 := by
      intro he
      exact hg (by simpa [he] using ht)
    refine ⟨g⁻¹ * t.1, ⟨hH, Or.inr ⟨hne, ?_⟩⟩, ?_⟩
    · simpa using (show t.1 ∈ T \ {1} from ⟨t.2, tn⟩)
    · rintro h ⟨hh, he | he⟩
      · exact (hg (he.symm ▸ hh)).elim
      · have ht' : (g * h)⁻¹ * g ∈ H := by simpa [mul_assoc] using H.inv_mem hh
        have eqt := congrArg Subtype.val (hu ⟨g * h, he.2.1⟩ ht')
        calc
          h = g⁻¹ * (g * h) := by simp
          _ = g⁻¹ * t.1 := by rw [eqt]

/-- Every perfect subgroup code supplies a specified normal transversal
containing 1. The construction first removes 1 from Y and then inserts 1 as
the transversal's representative of H; it never assumes Y was disjoint H. -/
theorem normalized_transversal (H : Subgroup G) (Y : Set G) (hn : NormalSubset Y)
    (hc : IsPerfectCode (sumGraph Y hn) H) :
    Subgroup.IsComplement (insert 1 (Y \ {1})) (H : Set G) := by
  have internal (y : G) (hy : y ∈ Y) (hh : y ∈ H) : y = 1 := by
    by_contra he
    obtain ⟨h, hh', hu⟩ := hc 1
    have e1 : (1 : G) = h := hu 1 ⟨H.one_mem, Or.inl rfl⟩
    have ey : y = h := hu y ⟨hh, Or.inr ⟨Ne.symm he, by simpa using hy⟩⟩
    exact he (ey.trans e1.symm)
  apply Subgroup.isComplement_iff_existsUnique_inv_mul_mem.mpr
  intro g
  by_cases hg : g ∈ H
  · refine ⟨⟨1, Set.mem_insert 1 _⟩, by simpa using hg, ?_⟩
    intro t ht
    apply Subtype.ext
    rcases Set.mem_insert_iff.mp t.2 with he | he
    · exact he
    · have tm : t.1 ∈ H := by
        have heq : t.1 = g * (t.1⁻¹ * g)⁻¹ := by simp [mul_assoc]
        rw [heq]
        exact H.mul_mem hg (H.inv_mem ht)
      exact internal t.1 he.1 tm
  · obtain ⟨h, ⟨hh, he⟩, hu⟩ := hc g
    have edge : (sumGraph Y hn).Adj g h := he.resolve_left (fun he => hg (he.symm ▸ hh))
    have notone : g * h ≠ 1 := by
      intro he
      have geq : g = h⁻¹ := by
        have hh' := congrArg (fun z : G => z * h⁻¹) he
        simpa [mul_assoc] using hh'
      exact hg (geq.symm ▸ H.inv_mem hh)
    refine ⟨⟨g * h, Set.mem_insert_of_mem 1 ⟨edge.2, notone⟩⟩,
      by simpa [mul_assoc] using H.inv_mem hh, ?_⟩
    intro t ht
    have hty : t.1 ∈ Y := by
      rcases Set.mem_insert_iff.mp t.2 with he | he
      · exact (hg (by simpa [he] using ht)).elim
      · exact he.1
    have hH : g⁻¹ * t.1 ∈ H := (inverse_mem H g t.1).mp ht
    have hne : g ≠ g⁻¹ * t.1 := fun he => hg (he.symm ▸ hH)
    have eqh : g⁻¹ * t.1 = h := hu _ ⟨hH, Or.inr ⟨hne, by simpa using hty⟩⟩
    apply Subtype.ext
    calc
      t.1 = g * (g⁻¹ * t.1) := by simp
      _ = g * h := by rw [eqh]

/-- The normalized existential perfect-code criterion. The connection set
and graph may change when choosing the normalized witness. -/
theorem exists_iff (H : Subgroup G) :
    (∃ (Y : Set G) (hn : NormalSubset Y), IsPerfectCode (sumGraph Y hn) H) ↔
      ∃ T : Set G, NormalSubset T ∧ (1 : G) ∈ T ∧
        Subgroup.IsComplement T (H : Set G) := by
  constructor
  · rintro ⟨Y, hn, hc⟩
    exact ⟨insert 1 (Y \ {1}), normal_normalize Y hn, Set.mem_insert 1 _,
      normalized_transversal H Y hn hc⟩
  · rintro ⟨T, hn, h1, hc⟩
    exact ⟨T \ {1}, normal_erase T hn, of_transversal H T hn hc h1⟩

/-- Every subgroup of an abelian group has a perfect-code sum-graph witness.
The chosen transversal contains 1; its complement of {1} is the connection
set. No finite-group classification or total-code criterion is assumed. -/
theorem abelian_exists [IsMulCommutative G] (H : Subgroup G) :
    ∃ (Y : Set G) (hn : NormalSubset Y), IsPerfectCode (sumGraph Y hn) H := by
  obtain ⟨T, hc, h1⟩ := H.exists_isComplement_left 1
  have hn : NormalSubset T := by
    intro a x hx
    simpa [mul_comm a x, mul_assoc] using hx
  exact (exists_iff H).mpr ⟨T, hn, h1, hc⟩

#print axioms of_transversal
#print axioms normalized_transversal
#print axioms exists_iff
#print axioms abelian_exists

end D5.S3.Combinatorics.CayleySumCodes.PerfectCodeTransversal
