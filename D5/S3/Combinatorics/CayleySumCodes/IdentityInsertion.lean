/- GID: D5/S3/Combinatorics/CayleySumCodes/IdentityInsertion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CayleySumCodes/IdentityInsertion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Identity insertion preserves exponent-two subgroup codes with an exact graph-change boundary. -/

import D5.S3.Combinatorics.CayleySumCodes.TotalPerfectCriterion

set_option autoImplicit false

namespace D5.S3.Combinatorics.CayleySumCodes.IdentityInsertion

open D5.S3.Combinatorics.CayleySumCodes.TotalPerfectCriterion

variable {G : Type*} [Group G]

private theorem square_singleton_iff (H : Subgroup G) :
    squares H = {1} ↔ ∀ h ∈ H, h * h = 1 := by
  constructor
  · intro he h hh
    have hm : h * h ∈ squares H := ⟨h, hh, rfl⟩
    rw [he] at hm
    exact Set.mem_singleton_iff.mp hm
  · intro hs
    ext z
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact Set.mem_singleton_iff.mpr (hs h hh)
    · intro hz
      exact ⟨1, H.one_mem, by simpa using (Set.mem_singleton_iff.mp hz).symm⟩

private theorem normal_insert_one (Y : Set G) (hY : NormalSubset Y) :
    NormalSubset (insert 1 Y) := by
  intro a x hx
  rcases Set.mem_insert_iff.mp hx with hx | hx
  · subst x
    simp
  · exact Set.mem_insert_of_mem 1 (hY a x hx)

/-- If 1 was absent, inserting it gives the same simple graph precisely when
every element is an involution or the identity. Connection sets and graphs
therefore have different equality conditions. -/
theorem graph_eq_iff [Finite G] (Y : Set G) (hY : NormalSubset Y) (h1 : 1 ∉ Y) :
    sumGraph (insert 1 Y) (normal_insert_one Y hY) = sumGraph Y hY ↔
      ∀ g : G, g * g = 1 := by
  constructor
  · intro he g
    by_cases hg : g = g⁻¹
    · calc
        g * g = g * g⁻¹ := congrArg (fun x => g * x) hg
        _ = 1 := by simp
    · have hn : (sumGraph (insert 1 Y) (normal_insert_one Y hY)).Adj g g⁻¹ :=
        ⟨hg, by simp⟩
      have ho : (sumGraph Y hY).Adj g g⁻¹ := he ▸ hn
      exact False.elim (h1 (by simpa using ho.2))
  · intro hs
    ext g h
    change (g ≠ h ∧ g * h ∈ insert 1 Y) ↔ (g ≠ h ∧ g * h ∈ Y)
    constructor
    · rintro ⟨hne, hm⟩
      refine ⟨hne, ?_⟩
      rcases Set.mem_insert_iff.mp hm with hm | hm
      · apply False.elim
        apply hne
        calc
          g = g * (h * h) := by rw [hs h]; simp
          _ = (g * h) * h := (mul_assoc g h h).symm
          _ = h := by rw [hm, one_mul]
      · exact hm
    · exact fun he => ⟨he.1, Set.mem_insert_of_mem 1 he.2⟩

/-- Inserting or removing the identity preserves the exact subgroup's total
perfect-code property whenever its square set is the singleton {1}.
No restriction on squares of elements outside H is assumed. -/
theorem result [Finite G] (H : Subgroup G) (Y : Set G) (hY : NormalSubset Y)
    (hH : squares H = {1}) :
    IsTotalPerfectCode (sumGraph (insert 1 Y) (normal_insert_one Y hY)) H ↔
      IsTotalPerfectCode (sumGraph Y hY) H := by
  have hs := (square_singleton_iff H).mp hH
  have edges (g h : G) (hh : h ∈ H) :
      (sumGraph (insert 1 Y) (normal_insert_one Y hY)).Adj g h ↔
        (sumGraph Y hY).Adj g h := by
    constructor
    · rintro ⟨hne, hm⟩
      refine ⟨hne, ?_⟩
      rcases Set.mem_insert_iff.mp hm with hm | hm
      · apply False.elim
        apply hne
        calc
          g = g * (h * h) := by rw [hs h hh]; simp
          _ = (g * h) * h := (mul_assoc g h h).symm
          _ = h := by rw [hm, one_mul]
      · exact hm
    · exact fun he => ⟨he.1, Set.mem_insert_of_mem 1 he.2⟩
  unfold IsTotalPerfectCode
  apply forall_congr'
  intro g
  apply existsUnique_congr
  intro h
  exact and_congr_right (edges g h)

#print axioms graph_eq_iff
#print axioms result

end D5.S3.Combinatorics.CayleySumCodes.IdentityInsertion
