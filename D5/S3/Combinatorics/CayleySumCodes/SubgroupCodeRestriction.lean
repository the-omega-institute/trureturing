/- GID: D5/S3/Combinatorics/CayleySumCodes/SubgroupCodeRestriction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CayleySumCodes/SubgroupCodeRestriction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Perfect and total perfect codes restrict to every intermediate subgroup. -/
import D5.S3.Combinatorics.CayleySumCodes.PerfectCodeTransversal
import Mathlib.Combinatorics.SimpleGraph.Maps

/-! Source correspondence: Ma--Nikandish--Zhang original Theorem 2.7 and the
correction's inherited-code boundary, original scientific05 C13/C16. The proof
uses the induced graph directly, independently of either total-transversal
branch. It works for every intermediate subgroup, without subnormality or
normality of the code subgroup, and needs no finiteness assumption. The graph
remains loopless and the normal connection subset is restricted, not replaced
by a chosen transversal. This does not assert quotient total-code inheritance. -/
set_option autoImplicit false
namespace D5.S3.Combinatorics.CayleySumCodes.SubgroupCodeRestriction
open TotalPerfectCriterion PerfectCodeTransversal
variable {G : Type*} [Group G]

/-- The actual ambient connection subset intersected with the subgroup. -/
def connection (M : Subgroup G) (Y : Set G) : Set M := {x | (x : G) ∈ Y}

/-- Conjugation invariance restricts along the subgroup inclusion. -/
theorem normal (M : Subgroup G) (Y : Set G) (hY : NormalSubset Y) :
    NormalSubset (connection M Y) := by
  intro a x hx
  exact hY (a : G) (x : G) hx

/-- Restricting the connection set gives the actual induced simple graph. -/
theorem graph_induce (M : Subgroup G) (Y : Set G) (hY : NormalSubset Y) :
    sumGraph (connection M Y) (normal M Y hY) =
      (sumGraph Y hY).induce (M : Set G) := by
  ext x y
  change (x ≠ y ∧ (x : G)*(y : G) ∈ Y) ↔
    ((x : G) ≠ (y : G) ∧ (x : G)*(y : G) ∈ Y)
  constructor
  · rintro ⟨hne, hm⟩
    exact ⟨fun he => hne (Subtype.ext he), hm⟩
  · rintro ⟨hne, hm⟩
    exact ⟨fun he => hne (congrArg Subtype.val he), hm⟩

/-- Every total perfect subgroup code remains a total perfect code in each
intermediate subgroup, with precisely the induced connection and graph. -/
theorem total (H M : Subgroup G) (hHM : H ≤ M) (Y : Set G)
    (hY : NormalSubset Y) (hc : IsTotalPerfectCode (sumGraph Y hY) H) :
    IsTotalPerfectCode (sumGraph (connection M Y) (normal M Y hY))
      (H.comap M.subtype : Set M) := by
  intro x
  obtain ⟨h, ⟨hh, hadj⟩, hu⟩ := hc (x : G)
  refine ⟨⟨h, hHM hh⟩, ⟨hh, ?_⟩, ?_⟩
  · rw [graph_induce M Y hY]
    exact hadj
  · intro z hz
    apply Subtype.ext
    exact hu (z : G) ⟨hz.1, by
      have he := hz.2
      rw [graph_induce M Y hY] at he
      exact he⟩

/-- The same actual induced graph preserves perfect codes, with equality
allowed in the closed neighborhood. This is independent of the total case. -/
theorem perfect (H M : Subgroup G) (hHM : H ≤ M) (Y : Set G)
    (hY : NormalSubset Y) (hc : IsPerfectCode (sumGraph Y hY) H) :
    IsPerfectCode (sumGraph (connection M Y) (normal M Y hY))
      (H.comap M.subtype : Set M) := by
  intro x
  obtain ⟨h, ⟨hh, he | he⟩, hu⟩ := hc (x : G)
  · refine ⟨⟨h, hHM hh⟩, ⟨hh, Or.inl (Subtype.ext he)⟩, ?_⟩
    intro z hz
    apply Subtype.ext
    apply hu (z : G)
    refine ⟨hz.1, ?_⟩
    rcases hz.2 with hz | hz
    · exact Or.inl (congrArg Subtype.val hz)
    · rw [graph_induce M Y hY] at hz
      exact Or.inr hz
  · refine ⟨⟨h, hHM hh⟩, ⟨hh, Or.inr ?_⟩, ?_⟩
    · rw [graph_induce M Y hY]
      exact he
    · intro z hz
      apply Subtype.ext
      apply hu (z : G)
      refine ⟨hz.1, ?_⟩
      rcases hz.2 with hz | hz
      · exact Or.inl (congrArg Subtype.val hz)
      · rw [graph_induce M Y hY] at hz
        exact Or.inr hz

#print axioms total
#print axioms perfect
end D5.S3.Combinatorics.CayleySumCodes.SubgroupCodeRestriction
