/- GID: D5/S3/FiniteGroups/FrobeniusCentralObstruction
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/FrobeniusCentralObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A nontrivial proper malnormal subgroup forces every central element to be one. -/

/-
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19389

admission_basis: escape-witness
Direct frozen dependencies: none.
Module escape_witness: central_eq_one_of_frobenius
Centrality places an element first in the malnormal subgroup and then in a trivial intersection with an outside conjugate.
central_eq_one_of_frobenius | proof_shape: content | escape_witness: central_eq_one_of_frobenius | consumer: BahturinCentronePereiraPeakGroups.BCP31.refutation_of_peak
-/

import Mathlib.Algebra.Group.Subgroup.Pointwise

namespace D5.S3.FiniteGroups.FrobeniusCentralObstruction

/-- A nontrivial proper subgroup with trivial intersections with its outside conjugates
excludes every nonidentity central element. -/
theorem central_eq_one_of_frobenius {G : Type*} [Group G] {H : Subgroup G}
    (hnebot : H ≠ ⊥) (hnetop : H ≠ ⊤)
    (hmal : ∀ g : G, g ∉ H → H ⊓ H.map (MulAut.conj g) = ⊥) {z : G}
    (hz : ∀ g : G, g * z = z * g) : z = 1 := by
  have hconj (g : G) : MulAut.conj g z = z := by
    change g * z * g⁻¹ = z
    rw [hz g, mul_inv_cancel_right]
  have hzH : z ∈ H := by
    by_contra hznot
    have hmap : H.map (MulAut.conj z) = H := by
      apply le_antisymm
      · rintro a ⟨b, hb, rfl⟩
        simpa [MulAut.conj_apply, ← hz b] using hb
      · intro a ha
        refine ⟨a, ha, ?_⟩
        simp [MulAut.conj_apply, ← hz a]
    have heq := hmal z hznot
    rw [hmap, inf_idem] at heq
    exact hnebot heq
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ H := by
    by_contra h
    apply hnetop
    exact top_unique (by intro a _; exact not_not.mp (not_exists.mp h a))
  have hzmap : z ∈ H.map (MulAut.conj g) := ⟨z, hzH, hconj g⟩
  have hzin : z ∈ H ⊓ H.map (MulAut.conj g) := ⟨hzH, hzmap⟩
  rw [hmal g hg] at hzin
  exact hzin

end D5.S3.FiniteGroups.FrobeniusCentralObstruction
