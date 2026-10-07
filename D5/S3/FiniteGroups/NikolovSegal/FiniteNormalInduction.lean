/- GID: D5/S3/FiniteGroups/NikolovSegal/FiniteNormalInduction
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/FiniteNormalInduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Minimal normal subgroups and smaller quotients support finite-order induction. -/

import D5.S3.FiniteGroups.GaschutzFixed
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace NikolovSegal

universe u v
variable {G : Type u} {Q : Type v} [Group G] [Group Q]

/-- A finite nontrivial group has a nontrivial normal subgroup minimal among
nontrivial normal subgroups, using the published finite-order minimality API. -/
theorem exists_minimal_normal [Finite G] [Nontrivial G] :
    ∃ N : Subgroup G, Minimal (fun M : Subgroup G => M.Normal ∧ M ≠ ⊥) N := by
  apply (Set.toFinite {M : Subgroup G | M.Normal ∧ M ≠ ⊥}).exists_minimal
  exact ⟨⊤, inferInstance, top_ne_bot⟩

/-- Quotienting by any nontrivial normal subgroup strictly decreases group order. -/
theorem card_quotient_lt [Finite G] (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) :
    Nat.card (G ⧸ N) < Nat.card G := by
  have hNcard : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).2 hN
  have hpos : 0 < Nat.card (G ⧸ N) := Nat.card_pos
  have hmul : Nat.card (G ⧸ N) * Nat.card N = Nat.card G := N.index_mul_card
  nlinarith

/-- Coordinatewise lifts of two quotient-generating tuples generate modulo N. -/
theorem lift_tuple_generation (N : Subgroup G) [N.Normal] {d : ℕ}
    (x y : Fin d → G) (xq yq : Fin d → G ⧸ N)
    (hx : ∀ i, QuotientGroup.mk' N (x i) = xq i)
    (hy : ∀ i, QuotientGroup.mk' N (y i) = yq i)
    (hgen : Subgroup.closure (Set.range xq ∪ Set.range yq) = ⊤) :
    N ⊔ Subgroup.closure (Set.range x ∪ Set.range y) = ⊤ := by
  let q := QuotientGroup.mk' N
  let H := Subgroup.closure (Set.range x ∪ Set.range y)
  have himage : q '' (Set.range x ∪ Set.range y) = Set.range xq ∪ Set.range yq := by
    ext g
    constructor
    · rintro ⟨_, (⟨i, rfl⟩ | ⟨i, rfl⟩), rfl⟩
      · exact Or.inl ⟨i, (hx i).symm⟩
      · exact Or.inr ⟨i, (hy i).symm⟩
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨x i, Or.inl ⟨i, rfl⟩, hx i⟩
      · exact ⟨y i, Or.inr ⟨i, rfl⟩, hy i⟩
  have hmap : H.map q = ⊤ := by
    change (Subgroup.closure _).map q = ⊤
    rw [MonoidHom.map_closure, himage, hgen]
  have h := Subgroup.comap_map_eq q H
  rw [hmap, Subgroup.comap_top, QuotientGroup.ker_mk', sup_comm] at h
  exact h.symm

end NikolovSegal
