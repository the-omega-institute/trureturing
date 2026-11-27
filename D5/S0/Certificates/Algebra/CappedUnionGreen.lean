/- GID: D5/S0/Certificates/Algebra/CappedUnionGreen
   generality: G
   mirror-B: D5/B/S0/Certificates/Algebra/CappedUnionGreen
   mirror-E: none(waiver:structural-proof)
   anchors: [lake/module/D5.S0.Certificates.Algebra.WangConjecture53Refutation]
   utility: none
   digest: In the capped union monoid principal ideals are coordinate up-sets, Green H is equality and every Schutzenberger group is trivial. -/

import D5.S0.Certificates.Algebra.CappedUnionDavenport
import D5.S0.Certificates.Algebra.WangConjecture326Refutation
import D5.S0.Certificates.Algebra.WangConjecture53Refutation

/-! Principal ideals and Green classes of the capped union monoid. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.Algebra.CappedUnionGreen

/-
proof_shape:
  add_eq: bind-only (consumer: below_iff)
  below_iff: content (consumer: result)
  result: content
escape_witness: (B, j) = (A, k) + (B, j - k) whenever A is contained in B and k <= j, while
  addition only enlarges supports and levels; hence principal ideals are coordinate up-sets,
  equal ideals force equal generators, every H-class is a singleton, and its translation group
  is the single map realized by the identity.
admission_basis: escape-witness
-/

open D5.S0.Certificates.Algebra.CappedUnionDavenport

variable {U : Type*} [DecidableEq U]

private theorem add_eq (x y : Capped U) :
    x + y = ⟨x.support ∪ y.support, ⟨min 2 (x.level.val + y.level.val), by omega⟩⟩ := rfl

/-- Membership in the principal ideal `{a} ∪ (a + S_U)`, in coordinates. -/
private theorem below_iff (x a : Capped U) :
    (x = a ∨ ∃ c, x = a + c) ↔ a.support ⊆ x.support ∧ (a.level : ℕ) ≤ x.level := by
  constructor
  · rintro (rfl | ⟨c, rfl⟩)
    · exact ⟨subset_rfl, le_rfl⟩
    · rw [add_eq]
      exact ⟨Finset.subset_union_left, by have := a.level.isLt; simp only; omega⟩
  · rintro ⟨hs, hl⟩
    right
    refine ⟨⟨x.support, ⟨x.level.val - a.level.val, by omega⟩⟩, ?_⟩
    ext1
    · rw [add_eq]; exact (Finset.union_eq_right.mpr hs).symm
    · apply Fin.ext; rw [add_eq]; have := x.level.isLt; simp only; omega

/-- The principal ideal of `(A, k)`, Green's relation `H` is equality, and every
Schützenberger translation group `Γ(H_a)` has exactly one element. -/
theorem result (a : Capped U) :
    WangConjecture326Refutation.principalIdeal a =
      {x | a.support ⊆ x.support ∧ (a.level : ℕ) ≤ x.level} ∧
    (∀ b : Capped U, WangConjecture53Refutation.Green a b ↔ a = b) ∧
    (∀ b : Capped U, (WangConjecture326Refutation.greenCon (Capped U)) a b ↔ a = b) ∧
    Nonempty (Unique (WangConjecture53Refutation.Gamma a)) := by
  have hgreen : ∀ b : Capped U, WangConjecture53Refutation.Green a b ↔ a = b := by
    intro b
    constructor
    · intro h
      have h1 := (below_iff a b).mp ((h a).mp (Or.inl rfl))
      have h2 := (below_iff b a).mp ((h b).mpr (Or.inl rfl))
      ext1
      · exact Finset.Subset.antisymm h2.1 h1.1
      · apply Fin.ext; omega
    · rintro rfl; exact fun _ => Iff.rfl
  refine ⟨?_, hgreen, ?_, ?_⟩
  · ext x
    exact below_iff x a
  · intro b
    change WangConjecture326Refutation.principalIdeal a =
      WangConjecture326Refutation.principalIdeal b ↔ a = b
    constructor
    · intro h
      have h1 : a ∈ WangConjecture326Refutation.principalIdeal b := h ▸ Or.inl rfl
      have h2 : b ∈ WangConjecture326Refutation.principalIdeal a := h.symm ▸ Or.inl rfl
      have h1' := (below_iff a b).mp h1
      have h2' := (below_iff b a).mp h2
      ext1
      · exact Finset.Subset.antisymm h2'.1 h1'.1
      · apply Fin.ext; omega
    · rintro rfl; rfl
  · have hsub : ∀ x y : WangConjecture53Refutation.HClass a, x = y := by
      intro x y
      apply Subtype.ext
      have hx : x.val = a := by
        have := (hgreen x.val).mp ?_
        · exact this.symm
        · intro z; exact (x.property z).symm
      have hy : y.val = a := by
        have := (hgreen y.val).mp ?_
        · exact this.symm
        · intro z; exact (y.property z).symm
      rw [hx, hy]
    refine ⟨{ default := ⟨id, ⟨0, fun x => (zero_add x.val).symm⟩⟩, uniq := ?_ }⟩
    intro f
    apply Subtype.ext
    funext x
    exact hsub _ _

#print axioms result

end D5.S0.Certificates.Algebra.CappedUnionGreen
