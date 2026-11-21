/- GID: D5/S0/Certificates/Algebra/CappedUnionAlgebraicDavenport
   generality: G
   mirror-B: D5/B/S0/Certificates/Algebra/CappedUnionAlgebraicDavenport
   mirror-E: none(waiver:structural-proof)
   anchors: [lake/module/D5.S0.Certificates.Algebra.WangConjecture326Refutation]
   utility: none
   digest: Over every nonzero commutative ring the capped union monoid has algebraic Davenport constant one. -/

import D5.S0.Certificates.Algebra.CappedUnionDavenport
import D5.S0.Certificates.Algebra.WangConjecture326Refutation

/-! The ordinary semigroup algebra of the capped union monoid. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.Algebra.CappedUnionAlgebraicDavenport

/-
proof_shape:
  add_eq: bind-only (consumers: cyclic_le, cyclicIdempotent_eq, double_self_or_one,
    pair_vanish, result)
  double_self_or_one: bind-only (consumer: pair_vanish)
  zero_fold: bind-only (consumer: result)
  cyclic_le: content (consumer: cyclicIdempotent_eq)
  cyclicIdempotent_eq: content (consumers: pair_vanish, result)
  pair_vanish: content (consumer: result)
  result: content
escape_witness: the positive cyclic subsemigroup of x is {x, x + x}, so the cyclic idempotent
  is x + x; level-one pairs then share the single label (A u B, 2) in all four monomials, and
  every other factor vanishes at coefficient one.
admission_basis: escape-witness
-/

open D5.S0.Certificates.Algebra.CappedUnionDavenport
open D5.S0.Certificates.Algebra.WangConjecture326Refutation

variable {U : Type*} [DecidableEq U]

private theorem add_eq (x y : Capped U) :
    x + y = ⟨x.support ∪ y.support, ⟨min 2 (x.level.val + y.level.val), by omega⟩⟩ := rfl

/-- The positive cyclic subsemigroup of `x` is `{x, x + x}`. -/
private theorem cyclic_le (x : Capped U) : (cyclic x : Set (Capped U)) ⊆ {x, x + x} := by
  have hclosed : ∀ a ∈ ({x, x + x} : Set (Capped U)), ∀ b ∈ ({x, x + x} : Set (Capped U)),
      a + b ∈ ({x, x + x} : Set (Capped U)) := by
    intro a ha b hb
    right
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    · ext1
      · simp only [add_eq, Finset.union_idempotent]
      · apply Fin.ext; simp only [add_eq]; try omega
  let T : AddSubsemigroup (Capped U) := ⟨{x, x + x}, fun ha hb => hclosed _ ha _ hb⟩
  have : cyclic x ≤ T := AddSubsemigroup.closure_le.mpr (by simp [T])
  exact this

/-- The cyclic idempotent of `x` is `x + x`. -/
theorem cyclicIdempotent_eq (x : Capped U) : cyclicIdempotent x = x + x := by
  have hidem : (x + x) + (x + x) = x + x := by
    ext1
    · simp only [add_eq, Finset.union_idempotent]
    · apply Fin.ext; simp only [add_eq]; omega
  have hmem : x + x ∈ cyclic x :=
    (cyclic x).add_mem (AddSubsemigroup.subset_closure (by simp))
      (AddSubsemigroup.subset_closure (by simp))
  have hex : ∃ e, IsCyclicIdempotent x e := ⟨x + x, hmem, hidem⟩
  have hspec : IsCyclicIdempotent x (cyclicIdempotent x) := by
    simpa [cyclicIdempotent, hex] using hex.choose_spec
  rcases cyclic_le x hspec.1 with h | h
  · have he := hspec.2
    rw [h] at he ⊢
    exact he.symm
  · exact h


private theorem double_self_or_one (x : Capped U) : x + x = x ∨ (x.level : ℕ) = 1 := by
  by_cases h : (x.level : ℕ) = 1
  · exact Or.inr h
  · left
    ext1
    · simp only [add_eq, Finset.union_idempotent]
    · apply Fin.ext; simp only [add_eq]; have := x.level.isLt; omega

private theorem pair_vanish {R : Type*} [CommRing R] (x y : Capped U) :
    factor x (1 : R) * factor y 1 = 0 := by
  rcases double_self_or_one x with hx | hx
  · simp [factor, cyclicIdempotent_eq, hx]
  rcases double_self_or_one y with hy | hy
  · simp [factor, cyclicIdempotent_eq, hy]
  have h1 : x + y = x + (y + y) := by
    ext1
    · simp only [add_eq, Finset.union_idempotent]
    · apply Fin.ext; simp only [add_eq]; omega
  have h2 : x + y = (x + x) + y := by
    ext1
    · simp only [add_eq, Finset.union_idempotent]
    · apply Fin.ext; simp only [add_eq]; omega
  have h3 : x + y = (x + x) + (y + y) := by
    ext1
    · simp only [add_eq, Finset.union_idempotent]
    · apply Fin.ext; simp only [add_eq]; omega
  simp only [factor, cyclicIdempotent_eq, sub_mul, mul_sub,
    AddMonoidAlgebra.single_mul_single, mul_one, ← h1, ← h2, ← h3]
  abel

private theorem zero_fold {R : Type*} [CommRing R] (l : List (Capped U × ℕ)) :
    l.foldl (fun p xi => p * factor xi.1 (1 : R)) 0 = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simpa only [List.foldl_cons, zero_mul] using ih

/-- In `R[S_U]` the two-level differences multiply to zero, and the algebraic Davenport
constant of `S_U` is one exactly over the nonzero commutative rings. -/
theorem result (R : Type*) [CommRing R] :
    (∀ A B : Finset U,
      (AddMonoidAlgebra.single (⟨A, 1⟩ : Capped U) (1 : R) -
          AddMonoidAlgebra.single (⟨A, 2⟩ : Capped U) 1) *
        (AddMonoidAlgebra.single (⟨B, 1⟩ : Capped U) 1 -
          AddMonoidAlgebra.single (⟨B, 2⟩ : Capped U) 1) = 0) ∧
    (algebraicD (Capped U) R = 1 ↔ Nontrivial R) := by
  refine ⟨fun A B => ?_, ⟨fun h => ?_, fun hR => ?_⟩⟩
  · have hA : (⟨A, 2⟩ : Capped U) = ⟨A, 1⟩ + ⟨A, 1⟩ := by
      ext1
      · simp only [add_eq, Finset.union_idempotent]
      · rfl
    have hB : (⟨B, 2⟩ : Capped U) = ⟨B, 1⟩ + ⟨B, 1⟩ := by
      ext1
      · simp only [add_eq, Finset.union_idempotent]
      · rfl
    have := pair_vanish (R := R) (⟨A, 1⟩ : Capped U) ⟨B, 1⟩
    simpa only [factor, cyclicIdempotent_eq, ← hA, ← hB] using this
  · by_contra hn
    have : Subsingleton R := not_nontrivial_iff_subsingleton.mp hn
    have htop : algebraicD (Capped U) R = ⊤ := by
      refine ENat.eq_top_iff_forall_ge.mpr fun n => ?_
      have hg : GoodSequence (R := R) (List.replicate (n + 1) (⟨∅, 0⟩ : Capped U)) := by
        intro c hc
        exact absurd (Subsingleton.elim (c 0) 0) (hc 0 (by simp))
      have := le_iSup₂ (f := fun (l : List (Capped U)) (_ : GoodSequence (R := R) l) =>
        (l.length : ℕ∞)) _ hg
      simp only [List.length_replicate] at this
      exact le_trans (by exact_mod_cast Nat.le_succ n) this
    rw [htop] at h
    exact ENat.top_ne_one h
  · apply le_antisymm
    · refine iSup_le fun l => iSup_le fun hl => ?_
      have hlen : l.length ≤ 1 := by
        by_contra hlen
        obtain ⟨x, y, t, rfl⟩ : ∃ x y t, l = x :: y :: t := by
          cases l with
          | nil => simp at hlen
          | cons x t => cases t with
            | nil => simp at hlen
            | cons y t => exact ⟨x, y, t, rfl⟩
        apply hl (fun _ => 1) (fun _ _ => one_ne_zero)
        simpa [factorProduct, List.zipIdx_cons, pair_vanish, List.foldl_cons] using
          zero_fold (R := R) (t.zipIdx 1)
      exact_mod_cast hlen
    · let a : Capped U := ⟨∅, 1⟩
      have hgood : GoodSequence (R := R) [a] := by
        intro c _ h
        have h' := congrArg (fun p : AddMonoidAlgebra R (Capped U) => p.coeff a) h
        have hne : a + a ≠ a := by
          intro he
          have := congrArg (fun z : Capped U => (z.level : ℕ)) he
          simp only [add_eq, a] at this
          omega
        simp [factorProduct, factor, cyclicIdempotent_eq, AddMonoidAlgebra.coeff_sub,
          AddMonoidAlgebra.coeff_single, hne] at h'
      have := le_iSup₂ (f := fun (l : List (Capped U)) (_ : GoodSequence (R := R) l) =>
        (l.length : ℕ∞)) [a] hgood
      simpa [algebraicD] using this

#print axioms result

end D5.S0.Certificates.Algebra.CappedUnionAlgebraicDavenport
