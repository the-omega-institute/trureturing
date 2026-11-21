/- GID: D5/S0/Certificates/Algebra/CappedUnionStructure
   generality: G
   mirror-B: D5/B/S0/Certificates/Algebra/CappedUnionStructure
   mirror-E: none(waiver:structural-proof)
   anchors: [lake/module/D5.S0.Certificates.Algebra.CappedUnionGreen]
   utility: none
   digest: The capped union monoid is periodic, its cyclic semigroups are groups exactly off level one, and its Wang invariants are explicit. -/

import D5.S0.Certificates.Algebra.CappedUnionAlgebraicDavenport
import D5.S0.Certificates.Algebra.CappedUnionGreen

/-! The structure theorem for the capped union monoid. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.Algebra.CappedUnionStructure

/-
proof_shape:
  add_eq: bind-only (consumer: result)
  result: content
escape_witness: the positive cyclic subsemigroup of a lies in {a, a + a}, which makes it finite;
  off level one a + a = a, so {a} is a group, while at level one neither a nor a + a fixes a,
  so no identity exists; the remaining clauses assemble the algebraic constant, Green relation,
  relative constants and translation groups already proved for the same monoid.
admission_basis: escape-witness
-/

open D5.S0.Certificates.Algebra.CappedUnionDavenport
open D5.S0.Certificates.Algebra.WangConjecture326Refutation

variable {U : Type*} [DecidableEq U]

private theorem add_eq (x y : Capped U) :
    x + y = ⟨x.support ∪ y.support, ⟨min 2 (x.level.val + y.level.val), by omega⟩⟩ := rfl

/-- For every set `U` and nonzero commutative ring `R`, the capped union monoid is periodic,
the positive cyclic semigroup of `(A, k)` is a group exactly when `k ≠ 1`, its algebraic
Davenport constant over `R` is one, Green `H` is equality, `D_(A,k) = |A| + k`, and every
Schützenberger translation group is trivial. -/
theorem result (R : Type*) [CommRing R] [Nontrivial R] :
    Periodic (Capped U) ∧
    (∀ a : Capped U, CyclicIsGroup a ↔ (a.level : ℕ) ≠ 1) ∧
    algebraicD (Capped U) R = 1 ∧
    (∀ a b : Capped U, (greenCon (Capped U)) a b ↔ a = b) ∧
    (∀ (A : Finset U) (k : Fin 3),
      IsGreatest (minimalLengths (⟨A, k⟩ : Capped U)) (A.card + k)) ∧
    (∀ a : Capped U, Nonempty (Unique (WangConjecture53Refutation.Gamma a))) := by
  refine ⟨fun a => ?_, fun a => ?_,
    (CappedUnionAlgebraicDavenport.result (U := U) R).2.mpr inferInstance,
    fun a b => (CappedUnionGreen.result a).2.2.1 b,
    CappedUnionDavenport.result,
    fun a => (CappedUnionGreen.result a).2.2.2⟩
  · exact (Set.toFinite ({a, a + a} : Set (Capped U))).subset
      (CappedUnionAlgebraicDavenport.cyclic_le a)
  · have ha : a ∈ cyclic a := AddSubsemigroup.subset_closure (by simp)
    constructor
    · rintro ⟨e, he, hid, -⟩ h1
      have hfix := hid a ha
      rcases CappedUnionAlgebraicDavenport.cyclic_le a he with rfl | rfl
      · have := congrArg (fun z : Capped U => (z.level : ℕ)) hfix
        simp only [add_eq] at this
        omega
      · have := congrArg (fun z : Capped U => (z.level : ℕ)) hfix
        simp only [add_eq] at this
        omega
    · intro h1
      have hdouble : a + a = a := by
        ext1
        · simp only [add_eq, Finset.union_idempotent]
        · apply Fin.ext; simp only [add_eq]; have := a.level.isLt; omega
      have hcyc : ∀ x ∈ cyclic a, x = a := by
        intro x hx
        rcases CappedUnionAlgebraicDavenport.cyclic_le a hx with rfl | rfl
        · rfl
        · exact hdouble
      refine ⟨a, ha, fun x hx => ?_, fun x hx => ⟨a, ha, ?_⟩⟩
      · rw [hcyc x hx, hdouble]
      · rw [hcyc x hx, hdouble]

#print axioms result

end D5.S0.Certificates.Algebra.CappedUnionStructure
