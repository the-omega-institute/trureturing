/- GID: D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisLexicographicFiberExtension
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/DagCompletion/SalinasSchmeisLexicographicFiberExtension
   mirror-E: none(waiver:pure-mathematical-argument)
   anchors: []
   utility: none
   digest: Partitions lexicographic extensions and lifts Noetherian subsets. -/

import D5.S3.ConceptDynamics.DagCompletion.SalinasSchmeisOmegaChainExtensionRefutation
import Mathlib.Data.Finset.Max
import Mathlib.Order.OrderIsoNat
import Mathlib.Order.Prod.Lex.Basic

/-! Induced extensions with a literal partition by lexicographic fibers. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DagCompletion.SalinasSchmeisLexicographicFiberExtension

open SalinasSchmeisOmegaChainExtensionRefutation (IsOmegaChain)

universe u v

variable {P : Type u} {A : Type v} [PartialOrder P] [PartialOrder A]

/-- The first-coordinate fiber, with the order induced from the lexicographic product. -/
def lexFiber (p : P) : Set (P ×ₗ A) :=
  {x | (ofLex x).1 = p}

/-- The second coordinate is the inverse of the inclusion into the inherited fiber. -/
def lexFiberOrderIso (p : P) : A ≃o lexFiber (A := A) p where
  toFun a := ⟨toLex (p, a), rfl⟩
  invFun x := (ofLex x.val).2
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    exact Prod.ext x.property.symm rfl
  map_rel_iff' {a b} := by
    change toLex (p, a) ≤ toLex (p, b) ↔ a ≤ b
    simp [Prod.Lex.toLex_le_toLex]

/-- Every natural-number section of a Noetherian subset is finite. Shifting past the
section maximum gives one strictly upward injection on the entire subset.
The linked escape-audit issue #28004 remains unfinished. The construction establishes the
order and injection laws, while a faithful registration still needs an enrolled readout and
lawful observational variation on the arbitrary Noetherian-subset telescope. -/
theorem lexNatFiberLifting (K : Set (P ×ₗ ℕ))
    (hK : ∀ C : Set (P ×ₗ ℕ), C ⊆ K → ¬ IsOmegaChain C) :
    let fiberSection (p : P) : Set ℕ := {n | toLex (p, n) ∈ K}
    ∃ offset : P → ℕ,
      (∀ p, (fiberSection p).Finite) ∧
      (∀ p, fiberSection p = ∅ → offset p = 0) ∧
      (∀ p, (fiberSection p).Nonempty →
        ∃ m, IsGreatest (fiberSection p) m ∧ offset p = 1 + m) ∧
      ∃ lift : K ↪ ({y : P ×ₗ ℕ | ∃ x ∈ K, x < y} \ K : Set (P ×ₗ ℕ)),
        ∀ x : K, x.val < (lift x).val ∧
          (lift x).val = toLex ((ofLex x.val).1, offset (ofLex x.val).1 + (ofLex x.val).2) := by
  classical
  dsimp only
  let fiberSection (p : P) : Set ℕ := {n | toLex (p, n) ∈ K}
  have finiteSection (p : P) : (fiberSection p).Finite := by
    by_contra h
    have : Infinite (fiberSection p) := Set.infinite_coe_iff.mpr h
    let intoFiber : ℕ ↪o (P ×ₗ ℕ) := (lexFiberOrderIso (A := ℕ) p).toOrderEmbedding.trans
      (OrderEmbedding.subtype (· ∈ lexFiber (A := ℕ) p))
    let chain : ℕ ↪o (P ×ₗ ℕ) := ((Nat.Subtype.orderIsoOfNat (fiberSection p)).toOrderEmbedding.trans
      (OrderEmbedding.subtype (· ∈ fiberSection p))).trans intoFiber
    refine hK (Set.range chain) ?_ ⟨OrderEmbedding.orderIso (f := chain)⟩
    rintro _ ⟨n, rfl⟩
    exact (Nat.Subtype.orderIsoOfNat (fiberSection p) n).property
  let offset (p : P) : ℕ :=
    if h : (fiberSection p).Nonempty then
      1 + (finiteSection p).toFinset.max' (by simpa using h)
    else 0
  have offsetAtMax (p : P) (h : (fiberSection p).Nonempty) :
      ∃ m, IsGreatest (fiberSection p) m ∧ offset p = 1 + m := by
    have h' : (finiteSection p).toFinset.Nonempty := by simpa using h
    refine ⟨_, ?_, dite_eq_left h⟩
    simpa using Finset.isGreatest_max' (finiteSection p).toFinset h'
  have belowOffset {p : P} {n : ℕ} (hn : n ∈ fiberSection p) : n < offset p := by
    obtain ⟨m, hm, heq⟩ := offsetAtMax p ⟨n, hn⟩
    rw [heq, Nat.add_comm 1]
    exact Nat.lt_succ_of_le (hm.2 hn)
  refine ⟨offset, finiteSection, ?_, offsetAtMax, ?_⟩
  · intro p h
    change fiberSection p = ∅ at h
    have hempty : ¬ (fiberSection p).Nonempty := by
      rw [h]
      exact Set.not_nonempty_empty
    exact dite_eq_right hempty
  · let shift (x : K) : P ×ₗ ℕ :=
      toLex ((ofLex x.val).1, offset (ofLex x.val).1 + (ofLex x.val).2)
    have above (x : K) : x.val < shift x :=
      Prod.Lex.lt_iff.mpr (Or.inr ⟨rfl,
        (belowOffset x.property).trans_le (Nat.le_add_right _ _)⟩)
    have outside (x : K) : shift x ∉ K := by
      intro hx
      exact (not_lt_of_ge (Nat.le_add_right _ _)) (belowOffset hx)
    let lift : K ↪ ({y : P ×ₗ ℕ | ∃ x ∈ K, x < y} \ K : Set (P ×ₗ ℕ)) :=
      ⟨fun x => ⟨shift x, ⟨⟨x.val, x.property, above x⟩, outside x⟩⟩, by
        rintro ⟨⟨p, n⟩, hp⟩ ⟨⟨q, k⟩, hq⟩ h
        have hpq : p = q := congrArg (fun y => (ofLex y.val).1) h
        subst q
        have hnk : offset p + n = offset p + k := congrArg (fun y => (ofLex y.val).2) h
        have hcoords : n = k := Nat.add_left_cancel hnk
        subst k
        rfl⟩
    exact ⟨lift, fun x => ⟨above x, rfl⟩⟩

end D5.S3.ConceptDynamics.DagCompletion.SalinasSchmeisLexicographicFiberExtension
