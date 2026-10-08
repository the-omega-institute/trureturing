/- GID: D5/S3/Combinatorics/SignedDoubleRoman/PackingTriangleInduction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SignedDoubleRoman/PackingTriangleInduction
   mirror-E: none(waiver:double-triangle-induction)
   anchors: []
   utility: none
   digest: A double domination triangle reduces the packing induction by six-for-two. -/

import D5.S3.Combinatorics.SignedDoubleRoman.PackingTriangles
import D5.S3.Combinatorics.SignedDoubleRoman.PackingInductionCore

set_option autoImplicit false

namespace D5.S3.Combinatorics.SignedDoubleRoman.PackingTriangleInduction

open Finset MixedDefs PackingTriangles PackingInductionCore

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Selecting both ends of a double-triangle domination edge needs no new pair. -/
theorem double_triangle_case (C D : SimpleGraph V)
    [DecidableRel C.Adj] [DecidableRel D.Adj] (S : Finset V)
    (ih : ∀ T : Finset V, T.card < S.card →
      ∀ (C' D' : SimpleGraph V) [DecidableRel C'.Adj] [DecidableRel D'.Adj],
        Supported C' D' T → DegreeBound C' D' T → C'.CliqueFreeOn (T : Set V) 4 →
        ∃ X : Finset V, X ⊆ T ∧ MixedAdmissible C' D' X ∧ T.card ≤ 3 * X.card)
    (hsupport : Supported C D S) (hdegree : DegreeBound C D S)
    (hno : C.CliqueFreeOn (S : Set V) 4) (u v w z : V) (hdist : [u, v, w, z].Nodup)
    (huS : u ∈ S) (hvS : v ∈ S) (hwS : w ∈ S) (hzS : z ∈ S)
    (hu : C.neighborFinset u ∪ D.neighborFinset u = {v, w, z})
    (hv : C.neighborFinset v ∪ D.neighborFinset v = {u, w, z})
    (huv : D.Adj u v) :
    ∃ X : Finset V, X ⊆ S ∧ MixedAdmissible C D X ∧ S.card ≤ 3 * X.card := by
  classical
  let R := ({u, v, w, z} : Finset V) ∪
    (C.neighborFinset w ∪ D.neighborFinset w) ∪
    (C.neighborFinset z ∪ D.neighborFinset z)
  let Q : Finset V := {u, v}
  have hR : R ⊆ S := by
    intro x hx
    simp only [R, mem_union, mem_insert, mem_singleton,
      SimpleGraph.mem_neighborFinset] at hx
    rcases hx with ((rfl | rfl | rfl | rfl) | h | h) | h | h
    · exact huS
    · exact hvS
    · exact hwS
    · exact hzS
    · exact (hsupport (Or.inl h)).2
    · exact (hsupport (Or.inr h)).2
    · exact (hsupport (Or.inl h)).2
    · exact (hsupport (Or.inr h)).2
  have hQ : Q ⊆ R := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · simp [R]
    · have hxv := mem_singleton.mp hx
      subst x
      simp [R]
  have hglobal : ∀ x, C.degree x + D.degree x ≤ 3 := by
    intro x
    by_cases hx : x ∈ S
    · exact hdegree x hx
    · have hC : C.neighborFinset x = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro y hy
        exact hx (hsupport (Or.inl ((C.mem_neighborFinset _ _).mp hy))).1
      have hD : D.neighborFinset x = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro y hy
        exact hx (hsupport (Or.inr ((D.mem_neighborFinset _ _).mp hy))).1
      change (C.neighborFinset x).card + (D.neighborFinset x).card ≤ 3
      simp [hC, hD]
  obtain ⟨hcount, hc, hb, hl⟩ := double_triangle_reduction C D u v w z
    hdist hglobal hu hv huv
  have hboundary : ∀ x ∈ Q, ∀ y ∈ S \ R, ¬ C.Adj x y ∧ ¬ D.Adj x y := by
    intro x hx y hy
    have hyR := (mem_sdiff.mp hy).2
    constructor
    · intro h
      exact hyR (hb x hx (mem_union_left _ ((C.mem_neighborFinset _ _).mpr h)))
    · intro h
      exact hyR (hb x hx (mem_union_right _ ((D.mem_neighborFinset _ _).mpr h)))
  have hlocal : ∀ x ∈ R, ((insert x (D.neighborFinset x)) ∩ Q).card +
      (D.neighborFinset x ∩ (S \ R)).card ≤ 2 := by
    intro x hx
    have hh := hl x hx
    change ((insert x (D.neighborFinset x)) ∩ Q).card +
      (D.neighborFinset x \ R).card ≤ 2 at hh
    have hsub : D.neighborFinset x ∩ (S \ R) ⊆ D.neighborFinset x \ R := by
      intro y hy
      exact mem_sdiff.mpr ⟨(mem_inter.mp hy).1, (mem_sdiff.mp (mem_inter.mp hy).2).2⟩
    have hle := card_le_card hsub
    omega
  apply clean_reduce C D S R Q ih hR hQ ⟨u, by simp [R]⟩ _
    hsupport hdegree hc hboundary hlocal hno
  have hQcard : Q.card = 2 := card_pair huv.ne
  change R.card ≤ 3 * Q.card
  change R.card ≤ 6 at hcount
  omega

end D5.S3.Combinatorics.SignedDoubleRoman.PackingTriangleInduction
