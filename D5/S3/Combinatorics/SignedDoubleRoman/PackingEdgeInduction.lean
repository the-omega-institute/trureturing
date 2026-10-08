/- GID: D5/S3/Combinatorics/SignedDoubleRoman/PackingEdgeInduction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SignedDoubleRoman/PackingEdgeInduction
   mirror-E: none(waiver:ordinary-edge-induction)
   anchors: []
   utility: none
   digest: Nonobstructed domination-edge deletions lift six-for-two inductive packings. -/

import D5.S3.Combinatorics.SignedDoubleRoman.PackingEdge
import D5.S3.Combinatorics.SignedDoubleRoman.PackingInductionCore

set_option autoImplicit false

namespace D5.S3.Combinatorics.SignedDoubleRoman.PackingEdgeInduction

open Finset MixedDefs PackingEdge PackingInductionCore

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The local domination-edge conditions give an inductive lift if no colour clique is created. -/
theorem edge_case_regular (C D : SimpleGraph V)
    [DecidableRel C.Adj] [DecidableRel D.Adj] (S R : Finset V) (u v : V)
    (ih : ∀ T : Finset V, T.card < S.card →
      ∀ (C' D' : SimpleGraph V) [DecidableRel C'.Adj] [DecidableRel D'.Adj],
        Supported C' D' T → DegreeBound C' D' T → C'.CliqueFreeOn (T : Set V) 4 →
        ∃ X : Finset V, X ⊆ T ∧ MixedAdmissible C' D' X ∧ T.card ≤ 3 * X.card)
    (hsupport : Supported C D S) (hdegree : DegreeBound C D S)
    (hR : R ⊆ S) (huR : u ∈ R) (hvR : v ∈ R) (huv : u ≠ v) (hcard : R.card ≤ 6)
    (hc : C.IsIndepSet (({u, v} : Finset V) : Set V))
    (hb : ∀ x ∈ ({u, v} : Finset V), C.neighborFinset x ∪ D.neighborFinset x ⊆ R)
    (hl : ∀ x ∈ R, ((insert x (D.neighborFinset x)) ∩ ({u, v} : Finset V)).card ≤ 2 ∧
      (((insert x (D.neighborFinset x)) ∩ ({u, v} : Finset V)).card = 2 →
        D.neighborFinset x \ R = ∅) ∧ (D.neighborFinset x \ R).card ≤ 2)
    (hno : (ReducedColour C D R {u, v} (S \ R)).CliqueFreeOn ((S \ R : Finset V) : Set V) 4) :
    ∃ X : Finset V, X ⊆ S ∧ MixedAdmissible C D X ∧ S.card ≤ 3 * X.card := by
  classical
  have hQ : ({u, v} : Finset V) ⊆ R := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact huR
    · exact mem_singleton.mp hx ▸ hvR
  have hboundary : ∀ x ∈ ({u, v} : Finset V), ∀ y ∈ S \ R,
      ¬ C.Adj x y ∧ ¬ D.Adj x y := by
    intro x hx y hy
    have hyR := (mem_sdiff.mp hy).2
    constructor
    · intro h
      exact hyR (hb x hx (mem_union_left _ ((C.mem_neighborFinset _ _).mpr h)))
    · intro h
      exact hyR (hb x hx (mem_union_right _ ((D.mem_neighborFinset _ _).mpr h)))
  have hlocal : ∀ x ∈ R,
      ((insert x (D.neighborFinset x)) ∩ ({u, v} : Finset V)).card ≤ 2 ∧
      (((insert x (D.neighborFinset x)) ∩ ({u, v} : Finset V)).card = 2 →
        D.neighborFinset x ∩ (S \ R) = ∅) ∧
      (D.neighborFinset x ∩ (S \ R)).card ≤ 2 := by
    intro x hx
    have hh := hl x hx
    have hsub : D.neighborFinset x ∩ (S \ R) ⊆ D.neighborFinset x \ R := by
      intro y hy
      exact mem_sdiff.mpr ⟨(mem_inter.mp hy).1, (mem_sdiff.mp (mem_inter.mp hy).2).2⟩
    refine ⟨hh.1, ?_, (card_le_card hsub).trans hh.2.2⟩
    intro hq
    apply eq_empty_iff_forall_notMem.mpr
    intro y hy
    have hy' := hsub hy
    rw [hh.2.1 hq] at hy'
    exact notMem_empty _ hy'
  exact reduce C D S R {u, v} ih hR hQ ⟨u, huR⟩
    (by simpa [card_pair huv] using hcard) hsupport hdegree hc hboundary hlocal hno

/-- A triangle-free edge gives a six-vertex deletion when the residual graph has no obstruction. -/
theorem regular_no_triangle_case (C D : SimpleGraph V)
    [DecidableRel C.Adj] [DecidableRel D.Adj] (S : Finset V) (u v a b c d : V)
    (ih : ∀ T : Finset V, T.card < S.card →
      ∀ (C' D' : SimpleGraph V) [DecidableRel C'.Adj] [DecidableRel D'.Adj],
        Supported C' D' T → DegreeBound C' D' T → C'.CliqueFreeOn (T : Set V) 4 →
        ∃ X : Finset V, X ⊆ T ∧ MixedAdmissible C' D' X ∧ T.card ≤ 3 * X.card)
    (hsupport : Supported C D S) (hdegree : DegreeBound C D S)
    (hR : ({u, v, a, b, c, d} : Finset V) ⊆ S) (hdist : [u, v, a, b, c, d].Nodup)
    (hu : C.neighborFinset u ∪ D.neighborFinset u = {v, a, b})
    (hv : C.neighborFinset v ∪ D.neighborFinset v = {u, c, d}) (huv : D.Adj u v)
    (hno : (ReducedColour C D {u, v, a, b, c, d} {u, v}
      (S \ {u, v, a, b, c, d})).CliqueFreeOn
      ((S \ {u, v, a, b, c, d} : Finset V) : Set V) 4) :
    ∃ X : Finset V, X ⊆ S ∧ MixedAdmissible C D X ∧ S.card ≤ 3 * X.card := by
  obtain ⟨hcard, hc, hb, hl⟩ := no_triangle_reduction C D u v a b c d hdist
    (fun x hx => hdegree x (hR hx)) hu hv huv
  exact edge_case_regular C D S {u, v, a, b, c, d} u v ih hsupport hdegree hR
    (by simp) (by simp) huv.ne (by omega) hc hb hl hno

/-- A single triangle deletes its third vertex and that vertex's third neighbour as well. -/
theorem regular_one_triangle_case (C D : SimpleGraph V)
    [DecidableRel C.Adj] [DecidableRel D.Adj] (S : Finset V) (u v w a b c : V)
    (ih : ∀ T : Finset V, T.card < S.card →
      ∀ (C' D' : SimpleGraph V) [DecidableRel C'.Adj] [DecidableRel D'.Adj],
        Supported C' D' T → DegreeBound C' D' T → C'.CliqueFreeOn (T : Set V) 4 →
        ∃ X : Finset V, X ⊆ T ∧ MixedAdmissible C' D' X ∧ T.card ≤ 3 * X.card)
    (hsupport : Supported C D S) (hdegree : DegreeBound C D S)
    (hR : ({u, v, w, a, b, c} : Finset V) ⊆ S) (hdist : [u, v, w, a, b].Nodup)
    (hu : C.neighborFinset u ∪ D.neighborFinset u = {v, w, a})
    (hv : C.neighborFinset v ∪ D.neighborFinset v = {u, w, b})
    (hw : C.neighborFinset w ∪ D.neighborFinset w = {u, v, c}) (huv : D.Adj u v)
    (hno : (ReducedColour C D {u, v, w, a, b, c} {u, v}
      (S \ {u, v, w, a, b, c})).CliqueFreeOn
      ((S \ {u, v, w, a, b, c} : Finset V) : Set V) 4) :
    ∃ X : Finset V, X ⊆ S ∧ MixedAdmissible C D X ∧ S.card ≤ 3 * X.card := by
  obtain ⟨hcard, hc, hb, hl⟩ := one_triangle_reduction C D u v w a b c hdist
    (fun x hx => hdegree x (hR hx)) hu hv hw huv
  exact edge_case_regular C D S {u, v, w, a, b, c} u v ih hsupport hdegree hR
    (by simp) (by simp) huv.ne hcard hc hb hl hno

end D5.S3.Combinatorics.SignedDoubleRoman.PackingEdgeInduction
