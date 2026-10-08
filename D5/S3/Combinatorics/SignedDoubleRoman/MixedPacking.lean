/- GID: D5/S3/Combinatorics/SignedDoubleRoman/MixedPacking
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SignedDoubleRoman/MixedPacking
   mirror-E: none(waiver:mixed-packing-induction)
   anchors: []
   utility: none
   digest: Every subcubic two-relation graph without a colour four-clique has a large packing. -/

import D5.S3.Combinatorics.SignedDoubleRoman.PackingBase
import D5.S3.Combinatorics.SignedDoubleRoman.PackingDiamondInduction
import D5.S3.Combinatorics.SignedDoubleRoman.PackingLowInduction
import D5.S3.Combinatorics.SignedDoubleRoman.PackingColour
import D5.S3.Combinatorics.SignedDoubleRoman.PackingCubicStructure
import D5.S3.Combinatorics.SignedDoubleRoman.PackingTriangleInduction
import D5.S3.Combinatorics.SignedDoubleRoman.PackingOneTriangle
import D5.S3.Combinatorics.SignedDoubleRoman.PackingNoTriangleInduction

set_option autoImplicit false

namespace D5.S3.Combinatorics.SignedDoubleRoman.MixedPacking

open Finset MixedDefs

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option maxHeartbeats 1000000 in
/-- The packing induction resolves every local configuration, including created colour cliques. -/
theorem large_mixed_packing (C D : SimpleGraph V)
    [DecidableRel C.Adj] [DecidableRel D.Adj] (S : Finset V)
    (hsupport : Supported C D S) (hdegree : DegreeBound C D S)
    (hno : C.CliqueFreeOn (S : Set V) 4) :
    ∃ X : Finset V, X ⊆ S ∧ MixedAdmissible C D X ∧ S.card ≤ 3 * X.card := by
  classical
  have hall : ∀ n : ℕ, ∀ S : Finset V, S.card = n →
      ∀ (C D : SimpleGraph V) [DecidableRel C.Adj] [DecidableRel D.Adj],
        Supported C D S → DegreeBound C D S → C.CliqueFreeOn (S : Set V) 4 →
        ∃ X : Finset V, X ⊆ S ∧ MixedAdmissible C D X ∧ S.card ≤ 3 * X.card := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n hrec =>
      intro S hn C D _ _ hsupport hdegree hno
      have ih : ∀ T : Finset V, T.card < S.card →
          ∀ (C' D' : SimpleGraph V) [DecidableRel C'.Adj] [DecidableRel D'.Adj],
            Supported C' D' T → DegreeBound C' D' T → C'.CliqueFreeOn (T : Set V) 4 →
            ∃ X : Finset V, X ⊆ T ∧ MixedAdmissible C' D' X ∧ T.card ≤ 3 * X.card := by
        intro T hT C' D' _ _ hs hd hk
        exact hrec T.card (by omega) T rfl C' D' hs hd hk
      by_cases hsmall : S.card ≤ 4
      · exact PackingBase.small_carrier C D S hsmall hno
      by_cases hA : ∃ p q r s u v : V, [p, q, r, s, u, v].Nodup ∧
          ({p, q, r, s, u, v} : Finset V) ⊆ S ∧
          C.Adj p r ∧ C.Adj p s ∧ C.Adj q r ∧ C.Adj q s ∧ C.Adj r s ∧
          (C.Adj u p ∨ D.Adj u p) ∧ (C.Adj u q ∨ D.Adj u q) ∧
          (C.Adj u v ∨ D.Adj u v)
      · obtain ⟨p, q, r, s, u, v, hdist, hR, hpr, hps, hqr, hqs, hrs, hup, huq, huv⟩ := hA
        exact PackingDiamondInduction.diamond_case C D S ih hsupport hdegree hno
          p q r s u v hdist hR hpr hps hqr hqs hrs hup huq huv
      by_cases hlow : ∃ u ∈ S, (C.neighborFinset u ∪ D.neighborFinset u).card ≤ 2
      · obtain ⟨u, hu, hlow⟩ := hlow
        exact PackingLowInduction.low_case C D S u ih hsupport hdegree hno hu hlow hA
      by_cases hD : D = ⊥
      · exact PackingColour.pure_colour_case C D S hdegree hno hD
      have hcubic := PackingCubicStructure.cubic_union C D S hdegree
        (fun u hu hlowu => hlow ⟨u, hu, hlowu⟩)
      obtain ⟨u, v, huv⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hD
      obtain ⟨huS, hvS⟩ := hsupport (Or.inr huv)
      have hN : ∀ x, C.neighborFinset x ∪ D.neighborFinset x ⊆ S := by
        intro x y hy
        simp only [mem_union, SimpleGraph.mem_neighborFinset] at hy
        exact (hsupport hy).2
      have hsym : ∀ x y, y ∈ C.neighborFinset x ∪ D.neighborFinset x →
          x ∈ C.neighborFinset y ∪ D.neighborFinset y := by
        intro x y hxy
        simp only [mem_union, SimpleGraph.mem_neighborFinset] at hxy ⊢
        exact hxy.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)
      rcases PackingCubicStructure.edge_triangle_cases C D u v
        (hcubic u huS).1 (hcubic v hvS).1 huv with htwo | hone | hzero
      · obtain ⟨w, z, hdist, hu, hv⟩ := htwo
        exact PackingTriangleInduction.double_triangle_case C D S ih hsupport hdegree hno
          u v w z hdist huS hvS (hN u (by rw [hu]; simp))
          (hN u (by rw [hu]; simp)) hu hv huv
      · obtain ⟨w, a, b, hdist, hu, hv⟩ := hone
        have hwS : w ∈ S := hN u (by rw [hu]; simp)
        have haS : a ∈ S := hN u (by rw [hu]; simp)
        have hbS : b ∈ S := hN v (by rw [hv]; simp)
        let Nw := C.neighborFinset w ∪ D.neighborFinset w
        have hpair : ({u, v} : Finset V) ⊆ Nw := by
          intro x hx
          simp only [mem_insert, mem_singleton] at hx
          rcases hx with hx | hx
          · subst x
            exact hsym u w (by rw [hu]; simp)
          · subst x
            exact hsym v w (by rw [hv]; simp)
        have hNwcard : Nw.card = 3 := (hcubic w hwS).1
        have hthird : (Nw \ ({u, v} : Finset V)).card = 1 := by
          rw [card_sdiff_of_subset hpair, hNwcard, card_pair huv.ne]
        obtain ⟨c, hthird⟩ := card_eq_one.mp hthird
        have hcN : c ∈ Nw := (mem_sdiff.mp (show c ∈ Nw \ {u, v} from by
          rw [hthird]; simp)).1
        have hcS : c ∈ S := hN w hcN
        have hw : Nw = {u, v, c} := by
          have hh := (sdiff_union_of_subset hpair).symm
          rw [hthird] at hh
          calc
            Nw = {c} ∪ {u, v} := hh
            _ = {u, v, c} := by
              ext x
              simp only [mem_union, mem_singleton, mem_insert]
              tauto
        have hR : ({u, v, w, a, b, c} : Finset V) ⊆ S := by
          intro x hx
          simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
          · exact huS
          · exact hvS
          · exact hwS
          · exact haS
          · exact hbS
          · exact hcS
        exact PackingOneTriangle.one_triangle_case C D S u v w a b c ih hsupport hdegree
          hno hR hdist hu hv hw huv hA
      · obtain ⟨a, b, c, d, hdist, hu, hv⟩ := hzero
        have hR : ({u, v, a, b, c, d} : Finset V) ⊆ S := by
          intro x hx
          simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
          · exact huS
          · exact hvS
          · exact hN u (by rw [hu]; simp)
          · exact hN u (by rw [hu]; simp)
          · exact hN v (by rw [hv]; simp)
          · exact hN v (by rw [hv]; simp)
        exact PackingNoTriangleInduction.no_triangle_case C D S ih hsupport hdegree hno
          hA u v a b c d hdist hR hu hv huv
  exact hall S.card S rfl C D hsupport hdegree hno

end D5.S3.Combinatorics.SignedDoubleRoman.MixedPacking
