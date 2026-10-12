/- GID: D5/S3/Combinatorics/EdgeLabeling/CubicARGraphUnion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/EdgeLabeling/CubicARGraphUnion
   mirror-E: none(waiver:helper-for-open-problem-resolution)
   anchors: []
   utility: none
   digest: A strict bound on bad vertex events gives an exact AR-labeling. -/

import D5.S3.Combinatorics.EdgeLabeling.CubicARGraphLabeling
import D5.S3.Combinatorics.EdgeLabeling.CubicARGraphMarkedEvents
import D5.S3.Combinatorics.EdgeLabeling.CubicARGraphArithmetic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.EdgeLabeling.CubicARGraphUnion

open D5.S3.Combinatorics.EdgeLabeling.CubicARGraphDefs
open D5.S3.Combinatorics.EdgeLabeling.CubicARGraphLabeling
open D5.S3.Combinatorics.EdgeLabeling.CubicARGraphMarkedEvents
open D5.S3.Combinatorics.EdgeLabeling.CubicARGraphCounting
open D5.S3.Combinatorics.EdgeLabeling.CubicARGraphArithmetic

/-- An outcome avoiding every incident additive triple yields an AR-labeling. -/
private theorem arGraph_of_avoiding_marked {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : 2 ≤ G.edgeFinset.card)
    (p q : G.edgeSet) (t : V → Fin 3 → G.edgeSet)
    (hinc : ∀ v, G.incidenceFinset v = Finset.univ.image (fun i => (t v i).val))
    (hdeg : ∀ v, G.degree v = 3)
    (e : MarkedLabeling G.edgeSet G.edgeFinset.card hm p q)
    (havoid : ∀ v, ¬ AdditiveTriple (markLabel e) (t v 0) (t v 1) (t v 2)) :
    IsARGraph G := by
  apply arGraph_of_edge_equiv G e.val hdeg
  intro v a ha b hb c hc hab hac hbc hsum
  rw [hinc v] at ha hb hc
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hc
  have hlabel (l : Fin 3) : edgeLabel G e.val (t v l).val = markLabel e (t v l) := by
    simp [edgeLabel, (t v l).property, markLabel]
  simp only [hlabel] at hsum
  have hswap : markLabel e (t v j) + markLabel e (t v i) = markLabel e (t v k) :=
    (Nat.add_comm _ _).trans hsum
  have hn := havoid v
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    first
    | exact hab rfl
    | exact hac rfl
    | exact hbc rfl
    | exact hn (Or.inl hsum)
    | exact hn (Or.inr (Or.inl hsum))
    | exact hn (Or.inr (Or.inr hsum))
    | exact hn (Or.inl hswap)
    | exact hn (Or.inr (Or.inl hswap))
    | exact hn (Or.inr (Or.inr hswap))

/-- A strict sum of bad-event cardinalities suffices for an exact interval labeling. -/
theorem arGraph_of_bad_sum_lt {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : 2 ≤ G.edgeFinset.card)
    (p q : G.edgeSet) (hpq : p ≠ q) (t : V → Fin 3 → G.edgeSet)
    (hinc : ∀ v, G.incidenceFinset v = Finset.univ.image (fun i => (t v i).val))
    (hdeg : ∀ v, G.degree v = 3)
    (hcount : (∑ v, Nat.card {e : MarkedLabeling G.edgeSet G.edgeFinset.card hm p q //
      AdditiveTriple (markLabel e) (t v 0) (t v 1) (t v 2)}) <
        Nat.factorial (G.edgeFinset.card - 2)) : IsARGraph G := by
  classical
  let bad (v : V) : Finset (MarkedLabeling G.edgeSet G.edgeFinset.card hm p q) :=
    Finset.univ.filter (fun e => AdditiveTriple (markLabel e) (t v 0) (t v 1) (t v 2))
  have hbad (v : V) : (bad v).card = Nat.card
      {e : MarkedLabeling G.edgeSet G.edgeFinset.card hm p q //
        AdditiveTriple (markLabel e) (t v 0) (t v 1) (t v 2)} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_of_subtype (bad v)]
    intro e
    simp [bad]
  have hedgecard : Fintype.card G.edgeSet = G.edgeFinset.card := by
    simp [SimpleGraph.edgeFinset]
  have hsample := card_markedLabeling G.edgeFinset.card hm p q hpq hedgecard
  have hstrict : (∑ v, (bad v).card) <
      Fintype.card (MarkedLabeling G.edgeSet G.edgeFinset.card hm p q) := by
    simpa [hbad, hsample] using hcount
  obtain ⟨e, he⟩ := exists_avoiding_of_sum_card_lt bad hstrict
  apply arGraph_of_avoiding_marked G hm p q t hinc hdeg e
  intro v hv
  exact he v (by simp [bad, hv])

/-- The three marked endpoints and all other vertices fit the strict factorial bound. -/
theorem sum_bad_card_lt {V : Type} [Fintype V] [DecidableEq V]
    (m : ℕ) (hm : 12 ≤ m) (hrel : 3 * Fintype.card V = 2 * m)
    (v u w : V) (hvu : v ≠ u) (hvw : v ≠ w) (huw : u ≠ w)
    (b : V → ℕ)
    (hv : b v ≤ Nat.factorial (m - 3))
    (hu : b u ≤ 2 * (m - 3) * Nat.factorial (m - 4))
    (hw : b w ≤ 2 * (m - 4) * Nat.factorial (m - 4))
    (hother : ∀ x, x ≠ v → x ≠ u → x ≠ w →
      b x ≤ 6 * (additivePairs m).card * Nat.factorial (m - 5)) :
    (∑ x, b x) < Nat.factorial (m - 2) := by
  let s : Finset V := {v, u, w}
  have hs : s.card = 3 := by simp [s, hvu, hvw, huw]
  have hsum : (∑ x ∈ s, b x) ≤ Nat.factorial (m - 3) +
      2 * (m - 3) * Nat.factorial (m - 4) +
      2 * (m - 4) * Nat.factorial (m - 4) := by
    simpa [s, hvu, hvw, huw, add_assoc] using Nat.add_le_add (Nat.add_le_add hv hu) hw
  have hrest : (∑ x ∈ sᶜ, b x) ≤
      (Fintype.card V - 3) * (6 * (additivePairs m).card * Nat.factorial (m - 5)) := by
    calc
      _ ≤ ∑ x ∈ sᶜ, 6 * (additivePairs m).card * Nat.factorial (m - 5) := by
        apply Finset.sum_le_sum
        intro x hx
        have hn : x ≠ v ∧ x ≠ u ∧ x ≠ w := by simpa [s] using hx
        exact hother x hn.1 hn.2.1 hn.2.2
      _ = _ := by simp [Finset.card_compl, hs]
  rw [← Finset.sum_add_sum_compl s b]
  apply lt_of_le_of_lt (Nat.add_le_add hsum hrest)
  have harith := bad_count_lt_factorial m (Fintype.card V) (additivePairs m).card hm hrel
    (four_mul_card_additivePairs_le m (by omega))
  have hsub : m - 3 + (m - 4) = 2 * m - 7 := by omega
  rw [← hsub] at harith
  convert harith using 1 <;> first | rfl | ring

end D5.S3.Combinatorics.EdgeLabeling.CubicARGraphUnion
