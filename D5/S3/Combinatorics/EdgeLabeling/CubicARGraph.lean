/- GID: D5/S3/Combinatorics/EdgeLabeling/CubicARGraph
   generality: G
   mirror-B: D5/B/S3/Combinatorics/EdgeLabeling/CubicARGraph
   mirror-E: none(waiver:open-problem-resolution)
   anchors: []
   utility: none
   digest: Cubic graphs admit edge labelings with distinct incident subset sums. -/

import D5.S3.Combinatorics.EdgeLabeling.CubicARGraphDefs
import D5.S3.Combinatorics.EdgeLabeling.CubicARGraphSmallIso
import D5.S3.Combinatorics.EdgeLabeling.CubicARGraphTransport
import D5.S3.Combinatorics.EdgeLabeling.CubicARGraphLarge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.EdgeLabeling.CubicARGraph

open D5.S3.Combinatorics.EdgeLabeling.CubicARGraphDefs
open D5.S3.Combinatorics.EdgeLabeling.CubicARGraphSmallIso
open D5.S3.Combinatorics.EdgeLabeling.CubicARGraphTransport

/-- Manattu–Lakshmanan's §7 question, answered positively. -/
def claim : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (∀ v, G.degree v = 3) → IsARGraph G

private def tableLabel {n : ℕ} (t : Fin n → Fin n → ℕ) : Sym2 (Fin n) → ℕ :=
  Sym2.lift ⟨fun x y => t (min x y) (max x y), by
    intro x y
    change t (min x y) (max x y) = t (min y x) (max y x)
    rw [min_comm, max_comm]⟩

private def fourLabel : Sym2 (Fin 4) → ℕ :=
  tableLabel ![![0,1,2,4], ![0,0,3,5], ![0,0,0,6], ![0,0,0,0]]

private def trianglesLabel : Sym2 (Fin 6) → ℕ :=
  tableLabel ![![0,0,0,1,2,4], ![0,0,0,3,5,6], ![0,0,0,7,8,9],
    ![0,0,0,0,0,0], ![0,0,0,0,0,0], ![0,0,0,0,0,0]]

private def cycleLabel : Sym2 (Fin 6) → ℕ :=
  tableLabel ![![0,0,1,4,2,0], ![0,0,0,8,6,9], ![0,0,0,0,3,5],
    ![0,0,0,0,0,7], ![0,0,0,0,0,0], ![0,0,0,0,0,0]]

private theorem ar_graph_of_finite_label_certificate {V : Type} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (f : Sym2 V → ℕ)
    (himage : G.edgeFinset.image f = Finset.Icc 1 G.edgeFinset.card)
    (hinj : Set.InjOn f G.edgeSet) (hdeg : ∀ v, G.degree v = 3)
    (hno : ∀ v, ∀ a ∈ G.incidenceFinset v, ∀ b ∈ G.incidenceFinset v,
      ∀ c ∈ G.incidenceFinset v, a ≠ b → a ≠ c → b ≠ c → f a + f b ≠ f c) :
    IsARGraph G := by
  have hmaps : Set.MapsTo f G.edgeSet (Set.Icc 1 G.edgeFinset.card) := by
    intro a ha
    have hm : f a ∈ G.edgeFinset.image f :=
      Finset.mem_image.mpr ⟨a, G.mem_edgeFinset.mpr ha, rfl⟩
    rw [himage] at hm
    simpa using hm
  refine ⟨f, ⟨hmaps, hinj, ?_⟩, ?_⟩
  · intro b hb
    have hm : b ∈ G.edgeFinset.image f := by rw [himage]; simpa using hb
    obtain ⟨a,ha,hab⟩ := Finset.mem_image.mp hm
    exact ⟨a, G.mem_edgeFinset.mp ha, hab⟩
  · intro v
    apply ar_vertex_of_no_additive_relation G f v (hdeg v)
    · intro a ha
      have he := G.incidenceSet_subset v ((G.mem_incidenceFinset v a).mp ha)
      exact Nat.lt_of_lt_of_le Nat.zero_lt_one (hmaps he).1
    · exact hinj.mono (by simpa using G.incidenceSet_subset v)
    · exact hno v

private theorem four_ar : IsARGraph modelFour := by
  apply ar_graph_of_finite_label_certificate modelFour fourLabel
  · decide
  · unfold Set.InjOn; decide
  · decide
  · decide

private theorem triangles_ar : IsARGraph modelSixTriangles := by
  apply ar_graph_of_finite_label_certificate modelSixTriangles trianglesLabel
  · decide
  · unfold Set.InjOn; decide
  · decide
  · decide

private theorem cycle_ar : IsARGraph modelSixCycle := by
  apply ar_graph_of_finite_label_certificate modelSixCycle cycleLabel
  · decide
  · unfold Set.InjOn; decide
  · decide
  · decide

private theorem small_ar {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hdeg : ∀ v, G.degree v = 3)
    (hcard : Fintype.card V = 4 ∨ Fintype.card V = 6) : IsARGraph G := by
  rcases hcard with h4 | h6
  · obtain ⟨q⟩ := cubic_four_iso G h4 hdeg
    exact ar_graph_of_iso G modelFour q four_ar
  · rcases cubic_six_iso G h6 hdeg with htri | hcyc
    · obtain ⟨q⟩ := htri
      exact ar_graph_of_iso G modelSixTriangles q triangles_ar
    · obtain ⟨q⟩ := hcyc
      exact ar_graph_of_iso G modelSixCycle q cycle_ar

private theorem empty_ar {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hcard : Fintype.card V = 0)
    (hdeg : ∀ v, G.degree v = 3) : IsARGraph G := by
  letI : IsEmpty V := Fintype.card_eq_zero_iff.mp hcard
  have hm : G.edgeFinset.card = 0 := by
    have h := cubic_card_identity G hdeg
    rw [hcard] at h
    omega

  refine ⟨fun _ => 0, ⟨?_, ?_, ?_⟩, fun v => isEmptyElim v⟩
  · intro s hs
    induction s using Sym2.ind with
    | _ a b => exact isEmptyElim a
  · intro s hs t ht h
    induction s using Sym2.ind with
    | _ a b => exact isEmptyElim a
  · intro n hn
    rw [hm] at hn
    have hlow := hn.1
    have hhigh := hn.2
    omega


theorem result : claim := by
  intro V instV instEq G instAdj hdeg
  by_cases hzero : Fintype.card V = 0
  · exact empty_ar G hzero hdeg
  by_cases hsmall : Fintype.card V = 4 ∨ Fintype.card V = 6
  · exact small_ar G hdeg hsmall
  have horder := cubic_order_constraints G hdeg (by omega)
  have hn : 8 ≤ Fintype.card V := by
    rcases horder.2 with ⟨k, hk⟩
    omega
  have hrel := cubic_card_identity G hdeg
  have hm12 : 12 ≤ G.edgeFinset.card := by omega
  exact D5.S3.Combinatorics.EdgeLabeling.CubicARGraphLarge.ar_graph_large G hdeg hm12

end D5.S3.Combinatorics.EdgeLabeling.CubicARGraph
