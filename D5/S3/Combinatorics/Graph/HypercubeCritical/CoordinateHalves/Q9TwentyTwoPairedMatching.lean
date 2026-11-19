import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoSingletonExclusion

/-! The three solid edges in the paired complete bipartite compression form a
matching on the degree-two vertices of the two compressed graphs. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoPairedMatching

open Finset SimpleGraph
open private SideHigh compressed compressed_degree from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointCompression
open private side_high_neighbors_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointTheta
open private cross_neighbor_iff_degree_two from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoCompression
open GirthSliceCounting (degreeThree)

private theorem model_min_degree : ∀ i : Fin 5, 2 ≤ (turanGraph 5 2).degree i := by
  decide +kernel

attribute [local instance] Classical.propDecidable

private theorem compressed_degree_two_of_crossing
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {L R : Finset V}
    (hp : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {x y}, G.Adj x y → G.degree x = 2 → G.degree y = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (iso : compressed G L ≃g turanGraph 5 2)
    {x : SideHigh G L} {y : SideHigh G R} (hxy : G.Adj x.val y.val) :
    (compressed G L).degree x = 2 := by
  have hmin : 2 ≤ (compressed G L).degree x := by
    rw [← iso.degree_eq x]
    exact model_min_degree (iso x)
  have hy : y.val ∈ degreeThree G (G.neighborFinset x.val) :=
    Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr hxy,
      (Finset.mem_filter.mp y.property).2⟩
  have hpos := Finset.card_pos.mpr ⟨y.val, hy⟩
  have h := compressed_degree hp hdeg (fun hxy hx hy => hlow hxy hx hy) hg x
  omega

/-- Every solid edge joins compressed-degree-two vertices. Those vertices
have a bijective matching across the two parity classes. -/
theorem paired_cross_matching
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {L R : Finset V}
    (hp : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {x y}, G.Adj x y → G.degree x = 2 → G.degree y = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (left : compressed G L ≃g turanGraph 5 2) (right : compressed G R ≃g turanGraph 5 2) :
    ∃ e : {x : SideHigh G L // (compressed G L).degree x = 2} ≃
        {y : SideHigh G R // (compressed G R).degree y = 2},
      ∀ x : SideHigh G L, ∀ y : SideHigh G R,
        G.Adj x.val y.val ↔ ∃ hx : (compressed G L).degree x = 2, (e ⟨x, hx⟩).val = y := by
  let X := {x : SideHigh G L // (compressed G L).degree x = 2}
  let Y := {y : SideHigh G R // (compressed G R).degree y = 2}
  have hx {x : SideHigh G L} {y : SideHigh G R} (hxy : G.Adj x.val y.val) :
      (compressed G L).degree x = 2 :=
    compressed_degree_two_of_crossing hp hdeg (fun hxy hx hy => hlow hxy hx hy) hg left hxy
  have hy {x : SideHigh G L} {y : SideHigh G R} (hxy : G.Adj x.val y.val) :
      (compressed G R).degree y = 2 :=
    compressed_degree_two_of_crossing hp.symm hdeg
      (fun hxy hx hy => hlow hxy hx hy) hg right hxy.symm
  have hl (x : X) : ∃! y : SideHigh G R, G.Adj x.val.val y.val :=
    (cross_neighbor_iff_degree_two hp hdeg (fun hxy hx hy => hlow hxy hx hy) hg x.val).mp x.property
  have hr (y : Y) : ∃! x : SideHigh G L, G.Adj y.val.val x.val :=
    (cross_neighbor_iff_degree_two hp.symm hdeg
      (fun hxy hx hy => hlow hxy hx hy) hg y.val).mp y.property
  let f (x : X) : Y := ⟨Classical.choose (hl x), hy (Classical.choose_spec (hl x)).1⟩
  let g (y : Y) : X := ⟨Classical.choose (hr y), hx (Classical.choose_spec (hr y)).1.symm⟩
  have hf (x : X) : G.Adj x.val.val (f x).val.val := (Classical.choose_spec (hl x)).1
  have hg' (y : Y) : G.Adj y.val.val (g y).val.val := (Classical.choose_spec (hr y)).1
  let e : X ≃ Y :=
    { toFun := f
      invFun := g
      left_inv := fun x => Subtype.ext ((hr (f x)).unique (hg' (f x)) (hf x).symm)
      right_inv := fun y => Subtype.ext ((hl (g y)).unique (hf (g y)) (hg' y).symm) }
  refine ⟨e, fun x y => ⟨fun h => ⟨hx h, (hl ⟨x, hx h⟩).unique (hf _) h⟩, ?_⟩⟩
  rintro ⟨hx, rfl⟩
  exact hf ⟨x, hx⟩

#print axioms paired_cross_matching

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoPairedMatching
