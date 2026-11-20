/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TwentyTwoPairedMatching
   generality: G
   mirror-B: none(waiver:covered-by-q9-twenty-two-paired-exclusion-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Matching]
   utility: none
   digest: Identify the perfect matching between the terminals of the paired compression. -/

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

private def hub (i : Fin 2) : Fin 5 := ⟨2 * i.val + 1, by omega⟩
private def terminal (i : Fin 3) : Fin 5 := ⟨2 * i.val, by omega⟩

private theorem model_degrees :
    (∀ i : Fin 2, (turanGraph 5 2).degree (hub i) = 3) ∧
    (∀ i : Fin 3, (turanGraph 5 2).degree (terminal i) = 2) := by
  decide +kernel

private theorem model_joins :
    ∀ (i : Fin 2) (x : Fin 5), (turanGraph 5 2).degree x = 2 →
      (turanGraph 5 2).Adj (hub i) x := by
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

/-- Order the two compressed hubs and the three matched vertices on each side
so that the actual crossing edges pair equal terminal indices. -/
theorem paired_model_labels
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {L R : Finset V}
    (hp : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {x y}, G.Adj x y → G.degree x = 2 → G.degree y = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (left : compressed G L ≃g turanGraph 5 2) (right : compressed G R ≃g turanGraph 5 2) :
    ∃ (u : Fin 2 ↪ SideHigh G L) (v : Fin 2 ↪ SideHigh G R)
      (x : Fin 3 ↪ SideHigh G L) (y : Fin 3 ↪ SideHigh G R),
      (∀ i, (compressed G L).degree (u i) = 3) ∧
      (∀ i, (compressed G R).degree (v i) = 3) ∧
      (∀ j, (compressed G L).degree (x j) = 2) ∧
      (∀ j, (compressed G R).degree (y j) = 2) ∧
      (∀ i j, (compressed G L).Adj (u i) (x j)) ∧
      (∀ i j, (compressed G R).Adj (v i) (y j)) ∧
      (∀ i j, G.Adj (x i).val (y j).val ↔ i = j) ∧
      (∀ i z, ¬ G.Adj (u i).val (z : SideHigh G R).val) ∧
      (∀ i z, ¬ G.Adj (z : SideHigh G L).val (v i).val) := by
  have hh : Function.Injective hub := by
    intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    change 2 * i.val + 1 = 2 * j.val + 1 at hv
    omega
  have ht : Function.Injective terminal := by
    intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    change 2 * i.val = 2 * j.val at hv
    omega
  obtain ⟨e, he⟩ := paired_cross_matching hp hdeg (fun hxy hx hy => hlow hxy hx hy) hg left right
  let u : Fin 2 ↪ SideHigh G L :=
    (⟨hub, hh⟩ : Fin 2 ↪ Fin 5).trans left.symm.toEquiv.toEmbedding
  let v : Fin 2 ↪ SideHigh G R :=
    (⟨hub, hh⟩ : Fin 2 ↪ Fin 5).trans right.symm.toEquiv.toEmbedding
  let x : Fin 3 ↪ SideHigh G L :=
    (⟨terminal, ht⟩ : Fin 3 ↪ Fin 5).trans left.symm.toEquiv.toEmbedding
  have hu (i : Fin 2) : (compressed G L).degree (u i) = 3 :=
    (left.symm.degree_eq (hub i)).trans (model_degrees.1 i)
  have hv (i : Fin 2) : (compressed G R).degree (v i) = 3 :=
    (right.symm.degree_eq (hub i)).trans (model_degrees.1 i)
  have hx (j : Fin 3) : (compressed G L).degree (x j) = 2 :=
    (left.symm.degree_eq (terminal j)).trans (model_degrees.2 j)
  let y : Fin 3 ↪ SideHigh G R := ⟨fun j => (e ⟨x j, hx j⟩).val,
    fun _ _ h => x.injective (congrArg Subtype.val (e.injective (Subtype.ext h)))⟩
  have hy (j : Fin 3) : (compressed G R).degree (y j) = 2 := (e ⟨x j, hx j⟩).property
  refine ⟨u, v, x, y, hu, hv, hx, hy, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    exact left.symm.map_rel_iff.mpr (model_joins i _ (model_degrees.2 j))
  · intro i j
    have hj : (turanGraph 5 2).degree (right (y j)) = 2 :=
      (right.degree_eq (y j)).trans (hy j)
    have h := right.symm.map_rel_iff.mpr (model_joins i (right (y j)) hj)
    change (compressed G R).Adj (right.symm (hub i)) (y j)
    simpa only [Equiv.apply_symm_apply, RelIso.symm_apply_apply] using h
  · intro i j
    constructor
    · intro h
      obtain ⟨_, hij⟩ := (he (x i) (y j)).mp h
      exact y.injective hij
    · rintro rfl
      exact (he (x i) (y i)).mpr ⟨hx i, rfl⟩
  · intro i z h
    obtain ⟨hh, _⟩ := (he (u i) z).mp h
    exact (by decide : (3 : Nat) ≠ 2) ((hu i).symm.trans hh)
  · intro i z h
    have hh := compressed_degree_two_of_crossing hp.symm hdeg
      (fun hxy hx hy => hlow hxy hx hy) hg right h.symm
    exact (by decide : (3 : Nat) ≠ 2) ((hv i).symm.trans hh)

#print axioms paired_model_labels

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoPairedMatching
