/- GID: D5/S3/Topology/StableCategory/TetrahedralOneSidedRefinement
   generality: I
   mirror-B: none(waiver:support-for-the-three-piece-categorical-cover)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A tetrahedral refinement accelerates a graph parameter against any simplicial complex. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Topology.StableCategory.TetrahedralGraphIteration

/-!
One ordinary tetrahedral refinement round for a graph and an arbitrary
finite complex. The extra components of the second colour give isolated
vertices in its parameter.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Topology.StableCategory.TetrahedralOneSidedRefinement

open D5.S3.Geometry.FiniteAlexanderDualCollapse (simplex)
open D5.S3.Geometry.FiniteSimplicialJoin (simplicialJoin)
open BarycentricGraphDistance (Face Vertex)
open BarycentricBaseRigidity (Contiguous sd)
open BarycentricNeighborhoodIteration (iteratedAmbient)
open OrdinaryCollarRetraction (colourComplex retract)
open OrdinaryCollarContiguity (collarComplex collar_inclusion_contiguous)
open OrdinaryCollarNaturality (pullback pullback_comparison retractMap retract_map_simplicial)
open OrdinaryContiguityLift (Simplicial comp_chains comp_image includeSubcomplex
  include_subcomplex_simplicial iterate_comp lift_iterates ofTotal of_total_simplicial subdivide)
open OrdinarySubdivisionMap (inTwoCutCollar_iterate_iff iterate)
open TetrahedronCollar16 (Color Extra hasColour mainComplex pocket_conditions)
open TetrahedralMainFactorization (extraComponent extra_retraction_contracts
  pullback_main_factorization refinedColour)
open DisjointContiguityGluing (glue_contiguity glue_simplicial parameterUnion parameterMap
  parameter_map_simplicial)
open TerminalCarrierIteration (selector_naturality)
open Relation (ReflTransGen)

open private image from D5.S3.Topology.OrdinarySubdivisionMap
open private collarVertex colour_inclusion_image forgetColour
  from D5.S3.Topology.StableCategory.OrdinaryCollarContiguity
open private restricted_image from D5.S3.Topology.StableCategory.OrdinaryCollarNaturality
open private left_projection_image from D5.S3.Topology.StableCategory.ColourGraphJoin
open private change_colour_labels left_rank_colour right_rank_colour
  from D5.S3.Topology.StableCategory.TetrahedralGraphIteration
open private main_le_collar extra_le_collar ExtraVertex extraGraph pieceIndex refinedPieceIndex
  refined_colour_face_in_one_piece refined_main refined_extra
  from D5.S3.Topology.StableCategory.TetrahedralMainFactorization
open private colourPiece glue toUnion to_union_simplicial
  from D5.S3.Topology.StableCategory.DisjointContiguityGluing
open private subdivide_simplicial from D5.S3.Topology.StableCategory.TerminalCarrierIteration

noncomputable section

local instance (priority := 2000) (X : Type*) : DecidableEq X := Classical.decEq X
attribute [local instance] Classical.propDecidable

private abbrev point : PreAbstractSimplicialComplex Unit := simplex {()}

private theorem point_vertex : ({()} : Finset Unit) ∈ point :=
  ⟨Finset.singleton_nonempty _, fun _ hv => hv⟩

private abbrev cone {U : Type} (G : PreAbstractSimplicialComplex U) :=
  simplicialJoin G point

private def coneRank {U : Type} (a : U → Fin 2) : U ⊕ Unit → Fin 4 :=
  ColourGraphJoin.joinRank a (fun _ => 0)

private theorem cone_rank_proper {U : Type} {G : PreAbstractSimplicialComplex U}
    (a : U → Fin 2) (ha : ∀ s ∈ G, Set.InjOn a (s : Set U)) :
    ∀ s ∈ cone G, Set.InjOn (coneRank a) (s : Set (U ⊕ Unit)) :=
  ColourGraphJoin.join_rank_proper a (fun _ : Unit => 0) ha
    (fun _ _ _ _ _ _ _ => Subsingleton.elim _ _)

private def foldToCone {X U : Type} (p : X → Bool) (l : X → U) : X → U ⊕ Unit :=
  ColourGraphJoin.joinMap p l (fun _ => ())

private theorem fold_image {X U : Type} {D : PreAbstractSimplicialComplex X}
    {G : PreAbstractSimplicialComplex U} (p : X → Bool) (l : X → U)
    (hl : ∀ s ∈ colourComplex D p, image s l ∈ G) :
    ∀ s ∈ D, image s (foldToCone p l) ∈ cone G := by
  apply ColourGraphJoin.join_map_image p l (fun _ => ()) hl
  intro s hs
  change s.image (fun _ => ()) ∈ point
  rw [Finset.image_const ((colourComplex D (fun x => !p x)).isRelLowerSet_faces hs).1 ()]
  exact point_vertex

private theorem fold_graph_colour {X U : Type}
    (p : X → Bool) (l : X → U) (a : U → Fin 2) :
    p = (hasColour 1 ∘ coneRank a) ∘ foldToCone p l := by
  rw [show hasColour 1 ∘ coneRank a =
      (ColourGraphJoin.leftColour : U ⊕ Unit → Bool) from left_rank_colour a (fun _ => 0)]
  funext x
  cases hx : p x <;> simp [foldToCone, ColourGraphJoin.joinMap, ColourGraphJoin.leftColour, hx]

private theorem fold_opposite_colour {X U : Type}
    (p : X → Bool) (l : X → U) (a : U → Fin 2) :
    (fun x => !p x) = (hasColour 0 ∘ coneRank a) ∘ foldToCone p l := by
  rw [show hasColour 0 ∘ coneRank a =
      (ColourGraphJoin.rightColour : U ⊕ Unit → Bool) from right_rank_colour a (fun _ => 0)]
  funext x
  cases hx : p x <;> simp [foldToCone, ColourGraphJoin.joinMap, ColourGraphJoin.rightColour, hx]

/-- The refinement colour read on the actual third subdivision of the source. -/
def refinedConeColour {X U : Type} {D : PreAbstractSimplicialComplex X}
    {G : PreAbstractSimplicialComplex U} (p : X → Bool) (l : X → U)
    (hl : ∀ s ∈ colourComplex D p, image s l ∈ G) (a : U → Fin 2) :
    (iteratedAmbient D 3).1 → Color :=
  refinedColour (foldToCone p l) (fold_image p l hl) (coneRank a)

theorem refined_cone_colour_complement {X U : Type} {D : PreAbstractSimplicialComplex X}
    {G : PreAbstractSimplicialComplex U} (p : X → Bool) (l : X → U)
    (hl : ∀ s ∈ colourComplex D p, image s l ∈ G) (a : U → Fin 2) :
    (fun v => decide (refinedConeColour p l hl a v = 0)) =
      (fun v => !(decide (refinedConeColour p l hl a v = 1))) := by
  funext v
  let c := refinedConeColour p l hl a v
  change decide (c = 0) = !(decide (c = 1))
  have hc : c = 0 ∨ c = 1 :=
    (Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp c.isLt)).imp Fin.ext Fin.ext
  rcases hc with hc | hc <;> simp [hc]

private theorem no_graph_extra {U : Type} {G : PreAbstractSimplicialComplex U}
    (a : U → Fin 2) (v : Face (iteratedAmbient (cone G) 2).2) :
    ¬ Extra 1 (RankColouredTetrahedron.row (coneRank a) v) := by
  intro h
  have hthree : (3 : Fin 4).val ∈ TetrahedronCollar16.carrier
      (RankColouredTetrahedron.row (coneRank a) v) := (pocket_conditions h).2.2
  obtain ⟨x, _, hx⟩ := (RankColouredTetrahedron.mem_carrier_row (coneRank a) v 3).mp hthree
  cases x with
  | inl u =>
    have hu := (a u).isLt
    have hval : (a u).val = 3 := congrArg Fin.val hx
    rw [hval] at hu
    exact (Nat.not_lt_of_ge (Nat.le_succ 2)) hu
  | inr u =>
    have hval : (2 : ℕ) = 3 := congrArg Fin.val hx
    exact (Nat.ne_of_lt (Nat.lt_succ_self 2)) hval

/-- Each index represents an extra component in the folded cone. Its
preimage can have several components, all with the same contraction. -/
abbrev ConeExtra {U : Type} (G : PreAbstractSimplicialComplex U) (a : U → Fin 2) :=
  (extraGraph (cone G) (coneRank a) 0).ConnectedComponent

/-- On the refined opposite colour, the absent tag denotes its main region. -/
def refinedOppositeTag {X U : Type} {D : PreAbstractSimplicialComplex X}
    {G : PreAbstractSimplicialComplex U} (p : X → Bool) (l : X → U)
    (hl : ∀ s ∈ colourComplex D p, image s l ∈ G) (a : U → Fin 2) :
    (iteratedAmbient D 3).1 → Option (ConeExtra G a) :=
  refinedPieceIndex (foldToCone p l) (fold_image p l hl) (coneRank a) 0

instance finiteConeExtra {U : Type} [Finite U]
    (G : PreAbstractSimplicialComplex U) (a : U → Fin 2) : Finite (ConeExtra G a) := by
  letI : Finite (Face (cone G)) := inferInstance
  letI : Finite (Face (sd (cone G))) := inferInstance
  letI : Finite (Face (sd (sd (cone G)))) := inferInstance
  letI : Finite (Face (iteratedAmbient (cone G) 2).2) :=
    inferInstanceAs (Finite (Face (sd (sd (cone G)))))
  letI : Finite (ExtraVertex (cone G) (coneRank a) 0) :=
    Finite.of_injective Subtype.val
      (Subtype.val_injective : Function.Injective
        (Subtype.val : ExtraVertex (cone G) (coneRank a) 0 → Face (sd (sd (cone G)))))
  change Finite (Quot (extraGraph (cone G) (coneRank a) 0).Reachable)
  exact Quot.finite _

abbrev OppositeVertexType {V E : Type} (H : PreAbstractSimplicialComplex V) :
    Option E → Type
  | none => (iteratedAmbient H 3).1
  | some _ => Unit

def oppositeFamily {V : Type} (H : PreAbstractSimplicialComplex V) (E : Type) :
    (j : Option E) → PreAbstractSimplicialComplex (OppositeVertexType H j)
  | none => (iteratedAmbient H 3).2
  | some _ => point

def oppositePostOn {V Z E : Type}
    {H : PreAbstractSimplicialComplex V} {L : PreAbstractSimplicialComplex Z}
    (h : V → Z) (hh : ∀ s ∈ H, image s h ∈ L)
    (atExtra : E → Vertex (iteratedAmbient L 3).2) :
    (j : Option E) → Vertex (oppositeFamily H E j) → Vertex (iteratedAmbient L 3).2
  | none => ofTotal (iterate h hh 3).val (iterate h hh 3).property
  | some e => fun _ => atExtra e

private theorem constant_simplicial {X Y : Type}
    {P : PreAbstractSimplicialComplex X} {Q : PreAbstractSimplicialComplex Y}
    (b : Vertex Q) : Simplicial (fun _ : Vertex P => b) := by
  intro s hs
  change s.attach.image (fun _ => b.val) ∈ Q
  rw [Finset.image_const (P.isRelLowerSet_faces hs).1.attach b.val]
  exact b.property

def initialAtThree {X Z : Type}
    {D : PreAbstractSimplicialComplex X} {L : PreAbstractSimplicialComplex Z}
    (i : X → Z) (hi : ∀ s ∈ D, image s i ∈ L)
    {P : PreAbstractSimplicialComplex (iteratedAmbient D 3).1}
    (hP : P ≤ (iteratedAmbient D 3).2) : Vertex P → Vertex (iteratedAmbient L 3).2 :=
  ofTotal (iterate i hi 3).val (fun s hs => (iterate i hi 3).property s (hP hs))

private theorem source_collar_factorization
    {X V Z : Type} [Finite X]
    {D : PreAbstractSimplicialComplex X} {H : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex Z}
    (i : X → Z) (hi : ∀ s ∈ D, image s i ∈ L) (q : X → Bool)
    (r : X → V) (hr : ∀ s ∈ colourComplex D q, image s r ∈ H)
    (h : V → Z) (hh : ∀ s ∈ H, image s h ∈ L)
    (old : ReflTransGen Contiguous
      (ofTotal (K := colourComplex D q) i (fun s hs => hi s hs.1))
      (ofTotal (h ∘ r) (comp_image r hr h hh))) :
    ReflTransGen Contiguous
      (initialAtThree i hi (P := collarComplex D q) (fun _ hs => hs.1))
      (ofTotal (iterate h hh 3).val (iterate h hh 3).property ∘
        ofTotal (iterate r hr 3).val (iterate r hr 3).property ∘ retractMap q) := by
  let C := collarComplex D q
  let L₃ := (iteratedAmbient L 3).2
  let i₃ := iterate i hi 3
  let inc := ofTotal i₃.val i₃.property
  let hiPart : ∀ s ∈ colourComplex D q, image s i ∈ L := fun s hs => hi s hs.1
  let subInc := ofTotal (iterate i hiPart 3).val (iterate i hiPart 3).property
  let hcomp := comp_image r hr h hh
  let subComp := ofTotal (iterate (h ∘ r) hcomp 3).val (iterate (h ∘ r) hcomp 3).property
  let r₃ := ofTotal (iterate r hr 3).val (iterate r hr 3).property
  let h₃ := ofTotal (iterate h hh 3).val (iterate h hh 3).property
  let idC : Vertex C → Vertex C := id
  have first := comp_chains idC inc (include_subcomplex_simplicial (le_refl C))
    (of_total_simplicial _ _) (collar_inclusion_contiguous (K := D) q)
  have firstEnd :
      (inc ∘ (fun v : Vertex C => BarycentricBaseRigidity.vertexOfFace (sd (sd D))
        ((forgetColour (K := D) q 3).val (retract q (collarVertex q v)))) ∘ idC) =
        subInc ∘ retractMap q := by
    funext v
    apply Subtype.ext
    exact congrFun (iterate_comp id (colour_inclusion_image (K := D) q) i hi 3).symm
      (retract q (collarVertex q v))
  rw [firstEnd] at first
  have second := comp_chains (retractMap q) (id : Vertex L₃ → Vertex L₃)
    (retract_map_simplicial q) (include_subcomplex_simplicial (le_refl L₃))
    (lift_iterates i (h ∘ r) hiPart hcomp old 3)
  have compEq : subComp = h₃ ∘ r₃ := by
    funext v
    apply Subtype.ext
    exact congrFun (iterate_comp r hr h hh 3) v.val
  have second' : ReflTransGen Contiguous (subInc ∘ retractMap q)
      (subComp ∘ retractMap q) := second
  rw [compEq] at second'
  exact first.trans second'

/-- Three ordinary subdivisions of the source and ambient give graph and
opposite-colour factors at parameter depths four and three. Every extra
piece is sent to an isolated parameter vertex whose ambient image comes
from the third subdivision of the graph. -/
theorem refine_graph_against_complex
    {X U V Z : Type} [Finite X] [Finite U] [Finite V]
    {D : PreAbstractSimplicialComplex X} {G : PreAbstractSimplicialComplex U}
    {H : PreAbstractSimplicialComplex V} {L : PreAbstractSimplicialComplex Z}
    (i : X → Z) (hi : ∀ s ∈ D, image s i ∈ L)
    (p : X → Bool) (l : X → U) (r : X → V)
    (hl : ∀ s ∈ colourComplex D p, image s l ∈ G)
    (hr : ∀ s ∈ colourComplex D (fun x => !p x), image s r ∈ H)
    (a : U → Fin 2) (ha : ∀ s ∈ G, Set.InjOn a (s : Set U))
    (g : U → Z) (h : V → Z) (hg : ∀ s ∈ G, image s g ∈ L)
    (hh : ∀ s ∈ H, image s h ∈ L) (left : Vertex G)
    (oldLeft : ReflTransGen Contiguous
      (ofTotal (K := colourComplex D p) i (fun s hs => hi s hs.1))
      (ofTotal (g ∘ l) (comp_image l hl g hg)))
    (oldRight : ReflTransGen Contiguous
      (ofTotal (K := colourComplex D (fun x => !p x)) i (fun s hs => hi s hs.1))
      (ofTotal (h ∘ r) (comp_image r hr h hh)))
    (selectG : Vertex (iteratedAmbient G 4).2 → Vertex (iteratedAmbient G 3).2)
    (memberG : ∀ v, (selectG v).val ∈ v.val.val) :
    let P := colourComplex (iteratedAmbient D 3).2
      (fun v => decide (refinedConeColour p l hl a v = 1))
    let Q := colourComplex (iteratedAmbient D 3).2
      (fun v => decide (refinedConeColour p l hl a v = 0))
    ∃ (factorG : Vertex P → Vertex (iteratedAmbient G 4).2)
      (factorH : Vertex Q → Vertex (parameterUnion (oppositeFamily H (ConeExtra G a))))
      (extraPoint : ConeExtra G a → Vertex (iteratedAmbient G 3).2),
      let atExtra := ofTotal (iterate g hg 3).val (iterate g hg 3).property ∘ extraPoint
      Simplicial factorG ∧ Simplicial factorH ∧
      Simplicial (parameterMap (oppositeFamily H (ConeExtra G a))
        (oppositePostOn h hh atExtra)) ∧
      (∀ v : Vertex Q, (factorH v).val.1 = refinedOppositeTag p l hl a v.val) ∧
      ReflTransGen Contiguous
        (initialAtThree i hi (P := P) (fun _ hs => hs.1))
        (ofTotal (iterate g hg 3).val (iterate g hg 3).property ∘ selectG ∘ factorG) ∧
      ReflTransGen Contiguous
        (initialAtThree i hi (P := Q) (fun _ hs => hs.1))
        (parameterMap (oppositeFamily H (ConeExtra G a)) (oppositePostOn h hh atExtra) ∘
          factorH) := by
  intro P Q
  let f := foldToCone p l
  let hf := fold_image p l hl
  let rank := coneRank a
  let J := cone G
  let L₃ := (iteratedAmbient L 3).2
  let D₃ := (iteratedAmbient D 3).2
  let proper : ∀ s ∈ J, Set.InjOn rank (s : Set (U ⊕ Unit)) := cone_rank_proper a ha
  let pl : U ⊕ Unit → U := Sum.elim id (fun _ => left.val)
  have hp : ∀ s ∈ colourComplex J (hasColour 1 ∘ rank), image s pl ∈ G := by
    change ∀ s ∈ colourComplex J (hasColour 1 ∘ coneRank a), image s pl ∈ G
    rw [show hasColour 1 ∘ coneRank a =
      (ColourGraphJoin.leftColour : U ⊕ Unit → Bool) from left_rank_colour a (fun _ => 0)]
    exact left_projection_image left.val
  have srcLeft : p = (hasColour 1 ∘ rank) ∘ f := fold_graph_colour p l a
  have srcRight : (fun x => !p x) = (hasColour 0 ∘ rank) ∘ f := fold_opposite_colour p l a
  have hgp := comp_image pl hp g hg
  have oldCone := change_colour_labels srcLeft i (g ∘ l) ((g ∘ pl) ∘ f) hi
    (comp_image l hl g hg)
    (comp_image f
      (restricted_image f hf ((hasColour 1 ∘ rank) ∘ f) (hasColour 1 ∘ rank) (fun _ => rfl))
      (g ∘ pl) hgp) (by
        intro x hx
        rw [← srcLeft] at hx
        simp [f, foldToCone, pl, ColourGraphJoin.joinMap, hx]) oldLeft

  have allMain : P = pullback D₃ (iterate f hf 3).val (mainComplex J rank 1) := by
    apply le_antisymm
    · intro s hs
      apply (refined_main f hf rank 1 s hs.1).2
      refine ⟨hs, fun v _ => ?_⟩
      have hn : ¬ Extra 1 (RankColouredTetrahedron.row rank ((iterate f hf 3).val v)) :=
        no_graph_extra (G := G) a ((iterate f hf 3).val v)
      simp only [refinedPieceIndex, pieceIndex, dite_eq_right hn]
    · intro s hs
      exact ((refined_main f hf rank 1 s hs.1).1 hs).1
  let intoMain := includeSubcomplex allMain.le
  have hIntoMain := include_subcomplex_simplicial allMain.le
  obtain ⟨tagSelect, tagFactor, tagMember, _, hTagFactor, graphChain⟩ :=
    pullback_main_factorization i hi f hf rank 1 (g ∘ pl) proper hgp oldCone
  -- The certificate factors through the tagged graph. Subdivide its
  -- projection to obtain an actual fourth-subdivision vertex of G.
  let projection := ofTotal (iterate pl hp 3).val (iterate pl hp 3).property
  have hProjection : Simplicial projection := of_total_simplicial _ _
  let graphPost := ofTotal (iterate g hg 3).val (iterate g hg 3).property
  have hGraphPost : Simplicial graphPost := of_total_simplicial _ _
  have graphPostEq :
      ofTotal (iterate (g ∘ pl) hgp 3).val (iterate (g ∘ pl) hgp 3).property =
        graphPost ∘ projection := by
    funext v
    apply Subtype.ext
    exact congrFun (iterate_comp pl hp g hg 3) v.val
  rw [graphPostEq] at graphChain
  have compareSelect := comp_chains tagFactor graphPost hTagFactor hGraphPost
    (ReflTransGen.single (selector_naturality projection hProjection
      tagSelect selectG tagMember memberG))
  let factorG := subdivide projection hProjection ∘ tagFactor ∘ intoMain
  have hFactorG : Simplicial factorG :=
    (subdivide_simplicial projection hProjection).comp (hTagFactor.comp hIntoMain)
  have hGraph : ReflTransGen Contiguous
      (initialAtThree i hi (P := P) (fun _ hs => hs.1))
      (graphPost ∘ selectG ∘ factorG) :=
    comp_chains intoMain (id : Vertex L₃ → Vertex L₃) hIntoMain
      (include_subcomplex_simplicial (le_refl L₃)) (graphChain.trans compareSelect)

  let E := ConeExtra G a
  letI : Finite E := finiteConeExtra G a
  letI : Fintype (Option E) := Fintype.ofFinite _
  let tag := refinedOppositeTag p l hl a
  let piece := colourPiece (P := Q) tag
  let family := oppositeFamily H E
  let initial := initialAtThree i hi (P := Q) (fun _ hs => hs.1)
  let inc (j : Option E) : Vertex (piece j) → Vertex L₃ :=
    fun v => initial ⟨v.val, v.property.1⟩
  have hface : ∀ s ∈ Q, ∃ j, ∀ v ∈ s, tag v = j :=
    refined_colour_face_in_one_piece f hf rank 0

  -- The folded labels detect membership in the source collar. Use the
  -- source retraction to recover the old factor into H.
  have mainToCollar : piece none ≤ collarComplex D (fun x => !p x) := by
    intro s hs
    have hmain : s ∈ pullback D₃ (iterate f hf 3).val (mainComplex J rank 0) :=
      (refined_main f hf rank 0 s hs.1.1).2
        ⟨hs.1, fun v hv => of_decide_eq_true (hs.2 v hv)⟩
    refine ⟨hmain.1, fun v hv => decide_eq_true ?_⟩
    have hcoll := main_le_collar rank 0 hmain.2
    have hv' : (iterate f hf 3).val v ∈ image s (iterate f hf 3).val :=
      Finset.mem_image.mpr ⟨v, hv, rfl⟩
    apply (inTwoCutCollar_iterate_iff f hf (fun x => !p x) (hasColour 0 ∘ rank)
      (fun x => (congrFun srcRight x).symm) v).mp
    exact of_decide_eq_true (hcoll.2 _ hv')
  let r₃ := ofTotal (iterate r hr 3).val (iterate r hr 3).property
  let h₃ := ofTotal (iterate h hh 3).val (iterate h hh 3).property
  let mainFactor : Vertex (piece none) → Vertex (iteratedAmbient H 3).2 :=
    r₃ ∘ retractMap (fun x => !p x) ∘ includeSubcomplex mainToCollar
  have hMainFactor : Simplicial mainFactor :=
    (of_total_simplicial _ _).comp
      ((retract_map_simplicial _).comp (include_subcomplex_simplicial mainToCollar))
  have hMain : ReflTransGen Contiguous (inc none) (h₃ ∘ mainFactor) :=
    comp_chains (includeSubcomplex mainToCollar) (id : Vertex L₃ → Vertex L₃)
      (include_subcomplex_simplicial mainToCollar) (include_subcomplex_simplicial (le_refl L₃))
      (source_collar_factorization i hi (fun x => !p x) r hr h hh oldRight)

  have extra (e : E) : ∃ b : Vertex (iteratedAmbient G 3).2,
      ReflTransGen Contiguous (inc (some e)) (fun _ => graphPost b) := by
    induction e using SimpleGraph.ConnectedComponent.ind with
    | h u =>
      let eu : ExtraVertex J rank 0 := ⟨u.val, u.property⟩
      have extraToPullback :
          piece (some ((extraGraph J rank 0).connectedComponentMk u)) ≤
            pullback D₃ (iterate f hf 3).val (extraComponent J rank 0 eu) := by
        intro s hs
        exact (refined_extra f hf rank 0 eu s hs.1.1).2
          ⟨hs.1, fun v hv => of_decide_eq_true (hs.2 v hv)⟩
      obtain ⟨b, contraction⟩ := extra_retraction_contracts rank 0 proper eu
      have chain := pullback_comparison i hi f hf (hasColour 1 ∘ rank) (g ∘ pl) hgp oldCone
        (extra_le_collar rank 0 eu) (fun _ => b) contraction
      dsimp only at chain
      rw [graphPostEq] at chain
      exact ⟨projection b,
        comp_chains (includeSubcomplex extraToPullback) (id : Vertex L₃ → Vertex L₃)
        (include_subcomplex_simplicial extraToPullback)
        (include_subcomplex_simplicial (le_refl L₃)) chain⟩
  choose extraPoint hExtra using extra

  let partFactor : (j : Option E) → Vertex (piece j) → Vertex (family j)
    | none => mainFactor
    | some _ => fun _ => ⟨(), point_vertex⟩
  let partPost := oppositePostOn h hh (graphPost ∘ extraPoint)
  have hPartFactor (j : Option E) : Simplicial (partFactor j) := by
    cases j with
    | none => exact hMainFactor
    | some e => exact constant_simplicial _
  have hPartPost (j : Option E) : Simplicial (partPost j) := by
    cases j with
    | none => exact of_total_simplicial (iterate h hh 3).val (iterate h hh 3).property
    | some e => exact constant_simplicial _
  have partChain (j : Option E) :
      ReflTransGen Contiguous (inc j) (partPost j ∘ partFactor j) := by
    cases j with
    | none => exact hMain
    | some e => exact hExtra e
  let factorH := glue tag (fun j => toUnion family j ∘ partFactor j)
  have hFactorH : Simplicial factorH := glue_simplicial tag hface _
    (fun j => (to_union_simplicial family j).comp (hPartFactor j))
  have hInitial : Simplicial initial := of_total_simplicial _ _
  have hInc (j : Option E) : Simplicial (inc j) := by
    have hle : piece j ≤ Q := fun _ hs => hs.1
    exact hInitial.comp (include_subcomplex_simplicial hle)
  have self_contiguous {S : PreAbstractSimplicialComplex (iteratedAmbient D 3).1}
      {k : Vertex S → Vertex L₃} (hk : Simplicial k) : Contiguous k k := by
    intro s hs
    rw [Finset.union_idempotent]
    exact hk s hs
  have hOpp := glue_contiguity tag hface inc (fun j => partPost j ∘ partFactor j)
    (fun j => self_contiguous (hInc j))
    (fun j => self_contiguous ((hPartPost j).comp (hPartFactor j))) partChain
  have hOpp' : ReflTransGen Contiguous initial (parameterMap family partPost ∘ factorH) := hOpp
  exact ⟨factorG, factorH, extraPoint, hFactorG, hFactorH,
    parameter_map_simplicial family partPost hPartPost, fun _ => rfl, hGraph, hOpp'⟩

end

end D5.S3.Topology.StableCategory.TetrahedralOneSidedRefinement
