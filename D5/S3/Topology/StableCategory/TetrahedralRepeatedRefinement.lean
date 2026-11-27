/- GID: D5/S3/Topology/StableCategory/TetrahedralRepeatedRefinement
   generality: I
   mirror-B: none(waiver:support-for-the-tetrahedral-categorical-cover)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Iterated two-colour graph refinement preserves the original carriers. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Topology.StableCategory.TetrahedralGraphIteration

/-! Repeated tetrahedral refinement keeps the parameter maps inside the
original carriers while the parameters gain one subdivision per round. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Topology.StableCategory.TetrahedralRepeatedRefinement

open BarycentricGraphDistance (Face Vertex)
open BarycentricBaseRigidity (Contiguous faceImage retainedVertex sd skeleton)
open BarycentricNeighborhoodIteration (iteratedAmbient)
open OrdinaryCollarRetraction (colourComplex)
open OrdinaryContiguityLift (Simplicial comp_image ofTotal of_total_simplicial
  subdivide subdivide_of_total)
open OrdinarySubdivisionMap (iterate)
open TerminalCarrierIteration (CarrierPreserving SelectorStep chooseSelectorStep
  iteratedCarrierMap iteratedCarrierMap_preserves_carrier selector_preserves_carrier
  subdivision_connected selectorIterate selectorIterate_mem selectorIterate_carrier
  contraction_after_synchronous_subdivision)
open TetrahedralGraphIteration (refine_bicolour_graphs)
open GraphSubdivisionIntervals (originalSupport)
open D5.S3.Geometry.FiniteConeCollapse (faceSimplex)
open GeometricGraphTermination (supported_graph_map_contracts_of_homotopy)
open PathContiguity (intervalComplex)
open D5.S3.Geometry.FiniteSimplicialJoin (Space)
open OrdinaryContiguityLift (comp_chains)
open Relation (ReflTransGen)
open private image from D5.S3.Topology.OrdinarySubdivisionMap
open private mem_faceImage_iff from D5.S3.Topology.GraphSubdivisionIntervals
open private subdivide_simplicial from D5.S3.Topology.StableCategory.TerminalCarrierIteration

noncomputable section

local instance (priority := 2000) (X : Type*) : DecidableEq X := Classical.decEq X

open scoped Classical in
private def totalMap {X Y : Type} {A : PreAbstractSimplicialComplex X}
    {B : PreAbstractSimplicialComplex Y} (f : Vertex A → Vertex B) (fallback : Y) :
    X → Y :=
  fun x => if hx : {x} ∈ A then (f ⟨x, hx⟩).val else fallback

private theorem totalMap_image {X Y : Type} {A : PreAbstractSimplicialComplex X}
    {B : PreAbstractSimplicialComplex Y} (f : Vertex A → Vertex B) (hf : Simplicial f)
    (fallback : Y) : ∀ s ∈ A, image s (totalMap f fallback) ∈ B := by
  intro s hs
  have he : image s (totalMap f fallback) = BarycentricBaseRigidity.faceImage f hs := by
    ext y
    rw [image, Finset.mem_image, mem_faceImage_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hv := (A.isRelLowerSet_faces hs).2
        (Finset.singleton_subset_iff.mpr hx) (Finset.singleton_nonempty _)
      refine ⟨⟨x, hv⟩, hx, ?_⟩
      have hmem : ({x} : Finset X) ∈ A := hv
      simp [totalMap, hmem]
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v.val, hv, by simp [totalMap, v.property]⟩
  exact he.symm ▸ hf s hs

private theorem ofTotal_totalMap {X Y : Type} {A : PreAbstractSimplicialComplex X}
    {B : PreAbstractSimplicialComplex Y} (f : Vertex A → Vertex B) (hf : Simplicial f)
    (fallback : Y) :
    ofTotal (totalMap f fallback) (totalMap_image f hf fallback) = f := by
  funext v
  apply Subtype.ext
  change totalMap f fallback v.val = _
  simp [totalMap, v.property]

private theorem subdivide_eq {X Y : Type}
    {A : PreAbstractSimplicialComplex X} {B : PreAbstractSimplicialComplex Y}
    {f g : Vertex A → Vertex B} (hf : Simplicial f) (hg : Simplicial g) (h : f = g) :
    subdivide f hf = subdivide g hg := by
  subst g
  rfl

private theorem lift_carrier_ofTotal {X : Type} (A : PreAbstractSimplicialComplex X)
    (a c : ℕ) (f : (iteratedAmbient A a).1 → (iteratedAmbient A c).1)
    (hf : ∀ s ∈ (iteratedAmbient A a).2, image s f ∈ (iteratedAmbient A c).2)
    : (iteratedCarrierMap A a c (ofTotal f hf) (of_total_simplicial f hf) 3).1 =
      ofTotal (iterate f hf 3).val (iterate f hf 3).property := by
  have step (n : ℕ) :
      subdivide (ofTotal (iterate f hf n).val (iterate f hf n).property)
        (of_total_simplicial _ _) =
      ofTotal (iterate f hf (n + 1)).val (iterate f hf (n + 1)).property :=
    subdivide_of_total _ _
  let t := iteratedCarrierMap A a c (ofTotal f hf) (of_total_simplicial f hf)
  have h0 : (t 0).1 = ofTotal (iterate f hf 0).val (iterate f hf 0).property := rfl
  have h1 : (t 1).1 = ofTotal (iterate f hf 1).val (iterate f hf 1).property :=
    (subdivide_eq (t 0).2 _ h0).trans (step 0)
  have h2 : (t 2).1 = ofTotal (iterate f hf 2).val (iterate f hf 2).property :=
    (subdivide_eq (t 1).2 _ h1).trans (step 1)
  exact (subdivide_eq (t 2).2 _ h2).trans (step 2)

private theorem finite_at_depth {X : Type} [Finite X] (A : PreAbstractSimplicialComplex X)
    (n : ℕ) : Finite (iteratedAmbient A n).1 := by
  induction n with
  | zero => exact ‹Finite X›
  | succ n ih =>
    let := ih
    change Finite (Face (iteratedAmbient A n).2)
    infer_instance

private theorem rank_at_depth {X : Type} (A : PreAbstractSimplicialComplex X)
    (rank : X → Fin 2) (proper : ∀ s ∈ A, Set.InjOn rank (s : Set X)) (n : ℕ) :
    ∃ rank' : (iteratedAmbient A n).1 → Fin 2,
      ∀ s ∈ (iteratedAmbient A n).2, Set.InjOn rank' (s : Set (iteratedAmbient A n).1) := by
  induction n with
  | zero => exact ⟨rank, proper⟩
  | succ n ih =>
    obtain ⟨q, hq⟩ := ih
    exact (ColourGraphJoin.subdivision_rank_colouring (iteratedAmbient A n).2
      (fun s hs => by
        rw [← Finset.card_image_of_injOn (hq s hs)]
        exact (Finset.card_le_univ _).trans (by simp))).2


private structure ThroughCarrier {X Y U : Type}
    (D : PreAbstractSimplicialComplex X) (L : PreAbstractSimplicialComplex Y)
    (G : PreAbstractSimplicialComplex U) (a c : ℕ)
    (inc : Vertex D → Vertex L) (post : Vertex (iteratedAmbient G c).2 → Vertex L) where
  carrier : Vertex (iteratedAmbient G a).2 → Vertex (iteratedAmbient G c).2
  simplicialCarrier : Simplicial carrier
  support : CarrierPreserving G a c carrier
  factor : Vertex D → Vertex (iteratedAmbient G a).2
  simplicialFactor : Simplicial factor
  chain : ReflTransGen Contiguous inc (post ∘ carrier ∘ factor)

private def ThroughCarrier.totalFactor {X Y U : Type}
    {D : PreAbstractSimplicialComplex X} {L : PreAbstractSimplicialComplex Y}
    {G : PreAbstractSimplicialComplex U} {a c : ℕ} {inc : Vertex D → Vertex L}
    {post : Vertex (iteratedAmbient G c).2 → Vertex L}
    (F : ThroughCarrier D L G a c inc post) (anchor : Vertex (iteratedAmbient G a).2) :
    X → (iteratedAmbient G a).1 :=
  totalMap F.factor anchor.val

private def ambientStage {U Y : Type}
    {G : PreAbstractSimplicialComplex U} {L : PreAbstractSimplicialComplex Y}
    (g : U → Y) (hg : ∀ s ∈ G, image s g ∈ L) (r : ℕ) :=
  ofTotal (iterate g hg r).val (iterate g hg r).property

private def parameterPost {X Y U : Type}
    {D : PreAbstractSimplicialComplex X} {L : PreAbstractSimplicialComplex Y}
    {G : PreAbstractSimplicialComplex U} {a c : ℕ} {inc : Vertex D → Vertex (iteratedAmbient L c).2}
    {g : U → Y} {hg : ∀ s ∈ G, image s g ∈ L}
    (F : ThroughCarrier D (iteratedAmbient L c).2 G a c inc (ambientStage g hg c))
    (fallback : (iteratedAmbient G c).1) : (iteratedAmbient G a).1 → (iteratedAmbient L c).1 :=
  (iterate g hg c).val ∘ totalMap F.carrier fallback

private theorem parameterPost_image {X Y U : Type}
    {D : PreAbstractSimplicialComplex X} {L : PreAbstractSimplicialComplex Y}
    {G : PreAbstractSimplicialComplex U} {a c : ℕ} {inc : Vertex D → Vertex (iteratedAmbient L c).2}
    {g : U → Y} {hg : ∀ s ∈ G, image s g ∈ L}
    (F : ThroughCarrier D (iteratedAmbient L c).2 G a c inc (ambientStage g hg c))
    (fallback : (iteratedAmbient G c).1) :
    ∀ s ∈ (iteratedAmbient G a).2, image s (parameterPost F fallback) ∈ (iteratedAmbient L c).2 :=
  comp_image _ (totalMap_image F.carrier F.simplicialCarrier fallback) _ (iterate g hg c).property

private theorem parameterPost_lift {X Y U : Type}
    {D : PreAbstractSimplicialComplex X} {L : PreAbstractSimplicialComplex Y}
    {G : PreAbstractSimplicialComplex U} {a c : ℕ} {inc : Vertex D → Vertex (iteratedAmbient L c).2}
    {g : U → Y} {hg : ∀ s ∈ G, image s g ∈ L}
    (F : ThroughCarrier D (iteratedAmbient L c).2 G a c inc (ambientStage g hg c))
    (fallback : (iteratedAmbient G c).1) :
    let post := iterate (parameterPost F fallback) (parameterPost_image F fallback) 3
    ofTotal post.val post.property =
      ambientStage g hg (c + 3) ∘
        (iteratedCarrierMap G a c F.carrier F.simplicialCarrier 3).1 := by
  intro post
  let f := totalMap F.carrier fallback
  have hf := totalMap_image F.carrier F.simplicialCarrier fallback
  have lift_eq {u v : Vertex (iteratedAmbient G a).2 → Vertex (iteratedAmbient G c).2}
      (hu : Simplicial u) (hv : Simplicial v) (eq : u = v) :
      (iteratedCarrierMap G a c u hu 3).1 = (iteratedCarrierMap G a c v hv 3).1 := by
    subst v
    rfl
  have hLift := (lift_eq _ F.simplicialCarrier
    (ofTotal_totalMap F.carrier F.simplicialCarrier fallback)).symm.trans
      (lift_carrier_ofTotal G a c f hf)
  have hcomp := OrdinaryContiguityLift.iterate_comp f hf
    (iterate g hg c).val (iterate g hg c).property 3
  funext u
  apply Subtype.ext
  change post.val u.val = _
  rw [hLift]
  exact congrFun hcomp u.val

private def factorization_from_refinement {X Y U W : Type}
    {D : PreAbstractSimplicialComplex X} {L : PreAbstractSimplicialComplex Y}
    {G : PreAbstractSimplicialComplex U} {a c : ℕ}
    {inc : Vertex D → Vertex (iteratedAmbient L c).2}
    {g : U → Y} {hg : ∀ s ∈ G, image s g ∈ L}
    (F : ThroughCarrier D (iteratedAmbient L c).2 G a c inc (ambientStage g hg c))
    (fallback : (iteratedAmbient G c).1) (select : SelectorStep G (a + 3))
    {P : PreAbstractSimplicialComplex W} (i : Vertex P → Vertex (iteratedAmbient L (c + 3)).2)
    (factor : Vertex P → Vertex (iteratedAmbient G (a + 3 + 1)).2)
    (hf : Simplicial factor)
    (chain : let p := iterate (parameterPost F fallback) (parameterPost_image F fallback) 3
      ReflTransGen Contiguous i (ofTotal p.val p.property ∘ select.map ∘ factor)) :
    ThroughCarrier P (iteratedAmbient L (c + 3)).2 G (a + 4) (c + 3) i
      (ambientStage g hg (c + 3)) := by
  let lift := iteratedCarrierMap G a c F.carrier F.simplicialCarrier 3
  let carry := lift.1 ∘ select.map
  have hLift := iteratedCarrierMap_preserves_carrier G a c F.carrier
    F.simplicialCarrier F.support 3
  have hStep := selector_preserves_carrier G (a + 3) select.map select.member
  refine ⟨carry, lift.2.comp select.simplicial, CarrierPreserving.comp G hLift hStep,
    factor, hf, ?_⟩
  dsimp only at chain
  rw [parameterPost_lift F fallback] at chain
  exact chain

private theorem fin_two_cases (a : Fin 2) : a = 0 ∨ a = 1 :=
  (Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp a.isLt)).imp Fin.ext Fin.ext

private theorem complement_label {X : Type} (c : X → Fin 2) :
    (fun v => decide (c v = 0)) = (fun v => !(decide (c v = 1))) := by
  funext v
  have hv := fin_two_cases (c v)
  rcases hv with hv | hv <;> simp [hv]

private theorem throughCarrier_rounds
    {X Y U V : Type} [Finite X] [Finite U] [Finite V]
    {D : PreAbstractSimplicialComplex X} {L : PreAbstractSimplicialComplex Y}
    {G : PreAbstractSimplicialComplex U} {H : PreAbstractSimplicialComplex V}
    (i : X → Y) (hi : ∀ s ∈ D, image s i ∈ L)
    (g : U → Y) (hg : ∀ s ∈ G, image s g ∈ L)
    (h : V → Y) (hh : ∀ s ∈ H, image s h ∈ L)
    (rankG : U → Fin 2) (properG : ∀ s ∈ G, Set.InjOn rankG (s : Set U))
    (rankH : V → Fin 2) (properH : ∀ s ∈ H, Set.InjOn rankH (s : Set V))
    (anchorG : Vertex G) (anchorH : Vertex H)
    (connected : ∀ x y : Vertex L, (skeleton L).Reachable x y)
    (p : X → Bool)
    (left : ThroughCarrier (colourComplex D p) L G 0 0
      (ofTotal (K := colourComplex D p) i (fun s hs => hi s hs.1)) (ambientStage g hg 0))
    (right : ThroughCarrier (colourComplex D (fun x => !p x)) L H 0 0
      (ofTotal (K := colourComplex D (fun x => !p x)) i (fun s hs => hi s hs.1))
      (ambientStage h hh 0))
    (m : ℕ) :
    let A := (iteratedAmbient D (3 * m)).2
    let B := (iteratedAmbient L (3 * m)).2
    let inc := iterate i hi (3 * m)
    ∃ q : (iteratedAmbient D (3 * m)).1 → Bool,
      Nonempty (ThroughCarrier (colourComplex A q) B G (4 * m) (3 * m)
        (ofTotal (K := colourComplex A q) inc.val (fun s hs => inc.property s hs.1))
        (ambientStage g hg (3 * m))) ∧
      Nonempty (ThroughCarrier (colourComplex A (fun x => !q x)) B H (4 * m) (3 * m)
        (ofTotal (K := colourComplex A (fun x => !q x)) inc.val
          (fun s hs => inc.property s hs.1)) (ambientStage h hh (3 * m))) := by
  induction m with
  | zero => exact ⟨p, ⟨left⟩, ⟨right⟩⟩
  | succ m ih =>
    simp only [Nat.mul_succ]
    obtain ⟨q, ⟨F⟩, ⟨E⟩⟩ := ih
    let inc := iterate i hi (3 * m)
    let gl := retainedVertex (4 * m) anchorG
    let hr := retainedVertex (4 * m) anchorH
    let fg := (retainedVertex (3 * m) anchorG).val
    let fh := (retainedVertex (3 * m) anchorH).val
    obtain ⟨rg, hrg⟩ := rank_at_depth G rankG properG (4 * m)
    obtain ⟨rh, hrh⟩ := rank_at_depth H rankH properH (4 * m)
    let := finite_at_depth D (3 * m)
    let := finite_at_depth G (4 * m)
    let := finite_at_depth H (4 * m)
    let sg := chooseSelectorStep G (4 * m + 3)
    let sh := chooseSelectorStep H (4 * m + 3)
    have Fchain : ReflTransGen Contiguous
        (ofTotal (K := colourComplex (iteratedAmbient D (3 * m)).2 q)
          inc.val (fun s hs => inc.property s hs.1))
        (ofTotal (parameterPost F fg ∘ F.totalFactor gl) (comp_image _
          (totalMap_image F.factor F.simplicialFactor gl.val) _ (parameterPost_image F fg))) := by
      have eq : ofTotal (parameterPost F fg ∘ F.totalFactor gl) (comp_image _
          (totalMap_image F.factor F.simplicialFactor gl.val) _ (parameterPost_image F fg)) =
          ambientStage g hg (3 * m) ∘ F.carrier ∘ F.factor := by
        funext v
        apply Subtype.ext
        simp [parameterPost, ThroughCarrier.totalFactor, ambientStage, ofTotal, totalMap, v.property,
          (F.factor v).property]
      exact eq.symm ▸ F.chain
    have Echain : ReflTransGen Contiguous
        (ofTotal (K := colourComplex (iteratedAmbient D (3 * m)).2 (fun x => !q x))
          inc.val (fun s hs => inc.property s hs.1))
        (ofTotal (parameterPost E fh ∘ E.totalFactor hr) (comp_image _
          (totalMap_image E.factor E.simplicialFactor hr.val) _ (parameterPost_image E fh))) := by
      have eq : ofTotal (parameterPost E fh ∘ E.totalFactor hr) (comp_image _
          (totalMap_image E.factor E.simplicialFactor hr.val) _ (parameterPost_image E fh)) =
          ambientStage h hh (3 * m) ∘ E.carrier ∘ E.factor := by
        funext v
        apply Subtype.ext
        simp [parameterPost, ThroughCarrier.totalFactor, ambientStage, ofTotal, totalMap, v.property,
          (E.factor v).property]
      exact eq.symm ▸ E.chain
    obtain ⟨labels, l, r, hl, hr', cl, cr⟩ := refine_bicolour_graphs
      inc.val inc.property q (F.totalFactor gl) (E.totalFactor hr)
      (totalMap_image F.factor F.simplicialFactor gl.val)
      (totalMap_image E.factor E.simplicialFactor hr.val)
      rg rh hrg hrh (parameterPost F fg) (parameterPost E fh)
      (parameterPost_image F fg) (parameterPost_image E fh)
      gl hr Fchain Echain (subdivision_connected L connected (3 * m + 3))
      sg.map sh.map sg.member sh.member
    refine ⟨fun v => decide (labels v = 1), ?_, ?_⟩
    · exact ⟨factorization_from_refinement F fg sg _ l hl cl⟩
    · let q' : (iteratedAmbient D (3 * m + 3)).1 → Fin 2 := labels
      have transfer (p' : (iteratedAmbient D (3 * m + 3)).1 → Bool)
          (he : p' = fun v => decide (q' v = 0)) :
          Nonempty (ThroughCarrier (colourComplex (iteratedAmbient D (3 * m + 3)).2 p')
            _ H (4 * m + 4) (3 * m + 3) (ofTotal (iterate i hi (3 * m + 3)).val
              (fun s hs => (iterate i hi (3 * m + 3)).property s hs.1))
            (ambientStage h hh (3 * m + 3))) := by
        subst p'
        exact ⟨factorization_from_refinement E fh sh _ r hr' cr⟩
      exact transfer _ (complement_label q').symm

private theorem contract_factor {X U Y : Type} [Finite U]
    {D : PreAbstractSimplicialComplex X}
    (G : PreAbstractSimplicialComplex U) (L : PreAbstractSimplicialComplex Y)
    (orientRank : U → Fin 2) (proper : ∀ s ∈ G, Set.InjOn orientRank (s : Set U))
    (g : U → Y) (hg : ∀ s ∈ G, image s g ∈ L)
    (anchor : Vertex G)
    (m a c : ℕ) (ha : a = m + c)
    (d : ℕ) (hd : d ≤ m) (b : Vertex L)
    (contract : ∀ n, d ≤ n → ∀ select : Vertex (iteratedAmbient G n).2 → Vertex G,
      (∀ x, (select x).val ∈ originalSupport G n {x.val}) →
      ReflTransGen Contiguous (ofTotal g hg ∘ select) (fun _ => b))
    {inc : Vertex D → Vertex (iteratedAmbient L c).2}
    (F : ThroughCarrier D (iteratedAmbient L c).2 G a c inc (ambientStage g hg c)) :
    ReflTransGen Contiguous inc (fun _ => retainedVertex c b) := by
  subst a
  let q (u : U) := (orientRank u).val
  have hq (s : Finset U) (hs : s ∈ G) : s.image q ∈ intervalComplex 1 := by
    have bound : ∀ a ∈ s.image q, a ≤ 1 := by
      intro a ha
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp ha
      exact Nat.le_of_lt_succ (orientRank u).isLt
    exact ⟨(G.isRelLowerSet_faces hs).1.image _, bound, fun _ ha _ _ =>
      (bound _ ha).trans (Nat.succ_le_succ (Nat.zero_le _))⟩
  have hdim (s : Finset U) (hs : s ∈ G) : s.card ≤ 2 := by
    rw [← Finset.card_image_of_injOn (proper s hs)]
    exact (Finset.card_le_univ _).trans (by simp)
  let E := {e : Face G // e.val.val.card = 2}
  have orient (e : E) : ∃ x y : Vertex G,
      e.val.val = {x.val, y.val} ∧ x ≠ y ∧ q x.val = 0 ∧ q y.val = 1 := by
    let s := e.val.val
    have hcard : (s.image orientRank).card = 2 :=
      (Finset.card_image_of_injOn (proper s e.val.property)).trans e.property
    have hall : s.image orientRank = Finset.univ :=
      Finset.eq_univ_of_card _ (by simpa using hcard)
    obtain ⟨x, hx, hxq⟩ := Finset.mem_image.mp (show (0 : Fin 2) ∈ s.image orientRank by simp [hall])
    obtain ⟨y, hy, hyq⟩ := Finset.mem_image.mp (show (1 : Fin 2) ∈ s.image orientRank by simp [hall])
    have hn : x ≠ y := fun h => by
      subst y
      exact Nat.zero_ne_one (congrArg (fun a : Fin 2 => a.val) (hxq.symm.trans hyq))
    let L : Vertex G := ⟨x, (G.isRelLowerSet_faces e.val.property).2
      (Finset.singleton_subset_iff.mpr hx) (Finset.singleton_nonempty _)⟩
    let R : Vertex G := ⟨y, (G.isRelLowerSet_faces e.val.property).2
      (Finset.singleton_subset_iff.mpr hy) (Finset.singleton_nonempty _)⟩
    refine ⟨L, R, ?_, fun h => hn (congrArg Subtype.val h), congrArg Fin.val hxq,
      congrArg Fin.val hyq⟩
    symm
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.insert_subset_iff.mpr ⟨hx, Finset.singleton_subset_iff.mpr hy⟩
    · rw [Finset.card_insert_of_notMem (by simpa only [Finset.mem_singleton] using hn),
        Finset.card_singleton]
      exact e.property.le
  choose left right ho using orient
  let selectors := chooseSelectorStep G
  let sel := selectorIterate G selectors m
  let f := totalMap sel.1 anchor.val
  let hf := totalMap_image sel.1 sel.2 anchor.val
  have he : ofTotal f hf = sel.1 := ofTotal_totalMap sel.1 sel.2 anchor.val
  have supp : CarrierPreserving G m 0 (ofTotal f hf) := by
    rw [he]
    exact selectorIterate_carrier G selectors m
  have hc := contract m hd sel.1 (selectorIterate_mem G selectors m)
  have hs : ofTotal (g ∘ f) (comp_image f hf g hg) = ofTotal g hg ∘ sel.1 := by
    funext v
    exact Subtype.ext (congrArg (fun t : Vertex G => g t.val) (congrFun he v))
  rw [← hs] at hc
  have result := contraction_after_synchronous_subdivision G L hdim q hq left right ho
    m c g hg f hf supp b hc F.carrier F.simplicialCarrier F.support
  exact F.chain.trans (comp_chains F.factor id F.simplicialFactor
    (OrdinaryContiguityLift.include_subcomplex_simplicial le_rfl) result)

private def initial_factor {X U Y : Type}
    {D : PreAbstractSimplicialComplex X} {G : PreAbstractSimplicialComplex U}
    {L : PreAbstractSimplicialComplex Y} (i : X → Y) (l : X → U) (g : U → Y)
    (hi : ∀ s ∈ D, image s i ∈ L)
    (hl : ∀ s ∈ D, image s l ∈ G)
    (hg : ∀ s ∈ G, image s g ∈ L)
    (chain : ReflTransGen Contiguous (ofTotal i hi) (ofTotal (g ∘ l) (comp_image l hl g hg))) :
    ThroughCarrier D L G 0 0 (ofTotal i hi) (ambientStage g hg 0) :=
  ⟨id, OrdinaryContiguityLift.include_subcomplex_simplicial le_rfl,
    fun _ => Finset.Subset.rfl, ofTotal l hl, of_total_simplicial l hl, chain⟩

/-- A two-colour factorization through two nullhomotopic bipartite graph maps
yields two induced regions categorical in a common ordinary subdivision. -/
theorem eventually_contracts_bicolour
    {X Y U V : Type} [Finite X] [Fintype Y] [Fintype U] [Fintype V]
    {D : PreAbstractSimplicialComplex X} {L : PreAbstractSimplicialComplex Y}
    {G : PreAbstractSimplicialComplex U} {H : PreAbstractSimplicialComplex V}
    (i : X → Y) (hi : ∀ s ∈ D, image s i ∈ L)
    (p : X → Bool) (l : X → U) (r : X → V)
    (hl : ∀ s ∈ colourComplex D p, image s l ∈ G)
    (hr : ∀ s ∈ colourComplex D (fun x => !p x), image s r ∈ H)
    (rankG : U → Fin 2) (properG : ∀ s ∈ G, Set.InjOn rankG (s : Set U))
    (rankH : V → Fin 2) (properH : ∀ s ∈ H, Set.InjOn rankH (s : Set V))
    (anchorG : Vertex G) (anchorH : Vertex H)
    (g : U → Y) (hg : ∀ s ∈ G, image s g ∈ L)
    (h : V → Y) (hh : ∀ s ∈ H, image s h ∈ L)
    (left : ReflTransGen Contiguous
      (ofTotal (K := colourComplex D p) i (fun s hs => hi s hs.1))
      (ofTotal (g ∘ l) (comp_image l hl g hg)))
    (right : ReflTransGen Contiguous
      (ofTotal (K := colourComplex D (fun x => !p x)) i (fun s hs => hi s hs.1))
      (ofTotal (h ∘ r) (comp_image r hr h hh)))
    (connected : ∀ x y : Vertex L, (skeleton L).Reachable x y)
    (realG : C(Space G, Space L)) (realH : C(Space H, Space L))
    (supportG : ∀ s (hs : s ∈ G) (z : Space G), z.val ∈ faceSimplex s →
      (realG z).val ∈ faceSimplex (faceImage (ofTotal g hg) hs))
    (supportH : ∀ s (hs : s ∈ H) (z : Space H), z.val ∈ faceSimplex s →
      (realH z).val ∈ faceSimplex (faceImage (ofTotal h hh) hs))
    (qG qH : Space L)
    (nullG : realG.Homotopy (ContinuousMap.const (Space G) qG))
    (nullH : realH.Homotopy (ContinuousMap.const (Space H) qH)) :
    ∃ depth, let A := (iteratedAmbient D depth).2
      let B := (iteratedAmbient L depth).2
      let inc := iterate i hi depth
      ∃ label : (iteratedAmbient D depth).1 → Fin 2,
        ∀ j, ∃ b' : Vertex B,
          ReflTransGen Contiguous
            (ofTotal (K := colourComplex A (fun x => decide (label x = j)))
              inc.val (fun s hs => inc.property s hs.1)) (fun _ => b') := by
  have card_of_rank {T : Type} {P : PreAbstractSimplicialComplex T} (q : T → Fin 2)
      (hq : ∀ s ∈ P, Set.InjOn q (s : Set T)) (s : Finset T) (hs : s ∈ P) : s.card ≤ 2 := by
    rw [← Finset.card_image_of_injOn (hq s hs)]
    exact (Finset.card_le_univ _).trans (by simp)
  obtain ⟨bg, dg, cg⟩ := supported_graph_map_contracts_of_homotopy
    (card_of_rank rankG properG) (ofTotal g hg) (of_total_simplicial g hg)
    realG supportG qG nullG
  obtain ⟨bh, dh, ch⟩ := supported_graph_map_contracts_of_homotopy
    (card_of_rank rankH properH) (ofTotal h hh) (of_total_simplicial h hh)
    realH supportH qH nullH
  let m := max dg dh
  obtain ⟨colour, ⟨F⟩, ⟨E⟩⟩ := throughCarrier_rounds i hi g hg h hh
    rankG properG rankH properH anchorG anchorH connected p
    (initial_factor (D := colourComplex D p) i l g (fun s hs => hi s hs.1) hl hg left)
    (initial_factor (D := colourComplex D (fun x => !p x)) i r h (fun s hs => hi s hs.1) hr hh right) m
  have he : 4 * m = m + 3 * m := by
    simpa only [Nat.one_mul] using (Nat.add_mul 1 3 m)
  have hlc := contract_factor G L rankG properG g hg anchorG m _ _ he dg (le_max_left _ _) bg cg F
  have hrc := contract_factor H L rankH properH h hh anchorH m _ _ he dh (le_max_right _ _) bh ch E
  let label x : Fin 2 := if colour x then 1 else 0
  refine ⟨3 * m, label, ?_⟩
  have eq1 : (fun x => decide (label x = 1)) = colour := by
    funext x
    cases h : colour x <;> simp [label, h]
  have eq0 : (fun x => decide (label x = 0)) = (fun x => !colour x) := by
    exact (complement_label label).trans (congrArg (fun f x => !f x) eq1)
  have liftResult (p' q' : (iteratedAmbient D (3 * m)).1 → Bool)
      (he : p' = q') (c : Vertex (iteratedAmbient L (3 * m)).2)
      (hc : ReflTransGen Contiguous
        (ofTotal (K := colourComplex (iteratedAmbient D (3 * m)).2 q')
          (iterate i hi (3 * m)).val (fun s hs => (iterate i hi (3 * m)).property s hs.1))
        (fun _ => c)) :
      ∃ b', ReflTransGen Contiguous
        (ofTotal (K := colourComplex (iteratedAmbient D (3 * m)).2 p')
          (iterate i hi (3 * m)).val (fun s hs => (iterate i hi (3 * m)).property s hs.1))
        (fun _ => b') := by
    subst p'
    exact ⟨c, hc⟩
  intro j
  have hj := fin_two_cases j
  rcases hj with rfl | rfl
  · exact liftResult _ _ eq0 _ hrc
  · exact liftResult _ _ eq1 _ hlc

end

end D5.S3.Topology.StableCategory.TetrahedralRepeatedRefinement
