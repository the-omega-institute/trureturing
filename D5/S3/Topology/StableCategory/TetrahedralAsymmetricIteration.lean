/- GID: D5/S3/Topology/StableCategory/TetrahedralAsymmetricIteration
   generality: I
   mirror-B: none(waiver:support-for-the-three-piece-categorical-cover)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Asymmetric refinement contracts the graph while keeping the opposite parameter four-ranked. -/

import Batteries.Tactic.OpenPrivate
import Mathlib.Basic.Finite.Sigma
import D5.S3.Topology.StableCategory.TetrahedralOneSidedRefinement
import D5.S3.Topology.StableCategory.TetrahedralRepeatedRefinement

/-! The graph parameter retains its original carriers through repeated one-sided
refinement. The opposite parameter is a new finite complex at each round. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Topology.StableCategory.TetrahedralAsymmetricIteration

open BarycentricGraphDistance (Vertex)
open BarycentricBaseRigidity (Contiguous faceImage retainedVertex sd)
open BarycentricNeighborhoodIteration (iteratedAmbient)
open OrdinaryCollarRetraction (colourComplex)
open OrdinaryContiguityLift (Simplicial comp_image ofTotal of_total_simplicial)
open OrdinarySubdivisionMap (iterate)
open TerminalCarrierIteration (chooseSelectorStep)
open TetrahedralOneSidedRefinement (ConeExtra OppositeVertexType finiteConeExtra
  oppositeFamily oppositePostOn refine_graph_against_complex refinedConeColour)
open DisjointContiguityGluing (parameterUnion parameterMap parameter_union_rank)
open D5.S3.Geometry.FiniteConeCollapse (faceSimplex)
open D5.S3.Geometry.FiniteSimplicialJoin (Space)
open GeometricGraphTermination (supported_graph_map_contracts_of_homotopy)
open Relation (ReflTransGen)

open private image from D5.S3.Topology.OrdinarySubdivisionMap
open private toUnion from D5.S3.Topology.StableCategory.DisjointContiguityGluing
open private ThroughCarrier ambientStage complement_label contract_factor
  factorization_from_refinement finite_at_depth initial_factor ofTotal_totalMap
  parameterPost parameterPost_image rank_at_depth totalMap totalMap_image
  ThroughCarrier.factor ThroughCarrier.simplicialFactor ThroughCarrier.carrier ThroughCarrier.chain
  from D5.S3.Topology.StableCategory.TetrahedralRepeatedRefinement

noncomputable section

local instance (priority := 2000) (X : Type*) : DecidableEq X := Classical.decEq X
attribute [local instance] Classical.propDecidable

private theorem ofTotal_comp_map {X U Y : Type}
    {D : PreAbstractSimplicialComplex X} {G : PreAbstractSimplicialComplex U}
    {L : PreAbstractSimplicialComplex Y} (l : X → U) (g : U → Y)
    (hl : ∀ s ∈ D, image s l ∈ G) (hg : ∀ s ∈ G, image s g ∈ L) :
    ofTotal (g ∘ l) (comp_image l hl g hg) = ofTotal g hg ∘ ofTotal l hl := by
  funext v
  exact Subtype.ext rfl

private abbrev OppositeFactor {X Y : Type}
    (D : PreAbstractSimplicialComplex X) (L : PreAbstractSimplicialComplex Y)
    (inc : Vertex D → Vertex L) : Prop :=
  ∃ (W : Type) (K : PreAbstractSimplicialComplex W),
    Finite W ∧ Nonempty (Vertex K) ∧
    (∃ rank : W → Fin 4, ∀ s ∈ K, Set.InjOn rank (s : Set W)) ∧
    ∃ (factor : Vertex D → Vertex K) (post : Vertex K → Vertex L),
      Simplicial factor ∧ Simplicial post ∧ ReflTransGen Contiguous inc (post ∘ factor)

private theorem throughCarrier_rounds_asymmetric
    {X Y U : Type} [Finite X] [Finite U]
    {D : PreAbstractSimplicialComplex X} {L : PreAbstractSimplicialComplex Y}
    {G : PreAbstractSimplicialComplex U}
    (i : X → Y) (hi : ∀ s ∈ D, image s i ∈ L)
    (g : U → Y) (hg : ∀ s ∈ G, image s g ∈ L)
    (rankG : U → Fin 2) (properG : ∀ s ∈ G, Set.InjOn rankG (s : Set U))
    (anchorG : Vertex G) (p : X → Bool)
    (left : ThroughCarrier (colourComplex D p) L G 0 0
      (ofTotal (K := colourComplex D p) i (fun s hs => hi s hs.1)) (ambientStage g hg 0))
    (right : OppositeFactor (colourComplex D (fun x => !p x)) L
      (ofTotal i (fun s hs => hi s hs.1))) (m : ℕ) :
    let A := (iteratedAmbient D (3 * m)).2
    let B := (iteratedAmbient L (3 * m)).2
    let inc := iterate i hi (3 * m)
    ∃ q : (iteratedAmbient D (3 * m)).1 → Bool,
      Nonempty (ThroughCarrier (colourComplex A q) B G (4 * m) (3 * m)
        (ofTotal (K := colourComplex A q) inc.val (fun s hs => inc.property s hs.1))
        (ambientStage g hg (3 * m))) ∧
      OppositeFactor (colourComplex A (fun x => !q x)) B
        (ofTotal inc.val (fun s hs => inc.property s hs.1)) := by
  induction m with
  | zero => exact ⟨p, ⟨left⟩, right⟩
  | succ m ih =>
    simp only [Nat.mul_succ]
    obtain ⟨q, ⟨F⟩, opposite⟩ := ih
    obtain ⟨W, K, finiteW, ⟨anchorW⟩, ⟨rankK, properK⟩, factorW, postW,
      factorW_simplicial, postW_simplicial, chainW⟩ := opposite
    let : Finite W := finiteW
    let : Finite (iteratedAmbient D (3 * m)).1 := finite_at_depth D (3 * m)
    let : Finite (iteratedAmbient G (4 * m)).1 := finite_at_depth G (4 * m)
    let inc := iterate i hi (3 * m)
    let graphAnchor := retainedVertex (4 * m) anchorG
    let fallback := (retainedVertex (3 * m) anchorG).val
    let graphFactor := totalMap (ThroughCarrier.factor F) graphAnchor.val
    let graphPost := parameterPost F fallback
    let graphFactor_image := totalMap_image (ThroughCarrier.factor F) (ThroughCarrier.simplicialFactor F) graphAnchor.val
    let graphPost_image := parameterPost_image F fallback
    let rightFactor := totalMap factorW anchorW.val
    let rightPost := totalMap postW (postW anchorW).val
    let rightFactor_image := totalMap_image factorW factorW_simplicial anchorW.val
    let rightPost_image := totalMap_image postW postW_simplicial (postW anchorW).val
    obtain ⟨rank, proper⟩ := rank_at_depth G rankG properG (4 * m)
    let select := chooseSelectorStep G (4 * m + 3)
    have graphChain : ReflTransGen Contiguous
        (ofTotal (K := colourComplex (iteratedAmbient D (3 * m)).2 q)
          inc.val (fun s hs => inc.property s hs.1))
        (ofTotal (graphPost ∘ graphFactor)
          (comp_image graphFactor graphFactor_image graphPost graphPost_image)) := by
      have eq : ofTotal (graphPost ∘ graphFactor)
          (comp_image graphFactor graphFactor_image graphPost graphPost_image) =
          ambientStage g hg (3 * m) ∘ (ThroughCarrier.carrier F) ∘ (ThroughCarrier.factor F) := by
        funext v
        apply Subtype.ext
        simp [graphPost, graphFactor, parameterPost, ambientStage, ofTotal, totalMap,
          v.property, ((ThroughCarrier.factor F) v).property]
      exact eq.symm ▸ (ThroughCarrier.chain F)
    have rightChain : ReflTransGen Contiguous
        (ofTotal (K := colourComplex (iteratedAmbient D (3 * m)).2 (fun x => !q x))
          inc.val (fun s hs => inc.property s hs.1))
        (ofTotal (rightPost ∘ rightFactor)
          (comp_image rightFactor rightFactor_image rightPost rightPost_image)) := by
      have eq : ofTotal (rightPost ∘ rightFactor)
          (comp_image rightFactor rightFactor_image rightPost rightPost_image) =
          postW ∘ factorW := by
        calc
          _ = ofTotal rightPost rightPost_image ∘ ofTotal rightFactor rightFactor_image :=
            ofTotal_comp_map rightFactor rightPost rightFactor_image rightPost_image
          _ = postW ∘ factorW := congrArg₂ Function.comp
            (ofTotal_totalMap postW postW_simplicial (postW anchorW).val)
            (ofTotal_totalMap factorW factorW_simplicial anchorW.val)
      exact eq.symm ▸ chainW
    obtain ⟨factorG, factorH, extraPoint, hFactorG, hFactorH, hPostH, _, chainG, chainH⟩ :=
      refine_graph_against_complex inc.val inc.property q graphFactor rightFactor
        graphFactor_image rightFactor_image rank proper graphPost rightPost
        graphPost_image rightPost_image graphAnchor graphChain rightChain select.map select.member
    let label := refinedConeColour q graphFactor graphFactor_image rank
    refine ⟨fun v => decide (label v = 1), ?_, ?_⟩
    · exact ⟨factorization_from_refinement F fallback select _ factorG hFactorG chainG⟩
    · let E := ConeExtra (iteratedAmbient G (4 * m)).2 rank
      letI : Finite E := finiteConeExtra _ rank
      letI : ∀ j : Option E, Finite (OppositeVertexType K j) := by
        intro j
        cases j with
        | none => exact finite_at_depth K 3
        | some _ =>
          change Finite Unit
          infer_instance
      let family := oppositeFamily K E
      let H' := parameterUnion family
      have finiteH' : Finite (Σ j : Option E, OppositeVertexType K j) := inferInstance
      have anchorH' : Nonempty (Vertex H') :=
        ⟨toUnion family none (retainedVertex 3 anchorW)⟩
      have boundK : ∀ s ∈ K, (s : Finset W).card ≤ 4 := by
        intro s hs
        rw [← Finset.card_image_of_injOn (properK s hs)]
        exact (Finset.card_le_univ _).trans (by simp)
      have rankedH' :
          ∃ rank : (Σ j : Option E, OppositeVertexType K j) → Fin 4,
            ∀ s ∈ H', Set.InjOn rank (s : Set _) := by
        have bound₁ := (ColourGraphJoin.subdivision_rank_colouring K boundK).1
        have bound₂ := (ColourGraphJoin.subdivision_rank_colouring (sd K) bound₁).1
        obtain ⟨rank₃, proper₃⟩ :=
          (ColourGraphJoin.subdivision_rank_colouring (sd (sd K)) bound₂).2
        let colours : ∀ j : Option E, OppositeVertexType K j → Fin 4
          | none => rank₃
          | some _ => fun _ => 0
        refine ⟨_, parameter_union_rank family colours ?_⟩
        intro j
        cases j with
        | none => exact proper₃
        | some _ => exact fun _ _ _ _ _ _ _ => Subsingleton.elim _ _
      let atExtra := ofTotal (iterate graphPost graphPost_image 3).val
        (iterate graphPost graphPost_image 3).property ∘ extraPoint
      let postH := parameterMap family (oppositePostOn rightPost rightPost_image atExtra)
      have transfer (qRight : (iteratedAmbient D (3 * m + 3)).1 → Bool)
          (eq : qRight = fun v => decide (label v = 0)) :
          OppositeFactor (colourComplex (iteratedAmbient D (3 * m + 3)).2 qRight)
            (iteratedAmbient L (3 * m + 3)).2
            (ofTotal (iterate i hi (3 * m + 3)).val
              (fun s hs => (iterate i hi (3 * m + 3)).property s hs.1)) := by
        subst qRight
        exact ⟨_, H', finiteH', anchorH', rankedH', factorH, postH, hFactorH, hPostH, chainH⟩
      exact transfer _ (complement_label label).symm

/-- A geometrically null graph factor becomes categorical after finitely many
one-sided rounds. At the same ordinary subdivision depth, the complementary
induced region factors up to contiguity through a finite complex of dimension
at most three. -/
theorem eventually_contracts_graph_against_complex
    {X Y U V : Type} [Finite X] [Fintype Y] [Fintype U] [Finite V]
    {D : PreAbstractSimplicialComplex X} {L : PreAbstractSimplicialComplex Y}
    {G : PreAbstractSimplicialComplex U} {H : PreAbstractSimplicialComplex V}
    (i : X → Y) (hi : ∀ s ∈ D, image s i ∈ L)
    (p : X → Bool) (l : X → U) (r : X → V)
    (hl : ∀ s ∈ colourComplex D p, image s l ∈ G)
    (hr : ∀ s ∈ colourComplex D (fun x => !p x), image s r ∈ H)
    (rankG : U → Fin 2) (properG : ∀ s ∈ G, Set.InjOn rankG (s : Set U))
    (anchorG : Vertex G) (anchorH : Vertex H)
    (rankH : V → Fin 4) (properH : ∀ s ∈ H, Set.InjOn rankH (s : Set V))
    (g : U → Y) (hg : ∀ s ∈ G, image s g ∈ L)
    (h : V → Y) (hh : ∀ s ∈ H, image s h ∈ L)
    (left : ReflTransGen Contiguous
      (ofTotal (K := colourComplex D p) i (fun s hs => hi s hs.1))
      (ofTotal (g ∘ l) (comp_image l hl g hg)))
    (right : ReflTransGen Contiguous
      (ofTotal (K := colourComplex D (fun x => !p x)) i (fun s hs => hi s hs.1))
      (ofTotal (h ∘ r) (comp_image r hr h hh)))
    (realG : C(Space G, Space L))
    (supportG : ∀ s (hs : s ∈ G) (z : Space G), z.val ∈ faceSimplex s →
      (realG z).val ∈ faceSimplex (faceImage (ofTotal g hg) hs))
    (qG : Space L) (nullG : realG.Homotopy (ContinuousMap.const (Space G) qG)) :
    ∃ m : ℕ,
      let A := (iteratedAmbient D (3 * m)).2
      let B := (iteratedAmbient L (3 * m)).2
      let inc := iterate i hi (3 * m)
      ∃ q : (iteratedAmbient D (3 * m)).1 → Bool,
        (∃ b : Vertex B, ReflTransGen Contiguous
          (ofTotal (K := colourComplex A q) inc.val (fun s hs => inc.property s hs.1))
          (fun _ => b)) ∧
        ∃ (W : Type) (K : PreAbstractSimplicialComplex W),
          Finite W ∧ Nonempty (Vertex K) ∧
          (∃ rank : W → Fin 4, ∀ s ∈ K, Set.InjOn rank (s : Set W)) ∧
          ∃ (factor : Vertex (colourComplex A (fun x => !q x)) → Vertex K)
            (post : Vertex K → Vertex B),
            Simplicial factor ∧ Simplicial post ∧ ReflTransGen Contiguous
              (ofTotal (K := colourComplex A (fun x => !q x))
                inc.val (fun s hs => inc.property s hs.1)) (post ∘ factor) := by
  have cardG (s : Finset U) (hs : s ∈ G) : s.card ≤ 2 := by
    rw [← Finset.card_image_of_injOn (properG s hs)]
    exact (Finset.card_le_univ _).trans (by simp)
  obtain ⟨base, d, contracts⟩ := supported_graph_map_contracts_of_homotopy
    cardG (ofTotal g hg) (of_total_simplicial g hg) realG supportG qG nullG
  have initialRight : OppositeFactor (colourComplex D (fun x => !p x)) L
      (ofTotal i (fun s hs => hi s hs.1)) := by
    refine ⟨V, H, inferInstance, ⟨anchorH⟩, ⟨rankH, properH⟩, ofTotal r hr, ofTotal h hh,
      of_total_simplicial r hr, of_total_simplicial h hh, ?_⟩
    exact (ofTotal_comp_map r h hr hh) ▸ right
  obtain ⟨q, ⟨F⟩, opposite⟩ := throughCarrier_rounds_asymmetric i hi g hg rankG properG
    anchorG p (initial_factor (D := colourComplex D p) i l g (fun s hs => hi s hs.1) hl hg left)
    initialRight d
  have depth : 4 * d = d + 3 * d := by
    simpa only [Nat.one_mul] using (Nat.add_mul 1 3 d)
  exact ⟨d, q, ⟨retainedVertex (3 * d) base,
    contract_factor G L rankG properG g hg anchorG d _ _ depth d le_rfl base contracts F⟩,
    opposite⟩

end

end D5.S3.Topology.StableCategory.TetrahedralAsymmetricIteration
