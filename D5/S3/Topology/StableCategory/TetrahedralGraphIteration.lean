/- GID: D5/S3/Topology/StableCategory/TetrahedralGraphIteration
   generality: I
   mirror-B: D5/B/S3/Topology/StableCategory/TetrahedralGraphIteration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: One ordinary tetrahedral refinement adds three ambient and four parameter subdivisions. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Topology.StableCategory.ColourGraphJoin
import D5.S3.Topology.GeometricGraphTermination
import D5.S3.Topology.StableCategory.TetrahedralMainFactorization
import D5.S3.Topology.StableCategory.TerminalCarrierIteration
import Mathlib.Topology.Order.IntermediateValue

/-! Iterate the tetrahedral refinement on the two graph parameters. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Topology.StableCategory.TetrahedralGraphIteration

open D5.S3.Geometry.FiniteConeCollapse (realization_mem_iff)
open D5.S3.Geometry.FiniteSimplicialJoin (Space simplicialJoin)
open D5.S3.Geometry.FiniteVertexCylinder (vertexPoint)
open BarycentricGraphDistance (Vertex)
open BarycentricBaseRigidity (Contiguous sd skeleton)
open BarycentricNeighborhoodIteration (iteratedAmbient)
open OrdinaryCollarRetraction (colourComplex)
open OrdinaryContiguityLift (Simplicial comp_image comp_chains iterate_comp ofTotal
  of_total_simplicial subdivide)
open OrdinarySubdivisionMap (iterate)
open TerminalCarrierIteration (selector_naturality)
open TetrahedronCollar16 (Color hasColour opposite)
open TetrahedralMainFactorization (refine_colour_factorization)
open Relation (ReflTransGen)
open scoped BigOperators
open private singleton_mem_of_mem from D5.S3.Topology.BarycentricBaseRigidity
open private image from D5.S3.Topology.OrdinarySubdivisionMap
open private restricted_image from D5.S3.Topology.StableCategory.OrdinaryCollarNaturality
open private refinedColourComplex from D5.S3.Topology.StableCategory.TetrahedralMainFactorization
open private subdivide_simplicial from D5.S3.Topology.StableCategory.TerminalCarrierIteration
open private left_projection_image right_projection_image from D5.S3.Topology.StableCategory.ColourGraphJoin

noncomputable section

local instance (priority := 2000) (V : Type*) : DecidableEq V := Classical.decEq V

/-- A path between realized vertices forces them to lie in one edge component.
Each realized simplex places all its mass in one component of the one-skeleton. -/
theorem skeleton_reachable_of_preconnected_realization {X : Type} [Fintype X]
    (K : PreAbstractSimplicialComplex X) [PreconnectedSpace (Space K)]
    (a b : Vertex K) : (skeleton K).Reachable a b := by
  classical
  by_contra h
  let inComponent (x : X) := ∃ v : Vertex K, v.val = x ∧ (skeleton K).Reachable a v
  let S := Finset.univ.filter inComponent
  let mass (q : Space K) : ℝ := ∑ x ∈ S, q.val x
  have ha : inComponent a.val := ⟨a, rfl, SimpleGraph.Reachable.rfl⟩
  have hb : ¬ inComponent b.val := by
    rintro ⟨v, hval, hv⟩
    exact h ((Subtype.ext hval : v = b) ▸ hv)
  have hm : Continuous mass :=
    continuous_finsetSum _ (fun x _ => (continuous_apply x).comp continuous_subtype_val)
  have mass_cases (q : Space K) : mass q = 0 ∨ mass q = 1 := by
    obtain ⟨s, hs, hq⟩ := (realization_mem_iff K q.val).mp q.property
    have supported (x : X) (hx : q.val x ≠ 0) : x ∈ s := by
      by_contra hxs
      exact hx (hq.2.2 x hxs)
    by_cases hpart : ∃ x ∈ S, q.val x ≠ 0
    · obtain ⟨x, hxS, hx⟩ := hpart
      have ⟨u, hux, hu⟩ := (Finset.mem_filter.mp hxS).2
      have hxFace : u.val ∈ s := by rw [hux]; exact supported x hx
      have ht (y : X) (hy : q.val y ≠ 0) : inComponent y := by
        let v : Vertex K := ⟨y, singleton_mem_of_mem hs (supported y hy)⟩
        refine ⟨v, rfl, hu.trans ?_⟩
        by_cases he : u = v
        · exact he ▸ SimpleGraph.Reachable.rfl
        have hpair : ({u.val, v.val} : Finset X) ∈ K :=
          (K.isRelLowerSet_faces hs).2
            (Finset.insert_subset_iff.mpr ⟨hxFace, Finset.singleton_subset_iff.mpr (supported y hy)⟩)
            (by simp)
        exact (show (skeleton K).Adj u v from ⟨he, hpair⟩).reachable
      right
      change (∑ y ∈ Finset.univ.filter inComponent, q.val y) = 1
      rw [Finset.sum_filter, ← hq.2.1]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : q.val y = 0
      · simp [hy]
      · exact if_pos (ht y hy)
    · left
      exact Finset.sum_eq_zero (fun x hx => by
        by_contra hn
        exact hpart ⟨x, hx, hn⟩)
  have single_mass (v : Vertex K) :
      mass (vertexPoint K v.val v.property) = if inComponent v.val then 1 else 0 := by
    change (∑ x ∈ Finset.univ.filter inComponent, (Pi.single v.val (1 : ℝ) : X → ℝ) x) = _
    rw [Finset.sum_filter]
    have eval (x : X) :
        (if inComponent x then (Pi.single v.val (1 : ℝ) : X → ℝ) x else 0) =
          (if x = v.val then (if inComponent v.val then 1 else 0) else 0) := by
      by_cases e : x = v.val
      · subst x
        simp
      · simp [Pi.single_apply, e, Ne.symm e]
    trans ∑ x : X, if x = v.val then (if inComponent v.val then 1 else 0) else 0
    · exact Finset.sum_congr rfl (fun x _ => eval x)
    · simp
  have h0 : (0 : ℝ) ∈ Set.range mass :=
    ⟨vertexPoint K b.val b.property, by rw [single_mass, if_neg hb]⟩
  have h1 : (1 : ℝ) ∈ Set.range mass :=
    ⟨vertexPoint K a.val a.property, by rw [single_mass, if_pos ha]⟩
  have hmid : (1 / 2 : ℝ) ∈ Set.range mass :=
    (isPreconnected_range hm).Icc_subset h0 h1 ⟨by norm_num, by norm_num⟩
  obtain ⟨q, hq⟩ := hmid
  rcases mass_cases q with hz | hz <;> rw [hq] at hz <;> norm_num at hz

/-- Compare the one-round tetrahedral factorization in the join with the
fourth subdivision of its untagged parameter. The backward selector may
be chosen in the untagged graph before this round is applied. -/
theorem refine_in_untagged_parameter
    {U X W Z : Type} [Finite U] [Finite X]
    {D : PreAbstractSimplicialComplex U} {K : PreAbstractSimplicialComplex X}
    {A : PreAbstractSimplicialComplex W} {L : PreAbstractSimplicialComplex Z}
    (i : U → Z) (hi : ∀ s ∈ D, image s i ∈ L)
    (f : U → X) (hf : ∀ s ∈ D, image s f ∈ K)
    (colour : X → Fin 4) (c : Color) (hinj : ∀ s ∈ K, Set.InjOn colour (s : Set X))
    (p : X → W) (hp : ∀ s ∈ colourComplex K (hasColour c ∘ colour), image s p ∈ A)
    (g : W → Z) (hg : ∀ s ∈ A, image s g ∈ L)
    (gOpp : X → Z)
    (hgOpp : ∀ s ∈ colourComplex K (hasColour (opposite c) ∘ colour), image s gOpp ∈ L)
    (old : ReflTransGen Contiguous
      (ofTotal (K := colourComplex D ((hasColour c ∘ colour) ∘ f)) i (fun s hs => hi s hs.1))
      (ofTotal ((g ∘ p) ∘ f) (comp_image f
        (restricted_image f hf ((hasColour c ∘ colour) ∘ f) (hasColour c ∘ colour)
          (fun _ => rfl)) (g ∘ p) (comp_image p hp g hg))))
    (oldOpp : ReflTransGen Contiguous
      (ofTotal (K := colourComplex D ((hasColour (opposite c) ∘ colour) ∘ f)) i
        (fun s hs => hi s hs.1))
      (ofTotal (gOpp ∘ f) (comp_image f
        (restricted_image f hf ((hasColour (opposite c) ∘ colour) ∘ f)
          (hasColour (opposite c) ∘ colour) (fun _ => rfl)) gOpp hgOpp))) :
    let P := refinedColourComplex f hf colour c
    let B := (iteratedAmbient (colourComplex K (hasColour c ∘ colour)) 3).2
    let C := (iteratedAmbient A 3).2
    ∀ (anchor : Vertex (sd B))
      (connected : ∀ a b : Vertex (iteratedAmbient L 3).2,
        (skeleton (iteratedAmbient L 3).2).Reachable a b)
      (select : Vertex (sd C) → Vertex C),
      (∀ v, (select v).val ∈ v.val.val) →
      ∃ factor : Vertex P → Vertex (sd C),
        Simplicial factor ∧ ReflTransGen Contiguous
          (ofTotal (K := P) (iterate i hi 3).val (fun s hs => (iterate i hi 3).property s hs.1))
          (ofTotal (iterate g hg 3).val (iterate g hg 3).property ∘ select ∘ factor) := by
  intro P B C anchor connected select hselect
  let hp3 := (iterate p hp 3).property
  let projection := ofTotal (iterate p hp 3).val hp3
  have hprojection : Simplicial projection := of_total_simplicial _ _
  let post := ofTotal (iterate g hg 3).val (iterate g hg 3).property
  have hpost : Simplicial post := of_total_simplicial _ _
  obtain ⟨tagSelect, tagFactor, htagMember, _, hfactor, chain⟩ :=
    refine_colour_factorization i hi f hf colour c (g ∘ p) gOpp hinj
      (comp_image p hp g hg) hgOpp old oldOpp anchor connected
  have hcomp :
      ofTotal (iterate (g ∘ p) (comp_image p hp g hg) 3).val
        (iterate (g ∘ p) (comp_image p hp g hg) 3).property = post ∘ projection := by
    funext v
    apply Subtype.ext
    exact congrFun (iterate_comp p hp g hg 3) v.val
  rw [hcomp] at chain
  let factor := subdivide projection hprojection ∘ tagFactor
  have newChain :=
    comp_chains tagFactor post hfactor hpost (ReflTransGen.single
      (selector_naturality projection hprojection tagSelect select htagMember hselect))
  exact ⟨factor, (subdivide_simplicial projection hprojection).comp hfactor,
    chain.trans newChain⟩

private theorem left_rank_colour {U V : Type}
    (rankU : U → Fin 2) (rankV : V → Fin 2) :
    hasColour (1 : Color) ∘ ColourGraphJoin.joinRank rankU rankV =
      (ColourGraphJoin.leftColour : U ⊕ V → Bool) := by
  funext x
  rcases x with u | v
  · have step (a : Fin 2) : hasColour 1
        (ColourGraphJoin.joinRank (fun _ : U => a) rankV (Sum.inl u)) =
        ColourGraphJoin.leftColour (Sum.inl u : U ⊕ V) := by
      fin_cases a <;> rfl
    exact step (rankU u)
  · have step (b : Fin 2) : hasColour 1
        (ColourGraphJoin.joinRank rankU (fun _ : V => b) (Sum.inr v)) =
        ColourGraphJoin.leftColour (Sum.inr v : U ⊕ V) := by
      fin_cases b <;> rfl
    exact step (rankV v)

private theorem right_rank_colour {U V : Type}
    (rankU : U → Fin 2) (rankV : V → Fin 2) :
    hasColour (0 : Color) ∘ ColourGraphJoin.joinRank rankU rankV =
      (ColourGraphJoin.rightColour : U ⊕ V → Bool) := by
  funext x
  rcases x with u | v
  · have step (a : Fin 2) : hasColour 0
        (ColourGraphJoin.joinRank (fun _ : U => a) rankV (Sum.inl u)) =
        ColourGraphJoin.rightColour (Sum.inl u : U ⊕ V) := by
      fin_cases a <;> rfl
    exact step (rankU u)
  · have step (b : Fin 2) : hasColour 0
        (ColourGraphJoin.joinRank rankU (fun _ : V => b) (Sum.inr v)) =
        ColourGraphJoin.rightColour (Sum.inr v : U ⊕ V) := by
      fin_cases b <;> rfl
    exact step (rankV v)

private theorem change_colour_labels {D Z : Type}
    {A : PreAbstractSimplicialComplex D} {L : PreAbstractSimplicialComplex Z}
    {p q : D → Bool} (hpq : p = q)
    (i f g : D → Z) (hi : ∀ s ∈ A, image s i ∈ L)
    (hf : ∀ s ∈ colourComplex A p, image s f ∈ L)
    (hg : ∀ s ∈ colourComplex A q, image s g ∈ L)
    (equal : ∀ x, q x = true → f x = g x)
    (chain : ReflTransGen Contiguous
      (ofTotal (K := colourComplex A p) i (fun s hs => hi s hs.1)) (ofTotal f hf)) :
    ReflTransGen Contiguous
      (ofTotal (K := colourComplex A q) i (fun s hs => hi s hs.1)) (ofTotal g hg) := by
  subst q
  have he : ofTotal f hf = ofTotal g hg := by
    funext v
    exact Subtype.ext (equal v.val (v.property.2 v.val (Finset.mem_singleton_self _)))
  exact he ▸ chain

/-- An ordinary three-step refinement of a two-colour factorization gives
two new factor maps into the four-step subdivisions of the same parameters. -/
theorem refine_bicolour_graphs
    {D U V Z : Type} [Finite D] [Finite U] [Finite V]
    {A : PreAbstractSimplicialComplex D} {G : PreAbstractSimplicialComplex U}
    {H : PreAbstractSimplicialComplex V} {L : PreAbstractSimplicialComplex Z}
    (i : D → Z) (hi : ∀ s ∈ A, image s i ∈ L)
    (p : D → Bool) (l : D → U) (r : D → V)
    (hl : ∀ s ∈ colourComplex A p, image s l ∈ G)
    (hr : ∀ s ∈ colourComplex A (fun x => !p x), image s r ∈ H)
    (a : U → Fin 2) (b : V → Fin 2)
    (ha : ∀ s ∈ G, Set.InjOn a (s : Set U))
    (hb : ∀ s ∈ H, Set.InjOn b (s : Set V))
    (g : U → Z) (h : V → Z)
    (hg : ∀ s ∈ G, image s g ∈ L) (hh : ∀ s ∈ H, image s h ∈ L)
    (left : Vertex G) (right : Vertex H)
    (oldLeft : ReflTransGen Contiguous
      (ofTotal (K := colourComplex A p) i (fun s hs => hi s hs.1))
      (ofTotal (g ∘ l) (comp_image l hl g hg)))
    (oldRight : ReflTransGen Contiguous
      (ofTotal (K := colourComplex A (fun x => !p x)) i (fun s hs => hi s hs.1))
      (ofTotal (h ∘ r) (comp_image r hr h hh)))
    (connected : ∀ x y : Vertex (iteratedAmbient L 3).2,
      (skeleton (iteratedAmbient L 3).2).Reachable x y)
    (selectG : Vertex (iteratedAmbient G 4).2 → Vertex (iteratedAmbient G 3).2)
    (selectH : Vertex (iteratedAmbient H 4).2 → Vertex (iteratedAmbient H 3).2)
    (memberG : ∀ v, (selectG v).val ∈ v.val.val)
    (memberH : ∀ v, (selectH v).val ∈ v.val.val) :
    ∃ colour : (iteratedAmbient A 3).1 → Color,
      ∃ (factorG : Vertex (colourComplex (iteratedAmbient A 3).2
            (fun v => decide (colour v = 1))) → Vertex (iteratedAmbient G 4).2)
        (factorH : Vertex (colourComplex (iteratedAmbient A 3).2
            (fun v => decide (colour v = 0))) → Vertex (iteratedAmbient H 4).2),
        Simplicial factorG ∧ Simplicial factorH ∧
        ReflTransGen Contiguous
          (ofTotal (K := colourComplex (iteratedAmbient A 3).2 (fun v => decide (colour v = 1)))
            (iterate i hi 3).val (fun s hs => (iterate i hi 3).property s hs.1))
          (ofTotal (iterate g hg 3).val (iterate g hg 3).property ∘ selectG ∘ factorG) ∧
        ReflTransGen Contiguous
          (ofTotal (K := colourComplex (iteratedAmbient A 3).2 (fun v => decide (colour v = 0)))
            (iterate i hi 3).val (fun s hs => (iterate i hi 3).property s hs.1))
          (ofTotal (iterate h hh 3).val (iterate h hh 3).property ∘ selectH ∘ factorH) := by
  let J := simplicialJoin G H
  let f := ColourGraphJoin.joinMap p l r
  have hf : ∀ s ∈ A, image s f ∈ J := ColourGraphJoin.join_map_image p l r hl hr
  let rank := ColourGraphJoin.joinRank a b
  have proper : ∀ s ∈ J, Set.InjOn rank (s : Set (U ⊕ V)) :=
    ColourGraphJoin.join_rank_proper a b ha hb
  have leftCut : hasColour (1 : Color) ∘ rank = ColourGraphJoin.leftColour :=
    left_rank_colour a b
  have rightCut : hasColour (0 : Color) ∘ rank = ColourGraphJoin.rightColour :=
    right_rank_colour a b
  let pl : U ⊕ V → U := Sum.elim id (fun _ => left.val)
  let pr : U ⊕ V → V := Sum.elim (fun _ => right.val) id
  have hpl : ∀ s ∈ colourComplex J (hasColour 1 ∘ rank), image s pl ∈ G := by
    rw [leftCut]
    exact left_projection_image left.val
  have hpr : ∀ s ∈ colourComplex J (hasColour 0 ∘ rank), image s pr ∈ H := by
    rw [rightCut]
    exact right_projection_image right.val
  have sourceLeft : p = (hasColour 1 ∘ rank) ∘ f := by
    funext x
    change p x = (hasColour 1 ∘ rank) (f x)
    rw [leftCut]
    cases e : p x <;> simp [f, ColourGraphJoin.joinMap, ColourGraphJoin.leftColour, e]
  have sourceRight : (fun x => !p x) = (hasColour 0 ∘ rank) ∘ f := by
    funext x
    change (!p x) = (hasColour 0 ∘ rank) (f x)
    rw [rightCut]
    cases e : p x <;> simp [f, ColourGraphJoin.joinMap, ColourGraphJoin.rightColour, e]
  have leftChain := change_colour_labels sourceLeft i (g ∘ l) ((g ∘ pl) ∘ f) hi
    (comp_image l hl g hg) (comp_image f
      (restricted_image f hf ((hasColour 1 ∘ rank) ∘ f) (hasColour 1 ∘ rank) (fun _ => rfl))
      (g ∘ pl) (comp_image pl hpl g hg)) (by
        intro x hx
        rw [← sourceLeft] at hx
        simp [f, pl, ColourGraphJoin.joinMap, hx]) oldLeft
  have rightChain := change_colour_labels sourceRight i (h ∘ r) ((h ∘ pr) ∘ f) hi
    (comp_image r hr h hh) (comp_image f
      (restricted_image f hf ((hasColour 0 ∘ rank) ∘ f) (hasColour 0 ∘ rank) (fun _ => rfl))
      (h ∘ pr) (comp_image pr hpr h hh)) (by
        intro x hx
        rw [← sourceRight] at hx
        have e : p x = false := by cases he : p x <;> simp_all
        simp [f, pr, ColourGraphJoin.joinMap, e]) oldRight
  have leftVertex : Vertex (colourComplex J (hasColour 1 ∘ rank)) := by
    rw [leftCut]
    exact ColourGraphJoin.leftJoinMap left
  have rightVertex : Vertex (colourComplex J (hasColour 0 ∘ rank)) := by
    rw [rightCut]
    exact ColourGraphJoin.rightJoinMap right
  obtain ⟨factorG, hfactorG, hchainG⟩ :=
    refine_in_untagged_parameter i hi f hf rank 1 proper pl hpl g hg (h ∘ pr)
      (comp_image pr hpr h hh) leftChain rightChain
      (BarycentricBaseRigidity.retainedVertex 4 leftVertex) connected selectG memberG
  obtain ⟨factorH, hfactorH, hchainH⟩ :=
    refine_in_untagged_parameter i hi f hf rank 0 proper pr hpr h hh (g ∘ pl)
      (comp_image pl hpl g hg) rightChain leftChain
      (BarycentricBaseRigidity.retainedVertex 4 rightVertex) connected selectH memberH
  exact ⟨TetrahedralMainFactorization.refinedColour f hf rank, factorG, factorH, hfactorG,
    hfactorH, hchainG, hchainH⟩

end

end D5.S3.Topology.StableCategory.TetrahedralGraphIteration
