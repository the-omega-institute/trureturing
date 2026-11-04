/- GID: D5/S3/Geometry/IndependenceComplexTorsionSeedSingular
   generality: I
   mirror-B: D5/B/S3/Geometry/IndependenceComplexTorsionSeedSingular
   mirror-E: none(waiver:actual-coordinate-singular-homology)
   anchors: []
   utility: none
   digest: The retained actual seed class transported through the ordered/singular comparison. -/

import D5.S3.Geometry.FiniteSimplicialSingularHomology
import D5.S3.Geometry.IndependenceComplexTorsionSeed
import D5.S3.HomologicalAlgebra.FiniteFreeCoproduct

/-!
The input is the completed scientific seed module, with its actual graph,
independence complex, ordered edge and triangle enumerations, boundary maps,
and categorical homology class. No replacement quotient or additional
homology hypothesis is introduced here.

-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open CategoryTheory Limits
open scoped BigOperators Finset

namespace D5.S3.Geometry.IndependenceComplexTorsionSeedSingular

open D5.S3.HomologicalAlgebra.FiniteFreeCoproduct

abbrev K : PreAbstractSimplicialComplex IndependenceComplexTorsionSeed.Vertex := IndependenceComplexTorsionSeed.seedComplex.toPreAbstractSimplicialComplex

/-- All actual vertices, once each. -/
def vertexFaceEquiv : IndependenceComplexTorsionSeed.Vertex ≃ FiniteSimplicialSingularHomology.Face K 0 :=
  Equiv.ofBijective
    (fun v => ⟨{v}, IndependenceComplexTorsionSeed.seedComplex.singleton_mem v, by simp⟩)
    ⟨by intro a b h; simpa using congrArg Subtype.val h, by
      intro s
      obtain ⟨v, hv⟩ := Finset.card_eq_one.mp s.property.2
      exact ⟨v, Subtype.ext hv.symm⟩⟩

private def edgeFace (e : IndependenceComplexTorsionSeed.EdgeIndex) : FiniteSimplicialSingularHomology.Face K 1 :=
  let p := IndependenceComplexTorsionSeed.edgeSimplexEquiv e
  ⟨{p.val.1, p.val.2}, p.property.2, by simp [p.property.1.ne]⟩

private def triangleFace (t : IndependenceComplexTorsionSeed.TriangleIndex) : FiniteSimplicialSingularHomology.Face K 2 :=
  let p := IndependenceComplexTorsionSeed.triangleSimplexEquiv t
  ⟨{p.val.1, p.val.2.1, p.val.2.2}, p.property.2.2, by
    simp [p.property.1.ne, p.property.2.1.ne,
      (lt_trans p.property.1 p.property.2.1).ne]⟩

private theorem edgeFace_injective : Function.Injective edgeFace := by
  have h : ∀ e f : IndependenceComplexTorsionSeed.EdgeIndex,
      ({(IndependenceComplexTorsionSeed.edge e).1, (IndependenceComplexTorsionSeed.edge e).2} : Finset IndependenceComplexTorsionSeed.Vertex) =
        {(IndependenceComplexTorsionSeed.edge f).1, (IndependenceComplexTorsionSeed.edge f).2} → e = f := by decide
  intro e f hef
  exact h e f (congrArg Subtype.val hef)

private theorem triangleFace_injective : Function.Injective triangleFace := by
  have h : ∀ t u : IndependenceComplexTorsionSeed.TriangleIndex,
      ({(IndependenceComplexTorsionSeed.triangle t).1, (IndependenceComplexTorsionSeed.triangle t).2.1, (IndependenceComplexTorsionSeed.triangle t).2.2} :
          Finset IndependenceComplexTorsionSeed.Vertex) =
        {(IndependenceComplexTorsionSeed.triangle u).1, (IndependenceComplexTorsionSeed.triangle u).2.1, (IndependenceComplexTorsionSeed.triangle u).2.2} → t = u := by
    decide
  intro t u htu
  exact h t u (congrArg Subtype.val htu)

private theorem edgeFace_surjective : Function.Surjective edgeFace := by
  intro s
  let a := s.val.orderEmbOfFin s.property.2 (0 : Fin 2)
  let b := s.val.orderEmbOfFin s.property.2 (1 : Fin 2)
  have hab : a < b := (s.val.orderEmbOfFin s.property.2).lt_iff_lt.mpr (by decide)
  have hset : ({a, b} : Finset IndependenceComplexTorsionSeed.Vertex) = s.val := by
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl <;> exact Finset.orderEmbOfFin_mem _ _ _
    · simp [hab.ne, s.property.2]
  obtain ⟨e, he⟩ := IndependenceComplexTorsionSeed.edgeSimplexEquiv.surjective
    ⟨(a, b), hab, hset.symm ▸ s.property.1⟩
  refine ⟨e, Subtype.ext ?_⟩
  change ({(IndependenceComplexTorsionSeed.edgeSimplexEquiv e).val.1, (IndependenceComplexTorsionSeed.edgeSimplexEquiv e).val.2} :
    Finset IndependenceComplexTorsionSeed.Vertex) = s.val
  rw [congrArg Subtype.val he]
  exact hset

private theorem triangleFace_surjective : Function.Surjective triangleFace := by
  intro s
  let a := s.val.orderEmbOfFin s.property.2 (0 : Fin 3)
  let b := s.val.orderEmbOfFin s.property.2 (1 : Fin 3)
  let c := s.val.orderEmbOfFin s.property.2 (2 : Fin 3)
  have hab : a < b := (s.val.orderEmbOfFin s.property.2).lt_iff_lt.mpr (by decide)
  have hbc : b < c := (s.val.orderEmbOfFin s.property.2).lt_iff_lt.mpr (by decide)
  have hset : ({a, b, c} : Finset IndependenceComplexTorsionSeed.Vertex) = s.val := by
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl <;> exact Finset.orderEmbOfFin_mem _ _ _
    · simp [hab.ne, hbc.ne, (lt_trans hab hbc).ne, s.property.2]
  obtain ⟨t, ht⟩ := IndependenceComplexTorsionSeed.triangleSimplexEquiv.surjective
    ⟨(a, b, c), hab, hbc, hset.symm ▸ s.property.1⟩
  refine ⟨t, Subtype.ext ?_⟩
  change ({(IndependenceComplexTorsionSeed.triangleSimplexEquiv t).val.1, (IndependenceComplexTorsionSeed.triangleSimplexEquiv t).val.2.1,
    (IndependenceComplexTorsionSeed.triangleSimplexEquiv t).val.2.2} : Finset IndependenceComplexTorsionSeed.Vertex) = s.val
  rw [congrArg Subtype.val ht]
  exact hset

/-- Uses the seed's already exhaustive actual edge enumeration. -/
def edgeFaceEquiv : IndependenceComplexTorsionSeed.EdgeIndex ≃ FiniteSimplicialSingularHomology.Face K 1 :=
  Equiv.ofBijective edgeFace ⟨edgeFace_injective, edgeFace_surjective⟩

/-- Uses the seed's already exhaustive actual triangle enumeration. -/
def triangleFaceEquiv : IndependenceComplexTorsionSeed.TriangleIndex ≃ FiniteSimplicialSingularHomology.Face K 2 :=
  Equiv.ofBijective triangleFace ⟨triangleFace_injective, triangleFace_surjective⟩

@[simp] theorem vertexFaceEquiv_val (v : IndependenceComplexTorsionSeed.Vertex) :
    (vertexFaceEquiv v).val = {v} := rfl

@[simp] theorem edgeFaceEquiv_val (e : IndependenceComplexTorsionSeed.EdgeIndex) :
    (edgeFaceEquiv e).val = {(IndependenceComplexTorsionSeed.edge e).1, (IndependenceComplexTorsionSeed.edge e).2} := rfl

@[simp] theorem triangleFaceEquiv_val (t : IndependenceComplexTorsionSeed.TriangleIndex) :
    (triangleFaceEquiv t).val =
      {(IndependenceComplexTorsionSeed.triangle t).1, (IndependenceComplexTorsionSeed.triangle t).2.1, (IndependenceComplexTorsionSeed.triangle t).2.2} := rfl

def vertexCoordinates : FiniteSimplicialSingularHomology.orderedGroup K 0 ≅ ModuleCat.of ℤ IndependenceComplexTorsionSeed.C0 :=
  coordinateIso vertexFaceEquiv

def edgeCoordinates : FiniteSimplicialSingularHomology.orderedGroup K 1 ≅ ModuleCat.of ℤ IndependenceComplexTorsionSeed.C1 :=
  coordinateIso edgeFaceEquiv

def triangleCoordinates : FiniteSimplicialSingularHomology.orderedGroup K 2 ≅ ModuleCat.of ℤ IndependenceComplexTorsionSeed.C2 :=
  coordinateIso triangleFaceEquiv

private theorem boundaryCoordinates_apply {p : ℕ} {I : Type}
    [Fintype I] [DecidableEq I] (e : I ≃ FiniteSimplicialSingularHomology.Face K p)
    (s : FiniteSimplicialSingularHomology.Face K (p + 1)) (i : I) :
    ((FiniteSimplicialSingularHomology.faceι K s ≫ FiniteSimplicialSingularHomology.orderedBoundary K p ≫
      (coordinateIso e).hom) (1 : ℤ)) i =
        ∑ v ∈ s.val, ((-1 : ℤ) ^ #{w ∈ s.val | w < v}) *
          (if (e i).val = s.val.erase v then 1 else 0) := by
  rw [FiniteSimplicialSingularHomology.faceι, FiniteSimplicialSingularHomology.orderedBoundary, Sigma.ι_comp_desc_assoc]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, FiniteSimplicialSingularHomology.faceι,
    ι_coordinateIso]
  simp [FiniteSimplicialSingularHomology.eraseFace, Subtype.ext_iff]
  exact Finset.sum_attach s.val (fun v =>
    if (e i).val = s.val.erase v then
      (-1 : ℤ) ^ (s.val.filter (fun w => w < v)).card else 0)

private theorem edge_boundary_certificate : ∀ (e : IndependenceComplexTorsionSeed.EdgeIndex) (v : IndependenceComplexTorsionSeed.Vertex),
    IndependenceComplexTorsionSeed.edgeBoundary e v =
      ∑ a ∈ ({(IndependenceComplexTorsionSeed.edge e).1, (IndependenceComplexTorsionSeed.edge e).2} : Finset IndependenceComplexTorsionSeed.Vertex),
        ((-1 : ℤ) ^ #{w ∈ ({(IndependenceComplexTorsionSeed.edge e).1, (IndependenceComplexTorsionSeed.edge e).2} : Finset IndependenceComplexTorsionSeed.Vertex) | w < a}) *
          (if ({v} : Finset IndependenceComplexTorsionSeed.Vertex) =
            ({(IndependenceComplexTorsionSeed.edge e).1, (IndependenceComplexTorsionSeed.edge e).2} : Finset IndependenceComplexTorsionSeed.Vertex).erase a then 1 else 0) := by
  decide

private theorem triangle_boundary_certificate :
    ∀ (t : IndependenceComplexTorsionSeed.TriangleIndex) (e : IndependenceComplexTorsionSeed.EdgeIndex), IndependenceComplexTorsionSeed.triangleBoundary t e =
      ∑ v ∈ ({(IndependenceComplexTorsionSeed.triangle t).1, (IndependenceComplexTorsionSeed.triangle t).2.1, (IndependenceComplexTorsionSeed.triangle t).2.2} :
          Finset IndependenceComplexTorsionSeed.Vertex),
        ((-1 : ℤ) ^ #{w ∈ ({(IndependenceComplexTorsionSeed.triangle t).1, (IndependenceComplexTorsionSeed.triangle t).2.1,
          (IndependenceComplexTorsionSeed.triangle t).2.2} : Finset IndependenceComplexTorsionSeed.Vertex) | w < v}) *
          (if ({(IndependenceComplexTorsionSeed.edge e).1, (IndependenceComplexTorsionSeed.edge e).2} : Finset IndependenceComplexTorsionSeed.Vertex) =
            ({(IndependenceComplexTorsionSeed.triangle t).1, (IndependenceComplexTorsionSeed.triangle t).2.1, (IndependenceComplexTorsionSeed.triangle t).2.2} :
              Finset IndependenceComplexTorsionSeed.Vertex).erase v then 1 else 0) := by
  decide

/-- Equality of the actual ordered edge boundary and the retained d1 matrix. -/
theorem edge_boundary_comm :
    edgeCoordinates.hom ≫ ModuleCat.ofHom IndependenceComplexTorsionSeed.d1 =
      FiniteSimplicialSingularHomology.orderedBoundary K 0 ≫ vertexCoordinates.hom := by
  apply Sigma.hom_ext
  intro s
  obtain ⟨e, rfl⟩ := edgeFaceEquiv.surjective s
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  ext v
  change IndependenceComplexTorsionSeed.d1 ((coordinateIso edgeFaceEquiv).hom
    ((FiniteSimplicialSingularHomology.faceι K (edgeFaceEquiv e)) 1)) v =
      ((FiniteSimplicialSingularHomology.faceι K (edgeFaceEquiv e) ≫ FiniteSimplicialSingularHomology.orderedBoundary K 0 ≫
        (coordinateIso vertexFaceEquiv).hom) 1) v
  erw [coordinateIso_basis, boundaryCoordinates_apply]
  simpa only [IndependenceComplexTorsionSeed.d1, Fintype.linearCombination_apply_single, one_smul,
    vertexFaceEquiv_val, edgeFaceEquiv_val] using edge_boundary_certificate e v

/-- Equality of the actual ordered triangle boundary and the retained d2 matrix. -/
theorem triangle_boundary_comm :
    triangleCoordinates.hom ≫ ModuleCat.ofHom IndependenceComplexTorsionSeed.d2 =
      FiniteSimplicialSingularHomology.orderedBoundary K 1 ≫ edgeCoordinates.hom := by
  apply Sigma.hom_ext
  intro s
  obtain ⟨t, rfl⟩ := triangleFaceEquiv.surjective s
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  ext e
  change IndependenceComplexTorsionSeed.d2 ((coordinateIso triangleFaceEquiv).hom
    ((FiniteSimplicialSingularHomology.faceι K (triangleFaceEquiv t)) 1)) e =
      ((FiniteSimplicialSingularHomology.faceι K (triangleFaceEquiv t) ≫ FiniteSimplicialSingularHomology.orderedBoundary K 1 ≫
        (coordinateIso edgeFaceEquiv).hom) 1) e
  erw [coordinateIso_basis, boundaryCoordinates_apply]
  simpa only [IndependenceComplexTorsionSeed.d2, Fintype.linearCombination_apply_single, one_smul,
    edgeFaceEquiv_val, triangleFaceEquiv_val] using triangle_boundary_certificate t e

/-- All three basis bijections and both differentials identify the actual seed short complex. -/
def orderedSeedShortComplexIso : FiniteSimplicialSingularHomology.orderedShortComplex K ≅ IndependenceComplexTorsionSeed.seedChainComplex :=
  ShortComplex.isoMk triangleCoordinates edgeCoordinates vertexCoordinates
    (by
      change triangleCoordinates.hom ≫ ModuleCat.ofHom IndependenceComplexTorsionSeed.d2 =
        FiniteSimplicialSingularHomology.orderedBoundary K 1 ≫ edgeCoordinates.hom
      exact triangle_boundary_comm)
    (by
      change edgeCoordinates.hom ≫ ModuleCat.ofHom IndependenceComplexTorsionSeed.d1 =
        FiniteSimplicialSingularHomology.orderedBoundary K 0 ≫ vertexCoordinates.hom
      exact edge_boundary_comm)

/-- Exact comparison consumed by the retained categorical seed class. -/
def seedH1IsoSingular : IndependenceComplexTorsionSeed.seedChainComplex.homology ≅
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).obj
        (TopCat.of ↥(FiniteConeCollapse.realization K)) :=
  ShortComplex.homologyMapIso orderedSeedShortComplexIso.symm ≪≫
    FiniteSimplicialSingularHomology.orderedH1IsoSingular K

/-- The image of the very same retained cycle class in the actual singular H1 object. -/
def singularSeedClass :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).obj
        (TopCat.of ↥(FiniteConeCollapse.realization K)) :=
  seedH1IsoSingular.hom IndependenceComplexTorsionSeed.seedClass

theorem singularSeedClass_nonzero_killed_by_two :
    singularSeedClass ≠ 0 ∧ (2 : ℕ) • singularSeedClass = 0 := by
  constructor
  · intro hzero
    have h := congrArg seedH1IsoSingular.inv hzero
    apply IndependenceComplexTorsionSeed.seedClass_nonzero_killed_by_two.1
    simpa only [singularSeedClass, ModuleCat.inv_hom_apply, map_zero] using h
  · change (2 : ℕ) • seedH1IsoSingular.hom IndependenceComplexTorsionSeed.seedClass = 0
    rw [← map_nsmul, IndependenceComplexTorsionSeed.seedClass_nonzero_killed_by_two.2, map_zero]

end D5.S3.Geometry.IndependenceComplexTorsionSeedSingular
