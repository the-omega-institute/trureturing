/- GID: D5/S3/Geometry/FiniteGraphSubgraphSuspension
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteGraphSubgraphSuspension
   mirror-E: none(waiver:finite-graph-singular-homology)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Clique]
   utility: none
   digest: Local arbitrary-subgraph transport and the reduced singular homology endpoint. -/
import D5.S3.Geometry.FiniteGraphSubgraphSuspensionRetraction
import D5.S3.Topology.TauCeti.AlgebraicTopology.Singular.MayerVietoris.Reduced
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Local subgraphs and homology endpoint

The local subgraph convention is transported to the spanning convention,
then the existing reduced Mayer--Vietoris connecting isomorphism consumes
the geometric cover and intersection equivalence.
-/

noncomputable section
open Set Topology CategoryTheory
open scoped BigOperators unitInterval ContinuousMap

namespace D5.S3.Geometry.FiniteGraphSubgraphSuspension

open FiniteConeCollapse FiniteGraphVertexSubstitution FiniteCoordinateTruncation

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G H : SimpleGraph V)

section LocalSubgraph

variable (H₀ : G.Subgraph)

private def outside : Finset V := by classical exact Finset.univ.filter (fun a => a ∉ H₀.verts)
private def restrictSet (M : Finset V) : Finset H₀.verts := by
  classical exact M.subtype (fun a => a ∈ H₀.verts)
private def extendSet (N : Finset H₀.verts) : Finset V :=
  N.image Subtype.val ∪ outside G H₀

private theorem restrict_mem (M : Finset V) (a : H₀.verts) :
    a ∈ restrictSet G H₀ M ↔ a.val ∈ M := by
  classical
  simp [restrictSet]

private theorem extend_mem (N : Finset H₀.verts) (a : V) :
    a ∈ extendSet G H₀ N ↔ a ∉ H₀.verts ∨
      ∃ ha : a ∈ H₀.verts, (⟨a, ha⟩ : H₀.verts) ∈ N := by
  classical
  simp only [extendSet, Finset.mem_union, Finset.mem_image, outside,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨b, hb, rfl⟩ | ha)
    · exact Or.inr ⟨b.property, hb⟩
    · exact Or.inl ha
  · rintro (ha | ⟨ha, hN⟩)
    · exact Or.inr ha
    · exact Or.inl ⟨⟨a, ha⟩, hN, rfl⟩

private theorem restrict_independent {M : Finset V}
    (hM : H₀.spanningCoe.IsIndepSet (M : Set V)) :
    H₀.coe.IsIndepSet (restrictSet G H₀ M : Set H₀.verts) := by
  intro a ha b hb hab hadj
  exact hM ((restrict_mem G H₀ M a).mp ha) ((restrict_mem G H₀ M b).mp hb)
    (fun h => hab (Subtype.ext h)) hadj

private theorem extend_independent {N : Finset H₀.verts}
    (hN : H₀.coe.IsIndepSet (N : Set H₀.verts)) :
    H₀.spanningCoe.IsIndepSet (extendSet G H₀ N : Set V) := by
  intro a ha b hb hab hadj
  have haW : a ∈ H₀.verts := H₀.edge_vert hadj
  have hbW : b ∈ H₀.verts := H₀.edge_vert (H₀.adj_symm hadj)
  obtain ⟨_, haN⟩ := ((extend_mem G H₀ N a).mp ha).resolve_left (not_not.mpr haW)
  obtain ⟨_, hbN⟩ := ((extend_mem G H₀ N b).mp hb).resolve_left (not_not.mpr hbW)
  exact hN haN hbN (fun h => hab (congrArg Subtype.val h)) hadj

private theorem restrict_extend (N : Finset H₀.verts) :
    restrictSet G H₀ (extendSet G H₀ N) = N := by
  classical
  ext a
  rw [restrict_mem, extend_mem]
  simp [a.property]

private theorem extend_restrict (M : MaxIndependent H₀.spanningCoe) :
    extendSet G H₀ (restrictSet G H₀ M.val) = M.val := by
  classical
  ext a
  rw [extend_mem]
  constructor
  · rintro (ha | ⟨ha, hm⟩)
    · exact isolated_mem H₀.spanningCoe M a fun b hab => ha (H₀.edge_vert hab)
    · exact (restrict_mem G H₀ M.val ⟨a, ha⟩).mp hm
  · intro hm
    by_cases ha : a ∈ H₀.verts
    · exact Or.inr ⟨ha, (restrict_mem G H₀ M.val ⟨a, ha⟩).mpr hm⟩
    · exact Or.inl ha

private theorem extend_mono {M N : Finset H₀.verts} (hMN : M ⊆ N) :
    extendSet G H₀ M ⊆ extendSet G H₀ N := by
  classical
  exact Finset.union_subset_union (Finset.image_subset_image hMN) (Finset.Subset.refl _)

def restrictMax (M : MaxIndependent H₀.spanningCoe) : MaxIndependent H₀.coe := by
  classical
  refine ⟨restrictSet G H₀ M.val, restrict_independent G H₀ M.property.1, ?_⟩
  intro N hN hMN a ha
  have hfull : M.val ⊆ extendSet G H₀ N := by
    rw [← extend_restrict G H₀ M]
    exact extend_mono G H₀ hMN
  have hback := M.property.2 _ (extend_independent G H₀ hN) hfull
  apply (restrict_mem G H₀ M.val a).mpr
  exact hback ((extend_mem G H₀ N a.val).mpr (Or.inr ⟨a.property, ha⟩))

def extendMax (N : MaxIndependent H₀.coe) : MaxIndependent H₀.spanningCoe := by
  classical
  refine ⟨extendSet G H₀ N.val, extend_independent G H₀ N.property.1, ?_⟩
  intro M hM hNM a ha
  by_cases haW : a ∈ H₀.verts
  · apply (extend_mem G H₀ N.val a).mpr
    right
    refine ⟨haW, ?_⟩
    apply N.property.2 (restrictSet G H₀ M) (restrict_independent G H₀ hM) _
      ((restrict_mem G H₀ M ⟨a, haW⟩).mpr ha)
    intro b hb
    exact (restrict_mem G H₀ M b).mpr
      (hNM ((extend_mem G H₀ N.val b.val).mpr (Or.inr ⟨b.property, hb⟩)))
  · exact (extend_mem G H₀ N.val a).mpr (Or.inl haW)

/-- Abstract bijection of maximal independent sets, adjoining every isolated
outside vertex. It is valid for a non-induced local subgraph. -/
def localMaxEquiv : MaxIndependent H₀.spanningCoe ≃ MaxIndependent H₀.coe where
  toFun := restrictMax G H₀
  invFun := extendMax G H₀
  left_inv M := Subtype.ext (extend_restrict G H₀ M)
  right_inv N := Subtype.ext (restrict_extend G H₀ N.val)

theorem old_complement_iff (M : MaxIndependent H₀.spanningCoe) (a : V) :
    a ∉ M.val ↔ a ∈ H₀.verts ∧
      a ∉ (localMaxEquiv G H₀ M).val.image Subtype.val := by
  classical
  constructor
  · intro ha
    have haW : a ∈ H₀.verts := by
      by_contra hn
      exact subgraph_apex_off_vertices G H₀ M a hn ha
    refine ⟨haW, ?_⟩
    rintro him
    obtain ⟨b, hb, he⟩ := Finset.mem_image.mp him
    exact ha (he ▸ (restrict_mem G H₀ M.val b).mp hb)
  · rintro ⟨haW, ha⟩ hm
    apply ha
    exact Finset.mem_image.mpr ⟨⟨a, haW⟩,
      (restrict_mem G H₀ M.val ⟨a, haW⟩).mpr hm, rfl⟩

abbrev LocalVertex := V ⊕ Option (MaxIndependent H₀.coe)

private def localAdj : LocalVertex G H₀ → LocalVertex G H₀ → Prop
  | .inl a, .inl b => G.Adj a b ∧ ¬ H₀.Adj a b
  | .inl _, .inr none => False
  | .inr none, .inl _ => False
  | .inl a, .inr (some M) => a ∈ H₀.verts ∧ a ∉ M.val.image Subtype.val
  | .inr (some M), .inl a => a ∈ H₀.verts ∧ a ∉ M.val.image Subtype.val
  | .inr none, .inr none => False
  | .inr none, .inr (some _) => True
  | .inr (some _), .inr none => True
  | .inr (some _), .inr (some _) => False

/-- Literal local-vertex version of S(G,H). -/
def localSuspensionGraph : SimpleGraph (LocalVertex G H₀) where
  Adj := localAdj G H₀
  symm.symm := by
    rintro (a | a) (b | b)
    · exact fun h => ⟨G.adj_symm h.1, fun h' => h.2 (H₀.adj_symm h')⟩
    · cases b <;> simp [localAdj]
    · cases a <;> simp [localAdj]
    · cases a <;> cases b <;> simp [localAdj]
  loopless.irrefl := by
    rintro (a | a)
    · simp [localAdj]
    · cases a <;> simp [localAdj]

/-- Exact gadget identification: old vertices and the central vertex are fixed;
the new apex bijection is the abstract maximal-extension equivalence. -/
def spanningLocalIso : suspensionGraph G H₀.spanningCoe ≃g localSuspensionGraph G H₀ where
  toEquiv := Equiv.sumCongr (Equiv.refl V) (Equiv.optionCongr (localMaxEquiv G H₀))
  map_rel_iff' := by
    rintro (a | a) (b | b)
    · rfl
    · cases b with
      | none => rfl
      | some M => exact (old_complement_iff G H₀ M a).symm
    · cases a with
      | none => rfl
      | some M => exact (old_complement_iff G H₀ M b).symm
    · cases a <;> cases b <;> rfl

end LocalSubgraph

/-- The consumed integral homology shift. H is an arbitrary spanning edge
subgraph: extra retained G-edges on the same vertices are explicitly allowed.
There is no topological or homological input hypothesis. -/
def reducedHomologyIso [Nonempty V] (hHG : H ≤ G) (q : ℕ) (_hq : 1 ≤ q) :
    (TauCeti.reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) (q + 1)).obj
      (TopCat.of (Ispace (suspensionGraph G H))) ≅
    (TauCeti.reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) q).obj
      (TopCat.of (Ispace G)) := by
  let R := ModuleCat.of ℤ ℤ
  letI : ContractibleSpace ↥(Coordinates.U G H) := Coordinates.contractible_U G H
  letI : ContractibleSpace ↥(Coordinates.O G H) := Coordinates.contractible_O G H
  have hδ : IsIso (TopCat.reducedMayerVietorisδ R
      (X := TopCat.of (Ispace (suspensionGraph G H)))
      (U := Coordinates.U G H) (V := Coordinates.O G H) (Coordinates.isOpen_U G H)
      (Coordinates.isOpen_O G H) (Coordinates.open_cover G H) q) :=
    TopCat.isIso_reducedMayerVietorisδ_of_contractible R
      (Coordinates.isOpen_U G H) (Coordinates.isOpen_O G H) (Coordinates.open_cover G H) q
  exact (TauCeti.reducedSingularHomologySuccIso R q).app
      (TopCat.of (Ispace (suspensionGraph G H))) ≪≫
    @asIso _ _ _ _ (TopCat.reducedMayerVietorisδ R
      (X := TopCat.of (Ispace (suspensionGraph G H)))
      (U := Coordinates.U G H) (V := Coordinates.O G H) (Coordinates.isOpen_U G H)
      (Coordinates.isOpen_O G H) (Coordinates.open_cover G H) q) hδ ≪≫
    (Coordinates.intersectionEquiv G H hHG).reducedSingularHomologyIso R q

/-- Subgraph input in Mathlib's local-vertex representation. Outside H.verts,
the spanning convention has isolated H-vertices; `subgraph_apex_off_vertices`
checks that none becomes a spurious neighbour of a new apex. -/
def subgraphReducedHomologyIso [Nonempty V] (H₀ : G.Subgraph) (q : ℕ) (hq : 1 ≤ q) :
    (TauCeti.reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) (q + 1)).obj
      (TopCat.of (Ispace (suspensionGraph G H₀.spanningCoe))) ≅
    (TauCeti.reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) q).obj
      (TopCat.of (Ispace G)) :=
  reducedHomologyIso G H₀.spanningCoe H₀.spanningCoe_le q hq

/-- The same consumed theorem for the literal local definition, transported by
the proved graph isomorphism and the existing coordinate homeomorphism.
The finite instance on H₀.verts may always be chosen with `Fintype.ofFinite`. -/
def localSubgraphReducedHomologyIso [Nonempty V] (H₀ : G.Subgraph)
    [Fintype H₀.verts] (q : ℕ) (hq : 1 ≤ q) :
    (TauCeti.reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) (q + 1)).obj
      (TopCat.of (Ispace (localSuspensionGraph G H₀))) ≅
    (TauCeti.reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) q).obj
      (TopCat.of (Ispace G)) :=
  ((graphIsoHomeomorph (spanningLocalIso G H₀)).toHomotopyEquiv.reducedSingularHomologyIso
    (ModuleCat.of ℤ ℤ) (q + 1)).symm ≪≫ subgraphReducedHomologyIso G H₀ q hq


end D5.S3.Geometry.FiniteGraphSubgraphSuspension
