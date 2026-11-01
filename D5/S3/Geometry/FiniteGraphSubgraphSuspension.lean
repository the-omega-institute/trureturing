/- GID: D5/S3/Geometry/FiniteGraphSubgraphSuspension
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteGraphSubgraphSuspension
   mirror-E: none(waiver:finite-graph-singular-homology)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Clique]
   utility: none
   digest: The maximal-independent-set star gadget for arbitrary subgraphs, with an explicit open-cover route to its integral homology shift. -/
import D5.S3.Geometry.FiniteCoordinateTruncation
import D5.S3.Topology.TauCeti.AlgebraicTopology.Singular.MayerVietoris.Reduced
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Subgraph suspension by an independent star cluster

This construction provides supporting machinery for the king-grid setting of
Question 32 in Carnero Bravo, arXiv:2505.06457v2. It does not settle that
question. In particular, H less than or equal to G never means that H is induced.

The geometric carrier and independence complex are the existing project ones.
The finite open cover, retraction and homotopies are constructed in coordinates.
The final homology step uses the existing TauCeti reduced Mayer--Vietoris API.
The graph splitting, suspension and star-cluster mechanisms have classical
sources in the work of Adamaszek, Barmak and Csorba. The corresponding Library
note identifies their original references and the scope of this construction.
-/

noncomputable section
open Set Topology CategoryTheory
open scoped BigOperators unitInterval ContinuousMap

namespace D5.S3.Geometry.FiniteGraphSubgraphSuspension

open FiniteConeCollapse FiniteGraphVertexSubstitution FiniteCoordinateTruncation

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Maximal, rather than maximum-cardinality, independent sets.  Finiteness is
used abstractly; no list of faces or vertex powerset is evaluated. -/
def MaxIndependent (H : SimpleGraph V) :=
  {M : Finset V // H.IsIndepSet (M : Set V) ∧
    ∀ N : Finset V, H.IsIndepSet (N : Set V) → M ⊆ N → N ⊆ M}

instance (H : SimpleGraph V) : Fintype (MaxIndependent H) := by
  classical
  unfold MaxIndependent
  infer_instance

instance (H : SimpleGraph V) : DecidableEq (MaxIndependent H) := Classical.decEq _

theorem maximal_extension (H : SimpleGraph V) (s : Finset V)
    (hs : H.IsIndepSet (s : Set V)) : ∃ M : MaxIndependent H, s ⊆ M.val := by
  classical
  let C : Set (Finset V) := {t | s ⊆ t ∧ H.IsIndepSet (t : Set V)}
  obtain ⟨M, hM⟩ := (Set.toFinite C).exists_maximal
    (show C.Nonempty from ⟨s, Finset.Subset.refl s, hs⟩)
  refine ⟨⟨M, hM.1.2, ?_⟩, hM.1.1⟩
  intro N hN hMN
  exact hM.2 ⟨hM.1.1.trans hMN, hN⟩ hMN

instance (H : SimpleGraph V) : Nonempty (MaxIndependent H) := by
  obtain ⟨M, _⟩ := maximal_extension H ∅ (by simp [SimpleGraph.isIndepSet_iff])
  exact ⟨M⟩

theorem isolated_mem (H : SimpleGraph V) (M : MaxIndependent H) (a : V)
    (ha : ∀ b, ¬ H.Adj a b) : a ∈ M.val := by
  classical
  have hi : H.IsIndepSet ((insert a M.val : Finset V) : Set V) := by
    intro x hx y hy hxy h
    simp only [Finset.mem_coe, Finset.mem_insert] at hx hy
    rcases hx with rfl | hx
    · exact ha y h
    rcases hy with rfl | hy
    · exact ha x (H.adj_symm h)
    · exact M.property.1 hx hy hxy h
  exact M.property.2 _ hi (Finset.subset_insert _ _) (Finset.mem_insert_self _ _)

abbrev Vertex (H : SimpleGraph V) := V ⊕ Option (MaxIndependent H)
def old {H : SimpleGraph V} (a : V) : Vertex H := Sum.inl a
def hub (H : SimpleGraph V) : Vertex H := Sum.inr none
def apex {H : SimpleGraph V} (M : MaxIndependent H) : Vertex H := Sum.inr (some M)

private def gadgetAdj (G H : SimpleGraph V) : Vertex H → Vertex H → Prop
  | .inl a, .inl b => G.Adj a b ∧ ¬ H.Adj a b
  | .inl _, .inr none => False
  | .inr none, .inl _ => False
  | .inl a, .inr (some M) => a ∉ M.val
  | .inr (some M), .inl a => a ∉ M.val
  | .inr none, .inr none => False
  | .inr none, .inr (some _) => True
  | .inr (some _), .inr none => True
  | .inr (some _), .inr (some _) => False

/-- Retain G minus H; add a hub and one independent apex for each maximal
H-independent set, adjacent precisely to its old complement and the hub. -/
def suspensionGraph (G H : SimpleGraph V) : SimpleGraph (Vertex H) where
  Adj := gadgetAdj G H
  symm.symm := by
    rintro (a | a) (b | b)
    · exact fun h => ⟨G.adj_symm h.1, fun h' => h.2 (H.adj_symm h')⟩
    · cases b <;> simp [gadgetAdj]
    · cases a <;> simp [gadgetAdj]
    · cases a <;> cases b <;> simp [gadgetAdj]
  loopless.irrefl := by
    rintro (a | a)
    · simp [gadgetAdj]
    · cases a <;> simp [gadgetAdj]

@[simp] theorem adj_apex_old (G H : SimpleGraph V) (a : V) (M : MaxIndependent H) :
    (suspensionGraph G H).Adj (apex M) (old a) ↔ a ∉ M.val := Iff.rfl
/-- The full-vertex convention adds no unwanted old neighbours outside the
local vertex set of an arbitrary subgraph. No inducedness is used. -/
theorem subgraph_apex_off_vertices (G : SimpleGraph V) (H : G.Subgraph)
    (M : MaxIndependent H.spanningCoe) (a : V) (ha : a ∉ H.verts) :
    ¬ (suspensionGraph G H.spanningCoe).Adj (old a) (apex M) := by
  apply not_not.mpr
  apply isolated_mem H.spanningCoe M a
  intro b hab
  exact ha (H.edge_vert hab)

variable (G H : SimpleGraph V)

/-- Closed star of a vertex in a flag independence complex. -/
def closedStar (a : Vertex H) : PreAbstractSimplicialComplex (Vertex H) where
  faces := {s | s.Nonempty ∧ (suspensionGraph G H).IsIndepSet (s : Set (Vertex H)) ∧
    ∀ b ∈ s, ¬ (suspensionGraph G H).Adj a b}
  isRelLowerSet_faces := by
    rintro s ⟨hne, hi, ha⟩
    exact ⟨hne, fun t hts ht => ⟨ht, hi.mono (fun _ hx => hts hx),
      fun b hb => ha b (hts hb)⟩⟩

def starA : PreAbstractSimplicialComplex (Vertex H) := closedStar G H (hub H)

def starB : PreAbstractSimplicialComplex (Vertex H) where
  faces := {s | ∃ M : MaxIndependent H, s ∈ closedStar G H (apex M)}
  isRelLowerSet_faces := by
    rintro s ⟨M, hs⟩
    exact ⟨hs.1, fun t hts ht =>
      ⟨M, ((closedStar G H (apex M)).isRelLowerSet_faces hs).2 hts ht⟩⟩

theorem starA_iff (s : Finset (Vertex H)) :
    s ∈ starA G H ↔ s.Nonempty ∧
      (suspensionGraph G H).IsIndepSet (s : Set (Vertex H)) ∧
      ∀ M : MaxIndependent H, apex M ∉ s := by
  change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
  constructor
  · rintro ⟨hn, hi, hh⟩
    exact ⟨hn, hi, fun M hm => hh (apex M) hm trivial⟩
  · rintro ⟨hn, hi, hm⟩
    refine ⟨hn, hi, ?_⟩
    rintro (a | a) ha
    · exact False.elim
    · cases a with
      | none => exact False.elim
      | some M => exact (hm M ha).elim

theorem cover_faces :
    (independenceComplex (suspensionGraph G H)).toPreAbstractSimplicialComplex =
      starA G H ⊔ starB G H := by
  classical
  ext s
  constructor
  · rintro ⟨hn, hi⟩
    by_cases hm : ∃ M : MaxIndependent H, apex M ∈ s
    · obtain ⟨M, hM⟩ := hm
      right
      refine ⟨M, hn, hi, ?_⟩
      intro b hb hab
      exact hi hM hb ((suspensionGraph G H).ne_of_adj hab) hab
    · left
      exact (starA_iff G H s).mpr ⟨hn, hi, by simpa using hm⟩
  · rintro (hs | ⟨M, hs⟩)
    · exact ⟨hs.1, hs.2.1⟩
    · exact ⟨hs.1, hs.2.1⟩

def oldEmbedding : V ↪ Vertex H := ⟨old, Sum.inl_injective⟩

/-- Exact intersection, including all retained G-edges on V(H). -/
theorem intersection_faces (hHG : H ≤ G) :
    starA G H ⊓ starB G H =
      (independenceComplex G).toPreAbstractSimplicialComplex.map (oldEmbedding H) := by
  classical
  ext s
  constructor
  · rintro ⟨hA, M, hB⟩
    have hA' := (starA_iff G H s).mp hA
    have hOld : ∀ b ∈ s, ∃ a, old a = b := by
      rintro (a | a) ha
      · exact ⟨a, rfl⟩
      · cases a with
        | none => exact (hB.2.2 (hub H) ha trivial).elim
        | some N => exact (hA'.2.2 N ha).elim
    let t := s.preimage (oldEmbedding H) (oldEmbedding H).injective.injOn
    have ht : t.image (oldEmbedding H) = s := by
      ext b
      constructor
      · rintro hb
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
        exact Finset.mem_preimage.mp ha
      · intro hb
        obtain ⟨a, rfl⟩ := hOld b hb
        exact Finset.mem_image.mpr ⟨a, Finset.mem_preimage.mpr hb, rfl⟩
    refine ⟨t, ⟨?_, ?_⟩, ht⟩
    · exact Finset.image_nonempty.mp (ht.symm ▸ hA'.1)
    · intro a ha b hb hab hG
      have has : old a ∈ s := Finset.mem_preimage.mp ha
      have hbs : old b ∈ s := Finset.mem_preimage.mp hb
      have haM : a ∈ M.val := by
        simpa only [adj_apex_old, not_not] using hB.2.2 (old a) has
      have hbM : b ∈ M.val := by
        simpa only [adj_apex_old, not_not] using hB.2.2 (old b) hbs
      by_cases hH : H.Adj a b
      · exact M.property.1 haM hbM hab hH
      · exact hA'.2.1 has hbs (fun h => hab (Sum.inl_injective h)) ⟨hG, hH⟩
  · rintro ⟨t, ⟨htn, hti⟩, rfl⟩
    obtain ⟨M, htM⟩ := maximal_extension H t (by
      intro a ha b hb hab hH
      exact hti ha hb hab (hHG hH))
    have hi : (suspensionGraph G H).IsIndepSet
        ((t.image (oldEmbedding H)) : Set (Vertex H)) := by
      rintro u hu v hv huv hadj
      obtain ⟨a, ha, hau⟩ := Finset.mem_image.mp hu
      obtain ⟨b, hb, hbv⟩ := Finset.mem_image.mp hv
      subst u
      subst v
      exact hti ha hb (fun h => huv (congrArg old h)) hadj.1
    refine ⟨(starA_iff G H _).mpr ⟨htn.image _, hi, ?_⟩, M, htn.image _, hi, ?_⟩
    · intro N hN
      obtain ⟨a, _, he⟩ := Finset.mem_image.mp hN
      cases he
    · intro b hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      exact not_not.mpr (htM ha)

theorem closedStar_cone (a : Vertex H) (s : Finset (Vertex H))
    (hs : s ∈ closedStar G H a) : insert a s ∈ closedStar G H a := by
  refine ⟨Finset.insert_nonempty _ _, ?_, ?_⟩
  · intro b hb c hc hbc hadj
    simp only [Finset.mem_coe, Finset.mem_insert] at hb hc
    rcases hb with rfl | hb
    · rcases hc with rfl | hc
      · exact (suspensionGraph G H).irrefl hadj
      · exact hs.2.2 c hc hadj
    · rcases hc with rfl | hc
      · exact hs.2.2 b hb ((suspensionGraph G H).adj_symm hadj)
      · exact hs.2.1 hb hc hbc hadj
  · intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact (suspensionGraph G H).irrefl
    · exact hs.2.2 b hb

def starACone : ConePair (Vertex H) where
  ambient := (independenceComplex (suspensionGraph G H)).toPreAbstractSimplicialComplex
  cone := starA G H
  inclusion := fun _ hs => ⟨hs.1, hs.2.1⟩
  apex := hub H
  apex_face := by
    refine ⟨Finset.singleton_nonempty _,
      ((independenceComplex (suspensionGraph G H)).singleton_mem (hub H)).2, ?_⟩
    intro b hb
    obtain rfl := Finset.mem_singleton.mp hb
    exact (suspensionGraph G H).irrefl
  cone_face := closedStar_cone G H (hub H)

theorem closedStar_realization_iff (a : Vertex H) (x : Vertex H → ℝ) :
    x ∈ realization (closedStar G H a) ↔ Probability x ∧
      Avoid (suspensionGraph G H) x ∧ ∀ b, (suspensionGraph G H).Adj a b → x b = 0 := by
  constructor
  · rintro ⟨s, ⟨hn, hi, ha⟩, hx⟩
    have hk := (realization_iff (suspensionGraph G H) x).mp ⟨s, ⟨hn, hi⟩, hx⟩
    refine ⟨hk.1, hk.2, ?_⟩
    rw [← faceSimplex_eq_convexHull] at hx
    intro b hab
    exact hx.2.2 b (fun hb => ha b hb hab)
  · rintro ⟨hp, hi, ha⟩
    refine ⟨support x, ⟨support_nonempty hp,
      (independent_support_iff _ _).mpr hi, ?_⟩, ?_⟩
    · intro b hb hab
      exact (mem_support x b).mp hb (ha b hab)
    · rw [← faceSimplex_eq_convexHull]
      exact ⟨hp.1, hp.2, fun b hb => by simpa using hb⟩

namespace Coordinates
abbrev X := Ispace (suspensionGraph G H)

def mass (x : Vertex H → ℝ) : ℝ := ∑ M : MaxIndependent H, x (apex M)

def bad (M : MaxIndependent H) (x : Vertex H → ℝ) : ℝ :=
  x (hub H) + ∑ a : V, if a ∈ M.val then 0 else x (old a)

private theorem allMax_nonempty : (Finset.univ : Finset (MaxIndependent H)).Nonempty :=
  Finset.univ_nonempty

def delta (x : Vertex H → ℝ) : ℝ :=
  Finset.univ.inf' (allMax_nonempty H) fun M => bad H M x

theorem bad_nonneg {x : Vertex H → ℝ} (hx : ∀ a, 0 ≤ x a)
    (M : MaxIndependent H) : 0 ≤ bad H M x := by
  apply add_nonneg (hx _)
  exact Finset.sum_nonneg fun a _ => by split_ifs <;> first | exact le_rfl | exact hx _

theorem hub_le_bad {x : Vertex H → ℝ} (hx : ∀ a, 0 ≤ x a)
    (M : MaxIndependent H) : x (hub H) ≤ bad H M x := by
  have h : 0 ≤ ∑ a : V, if a ∈ M.val then 0 else x (old a) :=
    Finset.sum_nonneg fun a _ => by split_ifs <;> first | exact le_rfl | exact hx _
  dsimp [bad]; linarith

theorem old_le_bad {x : Vertex H → ℝ} (hx : ∀ a, 0 ≤ x a)
    (M : MaxIndependent H) (a : V) (ha : a ∉ M.val) : x (old a) ≤ bad H M x := by
  have hs : x (old a) ≤ ∑ b : V, if b ∈ M.val then 0 else x (old b) := by
    simpa only [if_neg ha] using
      (Finset.single_le_sum (f := fun b : V => if b ∈ M.val then 0 else x (old b))
        (fun b _ => by split_ifs <;> first | exact le_rfl | exact hx _) (Finset.mem_univ a))
  dsimp [bad]; linarith [hx (hub H)]

theorem delta_nonneg {x : Vertex H → ℝ} (hx : ∀ a, 0 ≤ x a) : 0 ≤ delta H x :=
  Finset.le_inf' _ _ fun M _ => bad_nonneg H hx M

theorem delta_le (M : MaxIndependent H) (x : Vertex H → ℝ) :
    delta H x ≤ bad H M x := Finset.inf'_le _ (Finset.mem_univ M)

theorem delta_witness (x : Vertex H → ℝ) :
    ∃ M : MaxIndependent H, delta H x = bad H M x := by
  obtain ⟨M, _, hM⟩ := Finset.exists_mem_eq_inf' (allMax_nonempty H) (fun M => bad H M x)
  exact ⟨M, hM⟩

theorem continuous_mass : Continuous (mass H) :=
  continuous_finsetSum _ fun M _ => continuous_apply (apex M)

theorem continuous_bad (M : MaxIndependent H) : Continuous (bad H M) := by
  apply (continuous_apply (hub H)).add
  apply continuous_finsetSum
  intro a _
  by_cases ha : a ∈ M.val
  · simpa [ha] using (continuous_const : Continuous (fun _ : Vertex H → ℝ => (0 : ℝ)))
  · simpa [ha] using (continuous_apply (old a) : Continuous (fun x : Vertex H → ℝ => x (old a)))

theorem continuous_delta : Continuous (delta H) :=
  Continuous.finset_inf'_apply _ fun M _ => continuous_bad H M

theorem bad_mix (M : MaxIndependent H) (t : ℝ) (x y : Vertex H → ℝ) :
    bad H M (mix t x y) = (1 - t) * bad H M x + t * bad H M y := by
  have hs : (∑ a : V, if a ∈ M.val then 0 else mix t x y (old a)) =
      (1 - t) * (∑ a : V, if a ∈ M.val then 0 else x (old a)) +
        t * (∑ a : V, if a ∈ M.val then 0 else y (old a)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a ∈ M.val <;> simp [ha, mix]
  unfold bad
  rw [hs]
  unfold mix
  ring

theorem mass_mix (t : ℝ) (x y : Vertex H → ℝ) :
    mass H (mix t x y) = (1 - t) * mass H x + t * mass H y := by
  simp only [mass, mix, Finset.sum_add_distrib, ← Finset.mul_sum]

theorem bad_zero {x : Vertex H → ℝ} (hx : ∀ a, 0 ≤ x a)
    (M : MaxIndependent H) :
    bad H M x = 0 ↔ x (hub H) = 0 ∧ ∀ a ∉ M.val, x (old a) = 0 := by
  constructor
  · intro h
    refine ⟨le_antisymm (by linarith [hub_le_bad H hx M]) (hx _), ?_⟩
    intro a ha
    exact le_antisymm (by linarith [old_le_bad H hx M a ha]) (hx _)
  · rintro ⟨hh, ho⟩
    simp only [bad, hh, zero_add]
    apply Finset.sum_eq_zero
    intro a _
    split_ifs with ha
    · rfl
    · exact ho a ha

theorem delta_zero_iff {x : Vertex H → ℝ} (hx : ∀ a, 0 ≤ x a) :
    delta H x = 0 ↔ ∃ M : MaxIndependent H,
      x (hub H) = 0 ∧ ∀ a ∉ M.val, x (old a) = 0 := by
  constructor
  · intro hd
    obtain ⟨M, hM⟩ := delta_witness H x
    exact ⟨M, (bad_zero H hx M).mp (hM.symm.trans hd)⟩
  · rintro ⟨M, hM⟩
    exact le_antisymm ((delta_le H M x).trans ((bad_zero H hx M).mpr hM).le)
      (delta_nonneg H hx)

theorem starB_realization_iff (x : Vertex H → ℝ) :
    x ∈ realization (starB G H) ↔
      x ∈ realization (independenceComplex (suspensionGraph G H)).toPreAbstractSimplicialComplex ∧
        delta H x = 0 := by
  constructor
  · rintro ⟨s, ⟨M, hs⟩, hx⟩
    have hc := (closedStar_realization_iff G H (apex M) x).mp ⟨s, hs, hx⟩
    exact ⟨(realization_iff _ _).mpr ⟨hc.1, hc.2.1⟩,
      (delta_zero_iff H hc.1.1).mpr
        ⟨M, hc.2.2 (hub H) trivial, fun a ha => hc.2.2 (old a) ha⟩⟩
  · rintro ⟨hk, hd⟩
    have hc := (realization_iff _ _).mp hk
    obtain ⟨M, hh, ho⟩ := (delta_zero_iff H hc.1.1).mp hd
    have hm : x ∈ realization (closedStar G H (apex M)) := by
      apply (closedStar_realization_iff G H (apex M) x).mpr
      refine ⟨hc.1, hc.2, ?_⟩
      rintro (a | a) hab
      · exact ho a hab
      · cases a with
        | none => exact hh
        | some N => exact hab.elim
    obtain ⟨s, hs, hx⟩ := hm
    exact ⟨s, ⟨M, hs⟩, hx⟩

theorem bad_zero_of_apex (x : X G H) (M : MaxIndependent H)
    (hM : x.val (apex M) ≠ 0) : bad H M x.val = 0 := by
  apply (bad_zero H (probability _ x).1 M).mpr
  constructor
  · exact (avoid _ x (hub H) (apex M) trivial).resolve_right hM
  · intro a ha
    exact (avoid _ x (old a) (apex M) ha).resolve_right hM

theorem total (x : X G H) :
    (∑ a : V, x.val (old a)) + x.val (hub H) + mass H x.val = 1 := by
  have hs := (probability _ x).2
  simpa [mass, old, hub, apex, Fintype.sum_sum_type, Fintype.sum_option, add_assoc] using hs

def epsilon : ℝ := 1 / (4 * ((Fintype.card (Vertex H) : ℝ) + 1))

theorem epsilon_pos : 0 < epsilon H := by unfold epsilon; positivity

theorem card_epsilon : (Fintype.card (Vertex H) : ℝ) * epsilon H < 1 / 4 := by
  unfold epsilon
  rw [← mul_div_assoc, mul_one]
  apply (div_lt_iff₀ (by positivity : 0 < 4 * ((Fintype.card (Vertex H) : ℝ) + 1))).mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card (Vertex H))]

/-- Both are genuinely open subsets of the actual realization. -/
abbrev U : Set (X G H) := {x | mass H x.val < 1 / 2}
abbrev O : Set (X G H) := {x | delta H x.val < epsilon H}

theorem isOpen_U : IsOpen (U G H) :=
  isOpen_lt ((continuous_mass H).comp continuous_subtype_val) continuous_const
theorem isOpen_O : IsOpen (O G H) :=
  isOpen_lt ((continuous_delta H).comp continuous_subtype_val) continuous_const

theorem open_cover : U G H ∪ O G H = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : mass H x.val < 1 / 2
  · exact Or.inl hx
  · right
    have hp : 0 < mass H x.val := by linarith
    obtain ⟨M, _, hM⟩ := (Finset.sum_pos_iff_of_nonneg
      (fun M _ => (probability _ x).1 (apex M))).mp hp
    have hd : delta H x.val = 0 := le_antisymm
      ((delta_le H M x.val).trans (bad_zero_of_apex G H x M hM.ne').le)
      (delta_nonneg H (probability _ x).1)
    simpa [O, hd] using epsilon_pos H

def liftOld (z : V → ℝ) : Vertex H → ℝ
  | .inl a => z a
  | .inr _ => 0

theorem probability_liftOld {z : V → ℝ} (hz : Probability z) : Probability (liftOld H z) := by
  refine ⟨?_, ?_⟩
  · rintro (a | a)
    · exact hz.1 a
    · exact le_rfl
  · simpa [liftOld, Fintype.sum_sum_type, Fintype.sum_option] using hz.2

theorem continuous_liftOld : Continuous (liftOld H) := by
  apply continuous_pi
  rintro (a | a)
  · exact continuous_apply a
  · exact continuous_const

theorem avoid_liftOld {z : V → ℝ} (hz : Avoid G z) :
    Avoid (suspensionGraph G H) (liftOld H z) := by
  rintro (a | a) (b | b) hab
  · exact hz a b hab.1
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact Or.inl rfl

theorem delta_liftOld (hHG : H ≤ G) {z : V → ℝ} (hz : Probability z) (hi : Avoid G z) :
    delta H (liftOld H z) = 0 := by
  obtain ⟨M, hM⟩ := maximal_extension H (support z) (by
    intro a ha b hb hab hH
    exact (independent_support_iff G z).mpr hi ha hb hab (hHG hH))
  apply (delta_zero_iff H (probability_liftOld H hz).1).mpr
  refine ⟨M, rfl, ?_⟩
  intro a ha
  by_contra hz
  exact ha (hM ((mem_support z a).mpr hz))

theorem mass_liftOld (z : V → ℝ) : mass H (liftOld H z) = 0 := by simp [mass, liftOld, apex]

/- The next two constructors only package maps and homotopies whose coordinate
membership proofs are provided explicitly below. They assume no deformation
retraction or homology statement. -/
abbrev Region (p : (Vertex H → ℝ) → Prop) := {x : X G H // p x.val}

def regionMap {T : Type*} [TopologicalSpace T] (p : (Vertex H → ℝ) → Prop)
    (f : T → Vertex H → ℝ) (hc : Continuous f)
    (hk : ∀ x, Probability (f x) ∧ Avoid (suspensionGraph G H) (f x))
    (hp : ∀ x, p (f x)) : C(T, Region G H p) where
  toFun x := ⟨⟨f x, (realization_iff _ _).mpr (hk x)⟩, hp x⟩
  continuous_toFun := (hc.subtype_mk _).subtype_mk _

def regionStraight {T : Type*} [TopologicalSpace T] (p : (Vertex H → ℝ) → Prop)
    (f g : C(T, Region G H p))
    (hi : ∀ t : I, ∀ x, Avoid (suspensionGraph G H) (mix t (f x).val.val (g x).val.val))
    (hp : ∀ t : I, ∀ x, p (mix t (f x).val.val (g x).val.val)) : f.Homotopy g where
  toFun z := ⟨⟨mix z.1 (f z.2).val.val (g z.2).val.val,
    (realization_iff _ _).mpr ⟨probability_mix (probability _ (f z.2).val)
      (probability _ (g z.2).val) z.1, hi z.1 z.2⟩⟩, hp z.1 z.2⟩
  continuous_toFun := ((continuous_mix
    (continuous_subtype_val.comp (continuous_subtype_val.comp f.continuous))
    (continuous_subtype_val.comp (continuous_subtype_val.comp g.continuous))).subtype_mk _).subtype_mk _
  map_zero_left x := Subtype.ext (Subtype.ext (mix_zero _ _))
  map_one_left x := Subtype.ext (Subtype.ext (mix_one _ _))

theorem delta_mix_bound {x y : Vertex H → ℝ} (M : MaxIndependent H)
    (hy : bad H M y = 0) (t : I) :
    delta H (mix t x y) ≤ (1 - (t : ℝ)) * bad H M x := by
  calc
    _ ≤ bad H M (mix t x y) := delta_le H M _
    _ = _ := by rw [bad_mix, hy]; ring

theorem mass_mix_lt {x y : Vertex H → ℝ} (hx : mass H x < 1 / 2)
    (hn : 0 ≤ mass H x) (hy : mass H y = 0) (t : I) :
    mass H (mix t x y) < 1 / 2 := by
  rw [mass_mix, hy, mul_zero, add_zero]
  exact (mul_le_of_le_one_left hn (by linarith [t.2.1])).trans_lt hx

theorem delta_mix_lt {x y : Vertex H → ℝ} (hx : ∀ a, 0 ≤ x a)
    (hd : delta H x < epsilon H) (M : MaxIndependent H)
    (hM : delta H x = bad H M x) (hy : bad H M y = 0) (t : I) :
    delta H (mix t x y) < epsilon H := by
  apply (delta_mix_bound H M hy t).trans_lt
  rw [← hM]
  exact (mul_le_of_le_one_left (delta_nonneg H hx) (by linarith [t.2.1])).trans_lt hd

def eraseA (x : Vertex H → ℝ) : Vertex H → ℝ
  | .inl a => x (old a)
  | .inr none => x (hub H)
  | .inr (some _) => 0

theorem eraseA_nonneg (x : X G H) : ∀ a, 0 ≤ eraseA H x.val a := by
  rintro (a | a)
  · exact (probability _ x).1 _
  · cases a
    · exact (probability _ x).1 _
    · exact le_rfl

theorem eraseA_support (x : X G H) (a : Vertex H) (ha : x.val a = 0) :
    FiniteCoordinateTruncation.normalize (eraseA H x.val) a = 0 := by
  apply FiniteCoordinateTruncation.normalize_zero
  rcases a with a | a
  · exact ha
  · cases a
    · exact ha
    · rfl

theorem eraseA_sum (x : X G H) : ∑ a, eraseA H x.val a = 1 - mass H x.val := by
  have ht := total G H x
  simpa [eraseA, old, hub, Fintype.sum_sum_type, Fintype.sum_option] using
    (show (∑ a : V, x.val (old a)) + x.val (hub H) = 1 - mass H x.val by linarith)

theorem continuous_eraseA : Continuous (eraseA H) := by
  apply continuous_pi
  rintro (a | a)
  · exact continuous_apply _
  · cases a
    · exact continuous_apply _
    · exact continuous_const

def aMap : C(↥(U G H), ↥(U G H)) :=
  regionMap G H (fun x => mass H x < 1 / 2)
    (fun x => FiniteCoordinateTruncation.normalize (eraseA H x.val.val))
    (continuous_normalize ((continuous_eraseA H).comp
      (continuous_subtype_val.comp continuous_subtype_val)) (fun x => by
        rw [eraseA_sum]; exact (show 0 < 1 - mass H x.val.val by linarith [show mass H x.val.val < 1 / 2 from x.property]).ne'))
    (fun x => ⟨probability_normalize (eraseA_nonneg G H x.val) (by
      rw [eraseA_sum]; linarith [show mass H x.val.val < 1 / 2 from x.property]),
      avoid_of_support (avoid _ x.val) (eraseA_support G H x.val)⟩)
    (fun x => by simp [mass, FiniteCoordinateTruncation.normalize, eraseA, apex])

theorem aMap_mass (x : U G H) : mass H (aMap G H x).val.val = 0 := by
  change mass H (FiniteCoordinateTruncation.normalize (eraseA H x.val.val)) = 0
  simp [mass, FiniteCoordinateTruncation.normalize, eraseA, apex]

def aFirst : (ContinuousMap.id ↥(U G H)).Homotopy (aMap G H) :=
  regionStraight G H (fun x => mass H x < 1 / 2) _ _
    (fun t x => avoid_mix_of_support (avoid _ x.val) (eraseA_support G H x.val) t)
    (fun t x => mass_mix_lt H x.property
      (Finset.sum_nonneg fun _ _ => (probability _ x.val).1 _) (aMap_mass G H x) t)

def hubPoint : U G H :=
  ⟨vertex (suspensionGraph G H) (hub H), by simp [U, mass, vertex, apex, hub, Pi.single_apply]⟩

theorem no_apex_avoid_hub_mix {x : Vertex H → ℝ}
    (hp : Probability x) (hi : Avoid (suspensionGraph G H) x)
    (hm : ∀ M : MaxIndependent H, x (apex M) = 0) (t : I) :
    Avoid (suspensionGraph G H) (mix t x (Pi.single (hub H) 1)) := by
  have hA : x ∈ realization (starA G H) := by
    apply (closedStar_realization_iff G H (hub H) x).mpr
    refine ⟨hp, hi, ?_⟩
    rintro (a | a) hab
    · exact hab.elim
    · cases a with
      | none => exact hab.elim
      | some M => exact hm M
  obtain ⟨s, hs, hx⟩ := hA
  rw [← faceSimplex_eq_convexHull] at hx
  have hc := (starACone G H).cone_face s hs
  have hp' := probability_mix hp
    (probability (suspensionGraph G H) (vertex (suspensionGraph G H) (hub H))) t
  have hface : mix t x (Pi.single (hub H) 1) ∈ faceSimplex (insert (hub H) s) := by
    refine ⟨hp'.1, hp'.2, ?_⟩
    intro b hb
    have hbh : b ≠ hub H := by
      intro h
      apply hb
      rw [h]
      exact Finset.mem_insert_self _ _
    have hbs : b ∉ s := fun h => hb (Finset.mem_insert_of_mem h)
    simp [mix, hx.2.2 b hbs, Pi.single_apply, hbh, Ne.symm hbh]
  have hreal : mix t x (Pi.single (hub H) 1) ∈ realization
      (independenceComplex (suspensionGraph G H)).toPreAbstractSimplicialComplex := by
    refine ⟨insert (hub H) s, ?_, ?_⟩
    · rw [cover_faces G H]
      exact Or.inl hc
    · rwa [← faceSimplex_eq_convexHull]
  exact ((realization_iff (suspensionGraph G H) _).mp hreal).2

def aSecond : (aMap G H).Homotopy (ContinuousMap.const _ (hubPoint G H)) :=
  regionStraight G H (fun x => mass H x < 1 / 2) _ _
    (fun t x => no_apex_avoid_hub_mix G H (probability _ (aMap G H x).val)
      (avoid _ (aMap G H x).val)
      (fun M => by simp [aMap, regionMap, FiniteCoordinateTruncation.normalize, eraseA, apex]) t)
    (fun t x => by
      change mass H (mix t (aMap G H x).val.val (hubPoint G H).val.val) < 1 / 2
      rw [mass_mix, aMap_mass]
      simp [hubPoint, mass, vertex, apex, hub, Pi.single_apply])

theorem contractible_U : ContractibleSpace ↥(U G H) :=
  (contractible_iff_id_nullhomotopic _).mpr
    ⟨hubPoint G H, ⟨(aFirst G H).trans (aSecond G H)⟩⟩

def cutCoords (x : Vertex H → ℝ) : Vertex H → ℝ := FiniteCoordinateTruncation.normalize (cut (epsilon H) x)

private theorem cut_sum_lower (x : X G H) :
    (3 / 4 : ℝ) < ∑ a, cut (epsilon H) x.val a := by
  have hb := cut_sum_bound (probability _ x) (epsilon H)
  have he := card_epsilon H
  linarith

theorem cut_sum_pos (x : X G H) : 0 < ∑ a, cut (epsilon H) x.val a :=
  lt_trans (by norm_num : (0 : ℝ) < 3 / 4) (cut_sum_lower G H x)

theorem cut_probability (x : X G H) : Probability (cutCoords H x.val) :=
  probability_normalize (cut_nonneg _ _) (cut_sum_pos G H x)

theorem cut_support (x : X G H) (a : Vertex H) (ha : x.val a = 0) :
    cutCoords H x.val a = 0 :=
  FiniteCoordinateTruncation.normalize_zero (cut_zero (epsilon_pos H).le ha)

theorem cut_avoid (x : X G H) : Avoid (suspensionGraph G H) (cutCoords H x.val) :=
  avoid_of_support (avoid _ x) (cut_support G H x)

theorem continuous_cutCoords : Continuous (fun x : X G H => cutCoords H x.val) :=
  continuous_normalize (continuous_cut continuous_subtype_val continuous_const)
    fun x => (cut_sum_pos G H x).ne'

theorem cut_bad_zero (x : X G H) (M : MaxIndependent H)
    (hM : bad H M x.val < epsilon H) : bad H M (cutCoords H x.val) = 0 := by
  apply (bad_zero H (cut_probability G H x).1 M).mpr
  constructor
  · exact FiniteCoordinateTruncation.normalize_zero (cut_eq_zero ((hub_le_bad H (probability _ x).1 M).trans hM.le))
  · intro a ha
    exact FiniteCoordinateTruncation.normalize_zero (cut_eq_zero ((old_le_bad H (probability _ x).1 M a ha).trans hM.le))

theorem cut_delta_zero (x : O G H) : delta H (cutCoords H x.val.val) = 0 := by
  obtain ⟨M, hM⟩ := delta_witness H x.val.val
  exact le_antisymm ((delta_le H M _).trans (cut_bad_zero G H x.val M
    (hM ▸ x.property)).le) (delta_nonneg H (cut_probability G H x.val).1)

def weight (M : MaxIndependent H) (x : Vertex H → ℝ) : ℝ :=
  max (epsilon H - bad H M x) 0

def apexRaw (x : Vertex H → ℝ) : Vertex H → ℝ
  | .inl _ => 0
  | .inr none => 0
  | .inr (some M) => weight H M x

theorem apexRaw_nonneg (x : Vertex H → ℝ) : ∀ a, 0 ≤ apexRaw H x a := by
  rintro (a | a)
  · exact le_rfl
  · cases a
    · exact le_rfl
    · exact le_max_right _ _

private theorem apexRaw_sum_lower (x : O G H) :
    epsilon H - delta H x.val.val ≤ ∑ a, apexRaw H x.val.val a := by
  obtain ⟨M, hM⟩ := delta_witness H x.val.val
  calc
    epsilon H - delta H x.val.val = epsilon H - bad H M x.val.val := by rw [hM]
    _ ≤ max (epsilon H - bad H M x.val.val) 0 := le_max_left _ _
    _ ≤ ∑ a, apexRaw H x.val.val a :=
      Finset.single_le_sum (fun a _ => apexRaw_nonneg H x.val.val a) (Finset.mem_univ (apex M))

theorem apexRaw_sum_pos (x : O G H) : 0 < ∑ a, apexRaw H x.val.val a :=
  (sub_pos.mpr x.property).trans_le (apexRaw_sum_lower G H x)

theorem continuous_apexRaw : Continuous (apexRaw H) := by
  apply continuous_pi
  rintro (a | a)
  · exact continuous_const
  · cases a with
    | none => exact continuous_const
    | some M => exact (continuous_const.sub (continuous_bad H M)).max continuous_const

def weightCoords (x : Vertex H → ℝ) := FiniteCoordinateTruncation.normalize (apexRaw H x)

theorem weight_probability (x : O G H) : Probability (weightCoords H x.val.val) :=
  probability_normalize (apexRaw_nonneg H _) (apexRaw_sum_pos G H x)

theorem weight_old (x : Vertex H → ℝ) (a : V) : weightCoords H x (old a) = 0 := by
  simp [weightCoords, FiniteCoordinateTruncation.normalize, apexRaw, old]
theorem weight_hub (x : Vertex H → ℝ) : weightCoords H x (hub H) = 0 := by
  simp [weightCoords, FiniteCoordinateTruncation.normalize, apexRaw, hub]

theorem apex_supported_avoid {x : Vertex H → ℝ}
    (ho : ∀ a, x (old a) = 0) (hh : x (hub H) = 0) :
    Avoid (suspensionGraph G H) x := by
  rintro (a | a) (b | b) hab
  · exact Or.inl (ho a)
  · exact Or.inl (ho a)
  · exact Or.inr (ho b)
  · cases a <;> cases b <;> simp only [suspensionGraph, gadgetAdj] at hab
    · exact Or.inl hh
    · exact Or.inr hh

theorem weight_bad_zero (M : MaxIndependent H) (x : O G H) :
    bad H M (weightCoords H x.val.val) = 0 :=
  (bad_zero H (weight_probability G H x).1 M).mpr
    ⟨weight_hub H _, fun a _ => weight_old H _ a⟩

theorem weight_delta_zero (x : O G H) : delta H (weightCoords H x.val.val) = 0 := by
  let M : MaxIndependent H := Classical.choice inferInstance
  exact le_antisymm ((delta_le H M _).trans (weight_bad_zero G H M x).le)
    (delta_nonneg H (weight_probability G H x).1)

theorem cut_hub_zero (x : O G H) : cutCoords H x.val.val (hub H) = 0 := by
  obtain ⟨M, hM⟩ := delta_witness H x.val.val
  exact ((bad_zero H (cut_probability G H x.val).1 M).mp
    (cut_bad_zero G H x.val M (hM ▸ x.property))).1

theorem cut_weight_avoid (x : O G H) (t : ℝ) :
    Avoid (suspensionGraph G H)
      (mix t (cutCoords H x.val.val) (weightCoords H x.val.val)) := by
  apply avoid_mix
  have hi := cut_avoid G H x.val
  have hpair (a : V) (M : MaxIndependent H) (ha : a ∉ M.val) :
      (cutCoords H x.val.val (old a) = 0 ∧ weightCoords H x.val.val (old a) = 0) ∨
      (cutCoords H x.val.val (apex M) = 0 ∧ weightCoords H x.val.val (apex M) = 0) := by
    by_cases hM : bad H M x.val.val < epsilon H
    · left
      exact ⟨((bad_zero H (cut_probability G H x.val).1 M).mp
        (cut_bad_zero G H x.val M hM)).2 a ha, weight_old H _ a⟩
    · have hw : weightCoords H x.val.val (apex M) = 0 := by
        apply FiniteCoordinateTruncation.normalize_zero
        exact max_eq_right (sub_nonpos.mpr (le_of_not_gt hM))
      rcases hi (old a) (apex M) ha with ho | hm
      · exact Or.inl ⟨ho, weight_old H _ a⟩
      · exact Or.inr ⟨hm, hw⟩
  rintro (a | a) (b | b) hab
  · exact (hi (old a) (old b) hab).imp
      (fun ha => ⟨ha, weight_old H _ a⟩) (fun hb => ⟨hb, weight_old H _ b⟩)
  · cases b with
    | none => exact hab.elim
    | some M => exact hpair a M hab
  · cases a with
    | none => exact hab.elim
    | some M => exact (hpair b M hab).symm
  · cases a <;> cases b <;> simp only [suspensionGraph, gadgetAdj] at hab
    · exact Or.inl ⟨cut_hub_zero G H x, weight_hub H _⟩
    · exact Or.inr ⟨cut_hub_zero G H x, weight_hub H _⟩

theorem cut_weight_delta_zero (x : O G H) (t : I) :
    delta H (mix t (cutCoords H x.val.val) (weightCoords H x.val.val)) = 0 := by
  obtain ⟨M, hM⟩ := delta_witness H x.val.val
  have hy := cut_bad_zero G H x.val M (hM ▸ x.property)
  apply le_antisymm
  · apply (delta_le H M _).trans
    rw [bad_mix, hy, weight_bad_zero]; simp
  · exact delta_nonneg H (probability_mix (cut_probability G H x.val)
      (weight_probability G H x) t).1

def chosenApex : MaxIndependent H := Classical.choice inferInstance

def apexPoint : O G H :=
  ⟨vertex (suspensionGraph G H) (apex (chosenApex H)), by
    have hz := bad_zero_of_apex G H
      (vertex (suspensionGraph G H) (apex (chosenApex H))) (chosenApex H) (by simp [vertex])
    exact lt_of_le_of_lt ((delta_le H (chosenApex H) _).trans hz.le) (epsilon_pos H)⟩

theorem apexPoint_bad_zero (M : MaxIndependent H) :
    bad H M (apexPoint G H).val.val = 0 := by
  simp [bad, apexPoint, vertex, old, hub, apex, Pi.single_apply]

theorem weight_apex_avoid (x : O G H) (t : ℝ) :
    Avoid (suspensionGraph G H)
      (mix t (weightCoords H x.val.val) (apexPoint G H).val.val) := by
  apply apex_supported_avoid G H
  · intro a
    simp [mix, weightCoords, FiniteCoordinateTruncation.normalize, apexRaw,
      apexPoint, vertex, old, apex, Pi.single_apply]
  · simp [mix, weightCoords, FiniteCoordinateTruncation.normalize, apexRaw,
      apexPoint, vertex, hub, apex, Pi.single_apply]

theorem weight_apex_delta_zero (x : O G H) (t : I) :
    delta H (mix t (weightCoords H x.val.val) (apexPoint G H).val.val) = 0 := by
  apply le_antisymm
  · apply (delta_le H (chosenApex H) _).trans
    rw [bad_mix, weight_bad_zero, apexPoint_bad_zero]; simp
  · exact delta_nonneg H (probability_mix (weight_probability G H x)
      (probability _ (apexPoint G H).val) t).1

abbrev cluster : Set (X G H) := {x | delta H x.val = 0}

def clusterHomeomorph : ↥(realization (starB G H)) ≃ₜ ↥(cluster G H) where
  toFun x := ⟨⟨x.val, ((starB_realization_iff G H x.val).mp x.property).1⟩,
    ((starB_realization_iff G H x.val).mp x.property).2⟩
  invFun x := ⟨x.val.val, (starB_realization_iff G H x.val.val).mpr ⟨x.val.property, x.property⟩⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext (Subtype.ext rfl)
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

def clusterInO : C(↥(cluster G H), ↥(O G H)) where
  toFun x := ⟨x.val, lt_of_eq_of_lt x.property (epsilon_pos H)⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

def clusterCut : C(↥(cluster G H), ↥(cluster G H)) :=
  regionMap G H (fun x => delta H x = 0) (fun x => cutCoords H x.val.val)
    ((continuous_cutCoords G H).comp continuous_subtype_val)
    (fun x => ⟨cut_probability G H x.val, cut_avoid G H x.val⟩)
    (fun x => cut_delta_zero G H (clusterInO G H x))

def clusterWeight : C(↥(cluster G H), ↥(cluster G H)) :=
  regionMap G H (fun x => delta H x = 0) (fun x => weightCoords H x.val.val)
    (continuous_normalize ((continuous_apexRaw H).comp
      (continuous_subtype_val.comp continuous_subtype_val))
      (fun x => (apexRaw_sum_pos G H (clusterInO G H x)).ne'))
    (fun x => ⟨weight_probability G H (clusterInO G H x),
      apex_supported_avoid G H (weight_old H _) (weight_hub H _)⟩)
    (fun x => weight_delta_zero G H (clusterInO G H x))

def clusterPoint : cluster G H :=
  ⟨(apexPoint G H).val, by
    apply le_antisymm
    · exact (delta_le H (chosenApex H) _).trans (apexPoint_bad_zero G H _).le
    · exact delta_nonneg H (probability _ (apexPoint G H).val).1⟩

def clusterFirst : (ContinuousMap.id ↥(cluster G H)).Homotopy (clusterCut G H) :=
  regionStraight G H (fun x => delta H x = 0) _ _
    (fun t x => avoid_mix_of_support (avoid _ x.val) (cut_support G H x.val) t)
    (fun t x => by
      obtain ⟨M, hM⟩ := delta_witness H x.val.val
      have hm0 : bad H M x.val.val = 0 := hM.symm.trans x.property
      have hy0 := cut_bad_zero G H x.val M (by rw [hm0]; exact epsilon_pos H)
      apply le_antisymm
      · apply (delta_mix_bound H M hy0 t).trans
        change (1 - (t : ℝ)) * bad H M x.val.val ≤ 0
        rw [hm0]; simp
      · exact delta_nonneg H (probability_mix (probability _ x.val)
          (cut_probability G H x.val) t).1)

def clusterSecond : (clusterCut G H).Homotopy (clusterWeight G H) :=
  regionStraight G H (fun x => delta H x = 0) _ _
    (fun t x => cut_weight_avoid G H (clusterInO G H x) t)
    (fun t x => cut_weight_delta_zero G H (clusterInO G H x) t)

def clusterThird : (clusterWeight G H).Homotopy (ContinuousMap.const _ (clusterPoint G H)) :=
  regionStraight G H (fun x => delta H x = 0) _ _
    (fun t x => weight_apex_avoid G H (clusterInO G H x) t)
    (fun t x => weight_apex_delta_zero G H (clusterInO G H x) t)

theorem contractible_cluster : ContractibleSpace ↥(cluster G H) :=
  (contractible_iff_id_nullhomotopic _).mpr
    ⟨clusterPoint G H, ⟨((clusterFirst G H).trans (clusterSecond G H)).trans (clusterThird G H)⟩⟩

/-- Actual contractibility of the finite independent-apex star cluster. -/
theorem contractible_starB : ContractibleSpace ↥(realization (starB G H)) := by
  letI := contractible_cluster G H
  exact (clusterHomeomorph G H).contractibleSpace

/- Unlike the fixed cutoff used in the contraction, the following variable
cutoff vanishes on B. Thus it gives an actual neighborhood retraction. -/
def retractRaw (x : Vertex H → ℝ) := cut (delta H x) x
def retractCoords (x : Vertex H → ℝ) := FiniteCoordinateTruncation.normalize (retractRaw H x)

private theorem retract_sum_lower (x : O G H) :
    (3 / 4 : ℝ) < ∑ a, retractRaw H x.val.val a := by
  have hb := cut_sum_bound (probability _ x.val) (delta H x.val.val)
  have he := card_epsilon H
  have hle : (Fintype.card (Vertex H) : ℝ) * delta H x.val.val ≤
      (Fintype.card (Vertex H) : ℝ) * epsilon H :=
    mul_le_mul_of_nonneg_left x.property.le (by positivity)
  change (3 / 4 : ℝ) < ∑ a, cut (delta H x.val.val) x.val.val a
  linarith

theorem retract_sum_pos (x : O G H) : 0 < ∑ a, retractRaw H x.val.val a :=
  lt_trans (by norm_num : (0 : ℝ) < 3 / 4) (retract_sum_lower G H x)

theorem retract_probability (x : O G H) : Probability (retractCoords H x.val.val) :=
  probability_normalize (cut_nonneg _ _) (retract_sum_pos G H x)

theorem retract_support (x : O G H) (a : Vertex H) (ha : x.val.val a = 0) :
    retractCoords H x.val.val a = 0 :=
  FiniteCoordinateTruncation.normalize_zero (cut_zero (delta_nonneg H (probability _ x.val).1) ha)

theorem retract_bad_zero (x : O G H) (M : MaxIndependent H)
    (hM : delta H x.val.val = bad H M x.val.val) :
    bad H M (retractCoords H x.val.val) = 0 := by
  apply (bad_zero H (retract_probability G H x).1 M).mpr
  constructor
  · exact FiniteCoordinateTruncation.normalize_zero (cut_eq_zero (by rw [hM]; exact hub_le_bad H (probability _ x.val).1 M))
  · intro a ha
    exact FiniteCoordinateTruncation.normalize_zero (cut_eq_zero (by rw [hM]; exact old_le_bad H (probability _ x.val).1 M a ha))

def neighborhoodRetraction : C(↥(O G H), ↥(cluster G H)) :=
  regionMap G H (fun x => delta H x = 0) (fun x => retractCoords H x.val.val)
    (continuous_normalize
      (continuous_cut (continuous_subtype_val.comp continuous_subtype_val)
        ((continuous_delta H).comp (continuous_subtype_val.comp continuous_subtype_val)))
      (fun x => (retract_sum_pos G H x).ne'))
    (fun x => ⟨retract_probability G H x,
      avoid_of_support (avoid _ x.val) (retract_support G H x)⟩)
    (fun x => by
      obtain ⟨M, hM⟩ := delta_witness H x.val.val
      exact le_antisymm ((delta_le H M _).trans (retract_bad_zero G H x M hM).le)
        (delta_nonneg H (retract_probability G H x).1))

def neighborhoodFirst : (ContinuousMap.id ↥(O G H)).Homotopy
    ((clusterInO G H).comp (neighborhoodRetraction G H)) :=
  regionStraight G H (fun x => delta H x < epsilon H) _ _
    (fun t x => avoid_mix_of_support (avoid _ x.val) (retract_support G H x) t)
    (fun t x => by
      obtain ⟨M, hM⟩ := delta_witness H x.val.val
      exact delta_mix_lt H (probability _ x.val).1 x.property M hM
        (retract_bad_zero G H x M hM) t)

theorem retraction_fixes (x : cluster G H) :
    neighborhoodRetraction G H (clusterInO G H x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  ext a
  change FiniteCoordinateTruncation.normalize (cut (delta H x.val.val) x.val.val) a = x.val.val a
  rw [x.property]
  have hc : cut 0 x.val.val = x.val.val := by
    ext b
    simp [cut, max_eq_left ((probability _ x.val).1 b)]
  rw [hc]
  simp [FiniteCoordinateTruncation.normalize, (probability _ x.val).2]

/-- Explicit neighborhood equivalence, fixing the closed star cluster. -/
def neighborhoodEquiv : ↥(O G H) ≃ₕ ↥(cluster G H) where
  toFun := neighborhoodRetraction G H
  invFun := clusterInO G H
  left_inv := ⟨(neighborhoodFirst G H).symm⟩
  right_inv := by
    have he : (neighborhoodRetraction G H).comp (clusterInO G H) = ContinuousMap.id _ := by
      apply ContinuousMap.ext
      intro x
      exact retraction_fixes G H x
    rw [he]

theorem contractible_O : ContractibleSpace ↥(O G H) := by
  letI := contractible_starB G H
  letI : ContractibleSpace ↥(cluster G H) := (clusterHomeomorph G H).symm.contractibleSpace
  exact (neighborhoodEquiv G H).contractibleSpace

def oldRaw (x : Vertex H → ℝ) (a : V) : ℝ := cut (epsilon H) x (old a)
def oldCoords (x : Vertex H → ℝ) : V → ℝ := FiniteCoordinateTruncation.normalize (oldRaw H x)

private theorem oldRaw_sum_lower (x : ↥(U G H ∩ O G H)) :
    (1 / 4 : ℝ) < ∑ a, oldRaw H x.val.val a := by
  obtain ⟨M, hM⟩ := delta_witness H x.val.val
  have hhub : x.val.val (hub H) < epsilon H :=
    (hub_le_bad H (probability _ x.val).1 M).trans_lt (hM ▸ x.property.2)
  have hcard : (Fintype.card V : ℝ) + 1 ≤ Fintype.card (Vertex H) := by
    exact_mod_cast (show Fintype.card V + 1 ≤ Fintype.card (Vertex H) by
      simp only [Vertex, Fintype.card_sum, Fintype.card_option]; omega)
  have hprod := mul_le_mul_of_nonneg_right hcard (epsilon_pos H).le
  have he := card_epsilon H
  have hsum : (∑ a : V, x.val.val (old a)) - (Fintype.card V : ℝ) * epsilon H ≤
      ∑ a, oldRaw H x.val.val a := by
    calc
      _ = ∑ a : V, (x.val.val (old a) - epsilon H) := by
        rw [Finset.sum_sub_distrib]; simp
      _ ≤ _ := Finset.sum_le_sum fun _ _ => le_max_left _ _
  have ht := total G H x.val
  have hu := x.property.1
  dsimp [U] at hu
  nlinarith

theorem oldRaw_sum_pos (x : ↥(U G H ∩ O G H)) : 0 < ∑ a, oldRaw H x.val.val a :=
  lt_trans (by norm_num : (0 : ℝ) < 1 / 4) (oldRaw_sum_lower G H x)

theorem old_probability (x : ↥(U G H ∩ O G H)) : Probability (oldCoords H x.val.val) :=
  probability_normalize (fun a => cut_nonneg _ _ _) (oldRaw_sum_pos G H x)

theorem old_support (x : X G H) (a : V) (ha : x.val (old a) = 0) :
    oldCoords H x.val a = 0 :=
  FiniteCoordinateTruncation.normalize_zero (cut_zero (epsilon_pos H).le ha)

theorem old_off_M (x : X G H) (M : MaxIndependent H)
    (hM : bad H M x.val < epsilon H) (a : V) (ha : a ∉ M.val) :
    oldCoords H x.val a = 0 :=
  FiniteCoordinateTruncation.normalize_zero (cut_eq_zero ((old_le_bad H (probability _ x).1 M a ha).trans hM.le))

theorem old_avoid (x : ↥(U G H ∩ O G H)) : Avoid G (oldCoords H x.val.val) := by
  obtain ⟨M, hM⟩ := delta_witness H x.val.val
  have hbad : bad H M x.val.val < epsilon H := hM ▸ x.property.2
  intro a b hab
  by_cases hH : H.Adj a b
  · by_cases ha : a ∈ M.val
    · right
      apply old_off_M G H x.val M hbad b
      intro hb
      exact M.property.1 ha hb (H.ne_of_adj hH) hH
    · exact Or.inl (old_off_M G H x.val M hbad a ha)
  · exact (avoid _ x.val (old a) (old b) ⟨hab, hH⟩).imp
      (old_support G H x.val a) (old_support G H x.val b)

theorem continuous_oldRaw : Continuous (oldRaw H) := by
  apply continuous_pi
  intro a
  exact ((continuous_apply (old a)).sub continuous_const).max continuous_const

def oldReturn : C(↥(U G H ∩ O G H), Ispace G) where
  toFun x := ⟨oldCoords H x.val.val,
    (realization_iff _ _).mpr ⟨old_probability G H x, old_avoid G H x⟩⟩
  continuous_toFun := (continuous_normalize ((continuous_oldRaw H).comp
    (continuous_subtype_val.comp continuous_subtype_val))
    (fun x => (oldRaw_sum_pos G H x).ne')).subtype_mk _

def oldInclusion (hHG : H ≤ G) : C(Ispace G, ↥(U G H ∩ O G H)) :=
  regionMap G H (fun x => mass H x < 1 / 2 ∧ delta H x < epsilon H)
    (fun z => liftOld H z.val)
    ((continuous_liftOld H).comp continuous_subtype_val)
    (fun z => ⟨probability_liftOld H (probability _ z), avoid_liftOld G H (avoid _ z)⟩)
    (fun z => ⟨by rw [mass_liftOld]; norm_num,
      by rw [delta_liftOld G H hHG (probability _ z) (avoid _ z)]; exact epsilon_pos H⟩)

theorem return_lift_support (x : ↥(U G H ∩ O G H)) (a : Vertex H)
    (ha : x.val.val a = 0) : liftOld H (oldCoords H x.val.val) a = 0 := by
  rcases a with a | a
  · exact old_support G H x.val a ha
  · rfl

theorem return_bad_zero (x : ↥(U G H ∩ O G H)) (M : MaxIndependent H)
    (hM : bad H M x.val.val < epsilon H) :
    bad H M (liftOld H (oldCoords H x.val.val)) = 0 :=
  (bad_zero H (probability_liftOld H (old_probability G H x)).1 M).mpr
    ⟨rfl, fun a ha => old_off_M G H x.val M hM a ha⟩

def intersectionFirst (hHG : H ≤ G) :
    (ContinuousMap.id ↥(U G H ∩ O G H)).Homotopy
      ((oldInclusion G H hHG).comp (oldReturn G H)) :=
  regionStraight G H (fun x => mass H x < 1 / 2 ∧ delta H x < epsilon H) _ _
    (fun t x => avoid_mix_of_support (avoid _ x.val) (return_lift_support G H x) t)
    (fun t x => by
      constructor
      · exact mass_mix_lt H x.property.1
          (Finset.sum_nonneg fun _ _ => (probability _ x.val).1 _) (mass_liftOld H _) t
      · obtain ⟨M, hM⟩ := delta_witness H x.val.val
        exact delta_mix_lt H (probability _ x.val).1 x.property.2 M hM
          (return_bad_zero G H x M (hM ▸ x.property.2)) t)

def intersectionSecond (hHG : H ≤ G) :
    (ContinuousMap.id (Ispace G)).Homotopy
      ((oldReturn G H).comp (oldInclusion G H hHG)) :=
  straight _ _ (fun t z => by
    apply (realization_iff G _).mpr
    refine ⟨probability_mix (probability _ z)
      (probability _ ((oldReturn G H) ((oldInclusion G H hHG) z))) t, ?_⟩
    apply avoid_mix_of_support (avoid _ z)
    intro a ha
    apply FiniteCoordinateTruncation.normalize_zero
    exact cut_zero (epsilon_pos H).le ha)

/-- The intersection of the constructed OPEN neighborhoods is homotopy
equivalent to the actual old independence realization, with both homotopies
given above. This is the finite-cover bridge required by Mayer--Vietoris. -/
def intersectionEquiv (hHG : H ≤ G) : ↥(U G H ∩ O G H) ≃ₕ Ispace G where
  toFun := oldReturn G H
  invFun := oldInclusion G H hHG
  left_inv := ⟨(intersectionFirst G H hHG).symm⟩
  right_inv := ⟨(intersectionSecond G H hHG).symm⟩

end Coordinates

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
