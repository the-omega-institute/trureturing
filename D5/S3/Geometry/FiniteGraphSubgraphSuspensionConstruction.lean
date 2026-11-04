/- GID: D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction
   mirror-E: none(waiver:finite-graph-singular-homology)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Clique]
   utility: none
   digest: Graph gadget, exact open cover, and star-cluster contraction. -/
import D5.S3.Geometry.FiniteCoordinateTruncation
import Mathlib.Combinatorics.SimpleGraph.Subgraph

/-!
# Subgraph suspension by an independent star cluster

This construction provides supporting machinery for the king-grid setting of
Question 32 in Carnero Bravo, arXiv:2505.06457v2. It does not settle that
question. In particular, H less than or equal to G never means that H is induced.

The geometric carrier and independence complex are the existing project ones.
The finite open cover and its contractions are constructed in coordinates.
The retraction and homology endpoint are supplied by the following modules.
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
  let s := (support z).image (oldEmbedding H)
  have hs : s ∈ starA G H ⊓ starB G H := by
    rw [intersection_faces G H hHG]
    exact ⟨support z, ⟨support_nonempty hz, (independent_support_iff G z).mpr hi⟩, rfl⟩
  have hc : liftOld H z ∈ faceSimplex s := by
    refine ⟨(probability_liftOld H hz).1, (probability_liftOld H hz).2, ?_⟩
    rintro (a | a) ha
    · by_contra hza
      exact ha (Finset.mem_image.mpr ⟨a, (mem_support z a).mpr hza, rfl⟩)
    · rfl
  exact ((starB_realization_iff G H _).mp
    ⟨s, hs.2, (faceSimplex_eq_convexHull s) ▸ hc⟩).2

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


end Coordinates

end D5.S3.Geometry.FiniteGraphSubgraphSuspension
