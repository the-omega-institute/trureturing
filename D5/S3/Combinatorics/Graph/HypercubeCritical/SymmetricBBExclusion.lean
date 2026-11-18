/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricBBExclusion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SymmetricBBExclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricSliceExclusion.result; instance=D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricSliceExclusion.claim
   digest: Extract the actual B/B double-star and high eight-cycle. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricActualHighProfiles
import D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricCycleLowSaturation
import D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricTwentyTwoNonEmbedding
import D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceExclusion
import Batteries.Tactic.OpenPrivate

/-! Actual B/B extraction, retaining all original graph incidences. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricBBExclusion

open SimpleGraph GirthSliceCounting

attribute [local instance] Classical.propDecidable

open private High graph side graph_degree high_partition high_graph_girth actual_partition from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricHighGraph
open private highTypeB from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricHighProfiles
open private sideDegreeTuple side_typeB_iff actual_high_profiles
  actual_high_saturation_of_original_typeB from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricActualHighProfiles
open private saturated_decomposition from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricSaturatedDecomposition
open private CycleLowData CycleLowData.partner CycleLowData.low
  CycleLowData.low_injective CycleLowData.low_degree CycleLowData.partner_degree
  CycleLowData.partner_outside actual_high_cycle_low_saturation actual_cycle_partner_fibers
  cycle_partners_exhaust_leaves four_leaf_representatives cycle_partner_sides from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricCycleLowSaturation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {L R : Finset V}

/-- The original B/B conditions produce the actual double-star, actual high C8,
all eight actual lows, and exactly four antipodal leaf fibers. -/
private theorem actual_bb_classification
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL : L.card = 11) (hR : R.card = 11)
    (hL2 : (degreeTwo G L).card = 4) (hR2 : (degreeTwo G R).card = 4)
    (hLB : highTypeB G (degreeThree G L)) (hRB : highTypeB G (degreeThree G R)) :
    ∃ a b : High G, ∃ e : cycleGraph 8 ↪g graph G,
      ∃ d : CycleLowData G (fun i => (e i).val),
      a ∈ side G L ∧ b ∈ side G R ∧
      (graph G).degree a = 3 ∧ (graph G).degree b = 3 ∧ (graph G).Adj a b ∧
      (graph G).neighborFinset a = insert b ((side G R).filter fun x => (graph G).degree x = 1) ∧
      (graph G).neighborFinset b = insert a ((side G L).filter fun x => (graph G).degree x = 1) ∧
      (∀ x, (graph G).degree x = 2 ↔ ∃ i, e i = x) ∧
      (∀ i j, (CycleLowData.partner d) j = (CycleLowData.partner d) i ↔ j = i ∨ j = i + 4) ∧
      (∀ x : High G, (graph G).degree x = 1 ↔ ∃ i, (CycleLowData.partner d) i = x.val) ∧
      Function.Injective (fun i : Fin 4 => (CycleLowData.partner d) (i.castLE (by decide : 4 ≤ 8))) ∧
      (∀ i : Fin 8, ∃ j : Fin 4, (CycleLowData.partner d) i = (CycleLowData.partner d) (j.castLE (by decide : 4 ≤ 8))) := by
  have hBL := (side_typeB_iff G L).mpr hLB
  have hBR := (side_typeB_iff G R).mpr hRB
  unfold sideDegreeTuple at hBL hBR
  obtain ⟨hL1, hL23⟩ := Prod.mk.inj hBL
  obtain ⟨hLh2, hL3⟩ := Prod.mk.inj hL23
  obtain ⟨hR1, hR23⟩ := Prod.mk.inj hBR
  obtain ⟨hRh2, hR3⟩ := Prod.mk.inj hR23
  obtain ⟨hhigh, _, _⟩ := actual_high_profiles hpart hdeg hlow hg hL hR hL2 hR2
  have hsat := actual_high_saturation_of_original_typeB
    hpart hdeg hlow hg hL hR hL2 hR2 hLB hRB
  obtain ⟨_, _, hhp⟩ := high_partition hpart hdeg
  obtain ⟨a, b, e, ha, hb, ha3, hb3, hab, hNa, hNb, he⟩ :=
    saturated_decomposition hhp hhigh hsat (high_graph_girth hg)
      hL1 hR1 hLh2 hRh2 hL3 hR3
  have he2 : ∀ i, (graph G).degree (e i) = 2 := fun i => (he (e i)).mpr ⟨i, rfl⟩
  obtain ⟨d⟩ := actual_high_cycle_low_saturation hpart hdeg hlow hg hL2 hR2 e he2
  have hc : Function.Injective (fun i => (e i).val) := by
    intro i j hij
    exact e.injective (Subtype.ext hij)
  have hcycle : ∀ i j, (cycleGraph 8).Adj i j → G.Adj (e i).val (e j).val :=
    fun _ _ hij => e.map_adj_iff.mpr hij
  have hcover : ∀ x : High G,
      (graph G).degree x = 2 ↔ ∃ i, (e i).val = x.val := by
    intro x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := (he x).mp hx
      exact ⟨i, congrArg Subtype.val hi⟩
    · rintro ⟨i, hi⟩
      exact (he x).mpr ⟨i, Subtype.ext hi⟩
  have hf := actual_cycle_partner_fibers hpart hdeg hg (fun i => (e i).val)
    hc (fun i => (e i).property) hcycle d hhigh hcover
  have hex := cycle_partners_exhaust_leaves d hdeg hhigh hcover
  obtain ⟨hinj, hrep⟩ := four_leaf_representatives d hf
  refine ⟨a, b, e, d, ha, hb, ha3, hb3, hab, ?_, ?_, he, hf, hex, hinj, hrep⟩
  · simpa only [Finset.ext_iff, Finset.mem_insert] using hNa
  · simpa only [Finset.ext_iff, Finset.mem_insert] using hNb


private abbrev BBTag := Fin 8 ⊕ (Fin 2 ⊕ (Fin 8 ⊕ Fin 4))

private def bbLabels : Fin 22 → BBTag :=
  ![Sum.inr (Sum.inl 0), Sum.inr (Sum.inr (Sum.inl 0)),
    Sum.inr (Sum.inr (Sum.inl 4)), Sum.inr (Sum.inr (Sum.inl 2)),
    Sum.inl 5, Sum.inr (Sum.inr (Sum.inr 0)), Sum.inl 7,
    Sum.inr (Sum.inr (Sum.inl 6)), Sum.inl 3,
    Sum.inr (Sum.inr (Sum.inr 2)), Sum.inl 1, Sum.inl 6,
    Sum.inr (Sum.inr (Sum.inr 1)), Sum.inr (Sum.inl 1),
    Sum.inr (Sum.inr (Sum.inr 3)), Sum.inr (Sum.inr (Sum.inl 1)),
    Sum.inl 0, Sum.inr (Sum.inr (Sum.inl 7)), Sum.inl 2,
    Sum.inr (Sum.inr (Sum.inl 3)), Sum.inr (Sum.inr (Sum.inl 5)), Sum.inl 4]

private theorem bbLabels_injective : Function.Injective bbLabels := by
  decide +kernel

private def bbHighRealize (a b : High G) (e : cycleGraph 8 ↪g graph G)
    (d : CycleLowData G (fun i => (e i).val)) : Fin 2 ⊕ (Fin 8 ⊕ Fin 4) → High G :=
  Sum.elim ![a, b] (Sum.elim e (fun i =>
    ⟨CycleLowData.partner d (i.castLE (by decide : 4 ≤ 8)),
      CycleLowData.partner_degree d (i.castLE (by decide : 4 ≤ 8))⟩))

private def bbRealize (a b : High G) (e : cycleGraph 8 ↪g graph G)
    (d : CycleLowData G (fun i => (e i).val)) : BBTag → V :=
  Sum.elim (CycleLowData.low d) (fun t => (bbHighRealize a b e d t).val)

/-- Actual degree and high-degree distinctions separate all label categories. -/
private theorem bb_labels_injective
    (a b : High G) (e : cycleGraph 8 ↪g graph G)
    (d : CycleLowData G (fun i => (e i).val))
    (ha3 : (graph G).degree a = 3) (hb3 : (graph G).degree b = 3)
    (hab : (graph G).Adj a b)
    (he2 : ∀ i, (graph G).degree (e i) = 2)
    (hleaf : ∀ i, (graph G).degree
      (⟨CycleLowData.partner d i, CycleLowData.partner_degree d i⟩ : High G) = 1)
    (hinj : Function.Injective (fun i : Fin 4 =>
      CycleLowData.partner d (i.castLE (by decide : 4 ≤ 8)))) :
    Function.Injective (fun i : Fin 22 => bbRealize a b e d (bbLabels i)) := by
  let z : Fin 2 → High G := ![a, b]
  let p : Fin 4 → High G := fun i =>
    ⟨CycleLowData.partner d (i.castLE (by decide : 4 ≤ 8)),
      CycleLowData.partner_degree d (i.castLE (by decide : 4 ≤ 8))⟩
  have hz3 : ∀ i, (graph G).degree (z i) = 3 := by
    intro i
    fin_cases i
    · exact ha3
    · exact hb3
  have hp1 : ∀ i, (graph G).degree (p i) = 1 := fun i => hleaf _
  have hz : Function.Injective z := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact False.elim (hab.ne hij)
    · exact False.elim (hab.ne hij.symm)
    · rfl
  have hp : Function.Injective p := by
    intro i j hij
    exact hinj (congrArg Subtype.val hij)
  have hcp : ∀ i j, e i ≠ p j := by
    intro i j hij
    have hd := congrArg (fun x : High G => (graph G).degree x) hij
    rw [he2 i, hp1 j] at hd
    omega
  have hrest : Function.Injective (Sum.elim e p) := e.injective.sumElim hp hcp
  have hsep : ∀ i t, z i ≠ Sum.elim e p t := by
    intro i t hij
    have hd := congrArg (fun x : High G => (graph G).degree x) hij
    rcases t with j | j
    · change (graph G).degree (z i) = (graph G).degree (e j) at hd
      rw [hz3 i, he2 j] at hd
      omega
    · change (graph G).degree (z i) = (graph G).degree (p j) at hd
      rw [hz3 i, hp1 j] at hd
      omega
  have hh : Function.Injective (bbHighRealize a b e d) := hz.sumElim hrest hsep
  have hhval : Function.Injective (fun t => (bbHighRealize a b e d t).val) :=
    Subtype.val_injective.comp hh
  have hlowsep : ∀ i t, CycleLowData.low d i ≠ (bbHighRealize a b e d t).val := by
    intro i t hij
    have hd := CycleLowData.low_degree d i
    rw [hij] at hd
    have h3 := (bbHighRealize a b e d t).property
    omega
  have hr : Function.Injective (bbRealize a b e d) :=
    (CycleLowData.low_injective d).sumElim hhval hlowsep
  exact hr.comp bbLabels_injective

open private cycle_parity_sides from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricCycleLowSaturation
open private CycleLowData.cycle_adj CycleLowData.partner_adj from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricCycleLowSaturation
open private SymmetricTwentyTwoNonEmbedding.graph SymmetricTwentyTwoNonEmbedding.edges from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricTwentyTwoNonEmbedding
open private induced_of_saturated_degrees from
  D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceExclusion

private abbrev model := SymmetricTwentyTwoNonEmbedding.graph
private abbrev modelEdges := SymmetricTwentyTwoNonEmbedding.edges
private instance : DecidableRel model.Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ ((a,b) ∈ modelEdges ∨ (b,a) ∈ modelEdges)))
private def modelNeighbors (a : Fin 22) := Finset.univ.filter (model.Adj a)
private def bbTagDegree : BBTag → ℕ := Sum.elim (fun _ => 2) (fun _ => 3)
private theorem model_neighbor_card : ∀ a, (modelNeighbors a).card = bbTagDegree (bbLabels a) := by
  decide +kernel

private theorem bb_induced_embedding
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (a b : High G) (e : cycleGraph 8 ↪g graph G)
    (d : CycleLowData G (fun i => (e i).val))
    (h0 : (e 0).val ∈ L)
    (ha3 : (graph G).degree a = 3) (hb3 : (graph G).degree b = 3)
    (hab : (graph G).Adj a b)
    (hNa : (graph G).neighborFinset a = insert b ((side G R).filter fun x => (graph G).degree x = 1))
    (hNb : (graph G).neighborFinset b = insert a ((side G L).filter fun x => (graph G).degree x = 1))
    (he2 : ∀ i, (graph G).degree (e i) = 2)
    (hfiber : ∀ i j, CycleLowData.partner d j = CycleLowData.partner d i ↔ j = i ∨ j = i + 4)
    (hleaf : ∀ i, (graph G).degree
      (⟨CycleLowData.partner d i, CycleLowData.partner_degree d i⟩ : High G) = 1)
    (hinj : Function.Injective (fun i : Fin 4 =>
      CycleLowData.partner d (i.castLE (by decide : 4 ≤ 8)))) :
    ∃ F : Fin 22 → V, Function.Injective F ∧
      ∀ i j, model.Adj i j ↔ G.Adj (F i) (F j) := by
  let F : Fin 22 → V := fun i => bbRealize a b e d (bbLabels i)
  have hF := bb_labels_injective a b e d ha3 hb3 hab he2 hleaf hinj
  have hc : ∀ i j, (cycleGraph 8).Adj i j → G.Adj (e i).val (e j).val :=
    fun _ _ h => e.map_adj_iff.mpr h
  obtain ⟨hcL, hcR⟩ := cycle_parity_sides hpart (fun i => (e i).val) hc h0
  have haP (i : Fin 8) (hi : i.val % 2 = 1) : G.Adj a.val (CycleLowData.partner d i) := by
    let x : High G := ⟨CycleLowData.partner d i, CycleLowData.partner_degree d i⟩
    have hs : x ∈ side G R := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (cycle_partner_sides hpart d i).2.mpr (hcR i hi)⟩
    have hm : x ∈ (graph G).neighborFinset a := by
      rw [hNa]
      exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hs, hleaf i⟩)
    exact ((graph G).mem_neighborFinset _ _).mp hm
  have hbP (i : Fin 8) (hi : i.val % 2 = 0) : G.Adj b.val (CycleLowData.partner d i) := by
    let x : High G := ⟨CycleLowData.partner d i, CycleLowData.partner_degree d i⟩
    have hs : x ∈ side G L := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (cycle_partner_sides hpart d i).1.mpr (hcL i hi)⟩
    have hm : x ∈ (graph G).neighborFinset b := by
      rw [hNb]
      exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hs, hleaf i⟩)
    exact ((graph G).mem_neighborFinset _ _).mp hm
  have hp4 : CycleLowData.partner d 4 = CycleLowData.partner d 0 :=
    (hfiber 0 4).mpr (Or.inr (by decide))
  have hp5 : CycleLowData.partner d 5 = CycleLowData.partner d 1 :=
    (hfiber 1 5).mpr (Or.inr (by decide))
  have hp6 : CycleLowData.partner d 6 = CycleLowData.partner d 2 :=
    (hfiber 2 6).mpr (Or.inr (by decide))
  have hp7 : CycleLowData.partner d 7 = CycleLowData.partner d 3 :=
    (hfiber 3 7).mpr (Or.inr (by decide))
  have hedgeList : ∀ p ∈ modelEdges, G.Adj (F p.1) (F p.2) := by
    simp only [modelEdges, SymmetricTwentyTwoNonEmbedding.edges, List.forall_mem_cons,
      List.forall_mem_nil, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact haP 1 (by decide)
    · exact hab
    · exact haP 3 (by decide)
    · exact hc 0 1 (by decide)
    · exact CycleLowData.cycle_adj d 0
    · exact hc 0 7 (by decide)
    · exact hc 4 3 (by decide)
    · exact hc 4 5 (by decide)
    · exact CycleLowData.cycle_adj d 4
    · exact hc 2 1 (by decide)
    · exact CycleLowData.cycle_adj d 2
    · exact hc 2 3 (by decide)
    · change G.Adj (CycleLowData.low d 5) (CycleLowData.partner d 1)
      simpa only [hp5] using (CycleLowData.partner_adj d 5).symm
    · exact (CycleLowData.cycle_adj d 5).symm
    · exact (hbP 0 (by decide)).symm
    · exact CycleLowData.partner_adj d 0
    · change G.Adj (CycleLowData.partner d 0) (CycleLowData.low d 4)
      simpa only [hp4] using CycleLowData.partner_adj d 4
    · change G.Adj (CycleLowData.low d 7) (CycleLowData.partner d 3)
      simpa only [hp7] using (CycleLowData.partner_adj d 7).symm
    · exact (CycleLowData.cycle_adj d 7).symm
    · exact CycleLowData.cycle_adj d 6
    · exact hc 6 7 (by decide)
    · exact hc 6 5 (by decide)
    · exact (CycleLowData.partner_adj d 3).symm
    · exact (CycleLowData.cycle_adj d 3).symm
    · change G.Adj (CycleLowData.partner d 2) (CycleLowData.low d 6)
      simpa only [hp6] using CycleLowData.partner_adj d 6
    · exact (hbP 2 (by decide)).symm
    · exact CycleLowData.partner_adj d 2
    · exact (CycleLowData.partner_adj d 1).symm
    · exact (CycleLowData.cycle_adj d 1).symm
    · simp
  have hedge : ∀ i j, model.Adj i j → G.Adj (F i) (F j) := by
    intro i j h
    rcases h with ⟨_, h | h⟩
    · exact hedgeList (i,j) h
    · exact (hedgeList (j,i) h).symm
  have hrdeg (t : BBTag) : G.degree (bbRealize a b e d t) = bbTagDegree t := by
    rcases t with i | t
    · exact CycleLowData.low_degree d i
    · exact (bbHighRealize a b e d t).property
  have hN : ∀ i j, j ∈ modelNeighbors i ↔ model.Adj i j := by
    intro i j
    simp only [modelNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨F, hF, induced_of_saturated_degrees model modelNeighbors hN F hF hedge
    (fun i => (hrdeg (bbLabels i)).trans (model_neighbor_card i).symm)⟩

private theorem actual_bb_induced_embedding
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL : L.card = 11) (hR : R.card = 11)
    (hL2 : (degreeTwo G L).card = 4) (hR2 : (degreeTwo G R).card = 4)
    (hLB : highTypeB G (degreeThree G L)) (hRB : highTypeB G (degreeThree G R)) :
    ∃ F : Fin 22 → V, Function.Injective F ∧
      ∀ i j, model.Adj i j ↔ G.Adj (F i) (F j) := by
  obtain ⟨a, b, e, d, _ha, _hb, ha3, hb3, hab, hNa, hNb, he, hf, hex, hinj, _hrep⟩ :=
    actual_bb_classification hpart hdeg hlow hg hL hR hL2 hR2 hLB hRB
  have he2 : ∀ i, (graph G).degree (e i) = 2 := fun i => (he (e i)).mpr ⟨i, rfl⟩
  have hleaf : ∀ i, (graph G).degree
      (⟨CycleLowData.partner d i, CycleLowData.partner_degree d i⟩ : High G) = 1 := by
    intro i
    exact (hex _).mpr ⟨i, rfl⟩
  rcases actual_partition hpart hdeg (e 0).val with h0 | h0
  · exact bb_induced_embedding hpart a b e d h0 ha3 hb3 hab hNa hNb he2 hf hleaf hinj
  · exact bb_induced_embedding hpart.symm b a e d h0 hb3 ha3 hab.symm hNb hNa he2 hf hleaf hinj

/-- The B/B branch is excluded only when the original graph has an actual
induced finite-cube embedding; no abstract-graph nonexistence is asserted. -/
private theorem actual_bb_cube_excluded
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL : L.card = 11) (hR : R.card = 11)
    (hL2 : (degreeTwo G L).card = 4) (hR2 : (degreeTwo G R).card = 4)
    (hLB : highTypeB G (degreeThree G L)) (hRB : highTypeB G (degreeThree G R))
    (n : ℕ) (q : V → (Fin n → Bool)) (hq : Function.Injective q)
    (hqe : ∀ x y, G.Adj x y ↔ (Hypercube.hypercube n).Adj (q x) (q y)) : False := by
  obtain ⟨F, hF, he⟩ := actual_bb_induced_embedding
    hpart hdeg hlow hg hL hR hL2 hR2 hLB hRB
  exact SymmetricTwentyTwoNonEmbedding.result
    ⟨n, fun i => q (F i), hq.comp hF, fun i j => (he i j).trans (hqe (F i) (F j))⟩

end D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricBBExclusion
