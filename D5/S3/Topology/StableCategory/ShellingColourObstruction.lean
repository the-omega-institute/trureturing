/- GID: D5/S3/Topology/StableCategory/ShellingColourObstruction
   generality: G
   mirror-B: D5/B/S3/Topology/StableCategory/ShellingColourObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Induced four-cycles obstruct two-colour mixed shelling restrictions. -/

import D5.S3.Topology.BarycentricBaseRigidity
import D5.S3.Geometry.FiniteAlexanderDualCollapse
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Choose

/-!
# A four-cycle obstruction to mixing shelling restrictions

This formalizes the ordinary-shelling obstruction in Section 2 of the recovered
argument, using the old-vertices property from Section 3. It limits the
sufficient restriction-mixing criterion for Question 6.3.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Topology.StableCategory.ShellingColourObstruction

open BarycentricBaseRigidity (sd)
open BarycentricGraphDistance (Face subdivisionGraph)
open D5.S3.Geometry.FiniteAlexanderDualCollapse (simplex)

/-- Row i contributes one vertex in addition to all vertices in earlier rows. -/
private def rowFace (i j : Fin 3) : Finset (Fin 3 × Fin 3) :=
  insert (i, j) (Finset.univ.filter fun p : Fin 3 × Fin 3 => p.1 < i)

private theorem rowFace_nonempty (i j : Fin 3) : (rowFace i j).Nonempty :=
  Finset.insert_nonempty _ _

private theorem rowFace_subset_iff {i j k l : Fin 3} :
    rowFace i j ⊆ rowFace k l ↔ i < k ∨ (i = k ∧ j = l) := by
  constructor
  · intro h
    have hp : (i, j) ∈ rowFace k l := h (Finset.mem_insert_self _ _)
    rw [rowFace, Finset.mem_insert, Finset.mem_filter] at hp
    rcases hp with he | ⟨_, hlt⟩
    · exact Or.inr ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
    · exact Or.inl hlt
  · rintro (hlt | ⟨rfl, rfl⟩)
    · intro p hp
      rw [rowFace, Finset.mem_insert, Finset.mem_filter] at hp ⊢
      rcases hp with rfl | ⟨_, hp⟩
      · exact Or.inr ⟨Finset.mem_univ _, hlt⟩
      · exact Or.inr ⟨Finset.mem_univ _, hp.trans hlt⟩
    · exact Finset.Subset.rfl

noncomputable section

local instance (priority := 2000) (X : Type*) : DecidableEq X := Classical.decEq X

universe u

variable {V : Type u} {P Q : PreAbstractSimplicialComplex V}

private theorem singleton_mem {s : Finset V} (hs : s ∈ P) {x : V} (hx : x ∈ s) :
    ({x} : Finset V) ∈ P :=
  (P.isRelLowerSet_faces hs).2 (Finset.singleton_subset_iff.mpr hx) (Finset.singleton_nonempty x)

private theorem face_mem_of_old_vertices (label : V → Fin 2) (colour : Fin 2)
    {F R s : Finset V} (hs : s ∈ Q)
    (restriction_nonempty : R.Nonempty ∨ P = ⊥)
    (new_faces : ∀ t, t ∈ Q ∧ t ∉ P ↔ t.Nonempty ∧ R ⊆ t ∧ t ⊆ F)
    (mixed : 2 ≤ R.card → ∃ x ∈ R, ∃ y ∈ R, label x ≠ label y)
    (mono : ∀ x ∈ s, label x = colour)
    (old : ∀ x ∈ s, ({x} : Finset V) ∈ P) : s ∈ P := by
  by_contra hn
  obtain ⟨hne, hRs, hsF⟩ := (new_faces s).mp ⟨hs, hn⟩
  have hcard : R.card ≤ 1 := by
    by_contra hc
    obtain ⟨x, hx, y, hy, hxy⟩ := mixed (Nat.succ_le_of_lt (lt_of_not_ge hc))
    exact hxy ((mono x (hRs hx)).trans (mono y (hRs hy)).symm)
  rcases restriction_nonempty with hR | hP
  · obtain ⟨r, rfl⟩ := Finset.card_eq_one.mp (Nat.le_antisymm hcard (Finset.card_pos.mpr hR))
    have hr : r ∈ s := hRs (Finset.mem_singleton_self r)
    have hr_new := (new_faces {r}).mpr
      ⟨Finset.singleton_nonempty r, Finset.Subset.rfl, Finset.singleton_subset_iff.mpr (hsF hr)⟩
    exact hr_new.2 (old r hr)
  · obtain ⟨v, hv⟩ := hne
    have h := old v hv
    rw [hP] at h
    exact h

/-- A monochromatic induced four-cycle contradicts the mixed restriction-face
premises. Its two parts are indexed by `Fin 2`, with four cross edges and both
diagonals absent. A step introducing a cycle vertex would put its two neighbours
in the same attaching facet. Once all four vertices are in the older prefix,
mixing forces the four edges into that prefix too. -/
theorem false_of_monochromatic_four_cycle
    {n : ℕ} (prefixes : ℕ → PreAbstractSimplicialComplex V) (grows : Monotone prefixes)
    (initial : Finset V) (initial_eq : prefixes 0 = simplex initial)
    (facet restriction : ℕ → Finset V) (label : V → Fin 2)
    (facet_mem : ∀ j < n, facet j ∈ prefixes (j + 1))
    (restriction_nonempty : ∀ j < n, (restriction j).Nonempty ∨ prefixes j = ⊥)
    (new_faces : ∀ j < n, ∀ s, s ∈ prefixes (j + 1) ∧ s ∉ prefixes j ↔
      s.Nonempty ∧ restriction j ⊆ s ∧ s ⊆ facet j)
    (mixed : ∀ j < n, 2 ≤ (restriction j).card →
      ∃ x ∈ restriction j, ∃ y ∈ restriction j, label x ≠ label y)
    (left right : Fin 2 → V) (colour : Fin 2)
    (cross : ∀ i j, ({left i, right j} : Finset V) ∈ prefixes n)
    (no_left_diagonal : ({left 0, left 1} : Finset V) ∉ prefixes n)
    (no_right_diagonal : ({right 0, right 1} : Finset V) ∉ prefixes n)
    (left_colour : ∀ i, label (left i) = colour)
    (right_colour : ∀ j, label (right j) = colour) : False := by
  have cross_initial (k : ℕ) (hk : k ≤ n)
      (edges : ∀ i j, ({left i, right j} : Finset V) ∈ prefixes k) :
      ∀ i j, ({left i, right j} : Finset V) ∈ prefixes 0 := by
    induction k with
    | zero => exact edges
    | succ k ih =>
      have hlt : k < n := hk
      have vertex_old {a b c : V}
          (hab : ({a, b} : Finset V) ∈ prefixes (k + 1))
          (hac : ({a, c} : Finset V) ∈ prefixes (k + 1))
          (no_diagonal : ({b, c} : Finset V) ∉ prefixes n) :
          ({a} : Finset V) ∈ prefixes k := by
        by_contra ha
        have belongs_to_facet {s : Finset V} (hs : s ∈ prefixes (k + 1)) (ha_mem : a ∈ s) :
            s ⊆ facet k :=
          ((new_faces k hlt s).mp ⟨hs, fun hs_old => ha (singleton_mem hs_old ha_mem)⟩).2.2
        have hb := belongs_to_facet hab (Finset.mem_insert_self _ _)
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
        have hc := belongs_to_facet hac (Finset.mem_insert_self _ _)
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self c))
        have hbc : ({b, c} : Finset V) ∈ prefixes (k + 1) :=
          ((prefixes (k + 1)).isRelLowerSet_faces (facet_mem k hlt)).2
            (Finset.insert_subset_iff.mpr ⟨hb, Finset.singleton_subset_iff.mpr hc⟩)
            (Finset.insert_nonempty _ _)
        exact no_diagonal (grows hk hbc)
      have reverse_edges (i j : Fin 2) : ({right j, left i} : Finset V) ∈ prefixes (k + 1) :=
        Finset.pair_comm (left i) (right j) ▸ edges i j
      have left_old (i : Fin 2) :=
        vertex_old (edges i 0) (edges i 1) no_right_diagonal
      have right_old (j : Fin 2) :=
        vertex_old (reverse_edges 0 j) (reverse_edges 1 j) no_left_diagonal
      have old_edges (i j : Fin 2) : ({left i, right j} : Finset V) ∈ prefixes k := by
        refine face_mem_of_old_vertices label colour (edges i j)
          (restriction_nonempty k hlt) (new_faces k hlt) (mixed k hlt) ?_ ?_
        · intro v hv
          simp only [Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with rfl | rfl
          · exact left_colour i
          · exact right_colour j
        · intro v hv
          simp only [Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with rfl | rfl
          · exact left_old i
          · exact right_old j
      exact ih (Nat.le_of_lt hlt) old_edges
  have left_in_initial (i : Fin 2) : left i ∈ initial := by
    have h := cross_initial n le_rfl cross i 0
    rw [initial_eq] at h
    have hsub : ({left i, right 0} : Finset V) ⊆ initial := h.2
    exact hsub (Finset.mem_insert_self _ _)
  have hdiag : ({left 0, left 1} : Finset V) ∈ prefixes 0 := by
    rw [initial_eq]
    exact ⟨Finset.insert_nonempty _ _, Finset.insert_subset_iff.mpr
      ⟨left_in_initial 0, Finset.singleton_subset_iff.mpr (left_in_initial 1)⟩⟩
  exact no_left_diagonal (grows (Nat.zero_le n) hdiag)

private theorem pair_mem_sd_iff_adj {L : PreAbstractSimplicialComplex V} {s t : Face L}
    (hne : s ≠ t) : ({s, t} : Finset (Face L)) ∈ sd L ↔ (subdivisionGraph L).Adj s t := by
  constructor
  · intro h
    change s < t ∨ t < s
    exact h.2.1 (Finset.mem_insert_self _ _)
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) hne
  · intro h
    change s < t ∨ t < s at h
    refine ⟨Finset.insert_nonempty _ _, ?_, fun p _ => p.property⟩
    rw [Finset.coe_insert, Finset.coe_singleton]
    rcases h with h | h
    · exact IsChain.pair h
    · rw [Set.pair_comm]
      exact IsChain.pair h

private theorem exists_tripartite_in_sd {L : PreAbstractSimplicialComplex V} {F : Finset V}
    (hF : F ∈ L) (hcard : 9 ≤ F.card) :
    ∃ p : Fin 3 → Fin 3 → Face L,
      (∀ {i k}, i ≠ k → ∀ j l, ({p i j, p k l} : Finset (Face L)) ∈ sd L) ∧
      (∀ i {j l}, j ≠ l → ({p i j, p i l} : Finset (Face L)) ∉ sd L) := by
  obtain ⟨embed, embeds⟩ :=
    Function.Embedding.exists_of_card_le_finset (α := Fin 3 × Fin 3) (s := F)
      (by simpa using hcard)
  have subset_face (i j : Fin 3) : (rowFace i j).map embed ⊆ F := by
    intro x hx
    obtain ⟨p, _, rfl⟩ := Finset.mem_map.mp hx
    exact embeds ⟨p, rfl⟩
  let p (i j : Fin 3) : Face L :=
    ⟨(rowFace i j).map embed,
      (L.isRelLowerSet_faces hF).2 (subset_face i j)
        (Finset.map_nonempty.mpr (rowFace_nonempty i j))⟩
  have le_iff {i j k l : Fin 3} : p i j ≤ p k l ↔ i < k ∨ (i = k ∧ j = l) := by
    change (rowFace i j).map embed ⊆ (rowFace k l).map embed ↔ _
    exact Finset.map_subset_map.trans rowFace_subset_iff
  have lt_of_row_lt {i k : Fin 3} (hik : i < k) (j l : Fin 3) : p i j < p k l := by
    apply lt_of_le_not_ge (le_iff.mpr (Or.inl hik))
    intro h
    rcases le_iff.mp h with hki | ⟨hki, _⟩
    · exact (not_lt_of_ge hik.le) hki
    · exact hik.ne hki.symm
  refine ⟨p, ?_, ?_⟩
  · intro i k hik j l
    rcases lt_or_gt_of_ne hik with hlt | hgt
    · have h := lt_of_row_lt hlt j l
      exact (pair_mem_sd_iff_adj h.ne).mpr (Or.inl h)
    · have h := lt_of_row_lt hgt l j
      exact (pair_mem_sd_iff_adj h.ne.symm).mpr (Or.inr h)
  · intro i j l hjl
    have not_le {a b : Fin 3} (hab : a ≠ b) : ¬ p i a ≤ p i b := by
      intro h
      rcases le_iff.mp h with hlt | ⟨_, heq⟩
      · exact (lt_irrefl i) hlt
      · exact hab heq
    have hne : p i j ≠ p i l := fun h => not_le hjl (le_of_eq h)
    intro h
    rcases (pair_mem_sd_iff_adj hne).mp h with hjl' | hlj
    · exact not_le hjl hjl'.le
    · exact not_le hjl.symm hlj.le

/-- The ordinary barycentric subdivision of a complex with a face of at least
nine vertices cannot satisfy the two-colour restriction-mixing criterion. The
nine faces of sizes one, four and seven supply three independent triples with
every edge between different triples. Two uses of the pigeonhole principle
give a monochromatic induced four-cycle. -/
theorem false_of_mixed_restrictions_sd_of_nine_vertices
    {L : PreAbstractSimplicialComplex V} {F : Finset V} (hF : F ∈ L) (hcard : 9 ≤ F.card)
    {n : ℕ} (prefixes : ℕ → PreAbstractSimplicialComplex (Face L)) (grows : Monotone prefixes)
    (initial : Finset (Face L)) (initial_eq : prefixes 0 = simplex initial)
    (final_eq : prefixes n = sd L)
    (facet restriction : ℕ → Finset (Face L)) (label : Face L → Fin 2)
    (facet_mem : ∀ j < n, facet j ∈ prefixes (j + 1))
    (restriction_nonempty : ∀ j < n, (restriction j).Nonempty ∨ prefixes j = ⊥)
    (new_faces : ∀ j < n, ∀ s, s ∈ prefixes (j + 1) ∧ s ∉ prefixes j ↔
      s.Nonempty ∧ restriction j ⊆ s ∧ s ⊆ facet j)
    (mixed : ∀ j < n, 2 ≤ (restriction j).card →
      ∃ x ∈ restriction j, ∃ y ∈ restriction j, label x ≠ label y) : False := by
  obtain ⟨p, cross, diagonal⟩ := exists_tripartite_in_sd hF hcard
  have hsmall : Fintype.card (Fin 2) < Fintype.card (Fin 3) := by simp
  have repeat_colour (i : Fin 3) :
      ∃ a b : Fin 3, a ≠ b ∧ label (p i a) = label (p i b) :=
    Fintype.exists_ne_map_eq_of_card_lt (fun j => label (p i j)) hsmall
  choose a b distinct same_colour using repeat_colour
  obtain ⟨i, k, hik, same_rows⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun i => label (p i (a i))) hsmall
  let col (i : Fin 3) (s : Fin 2) : Fin 3 := if s = 0 then a i else b i
  have col_ne (i : Fin 3) : col i 0 ≠ col i 1 := by
    have h : (1 : Fin 2) ≠ 0 := by
      intro he
      exact Nat.one_ne_zero (congrArg Fin.val he)
    simpa [col, h] using distinct i
  have col_colour (i : Fin 3) (s : Fin 2) : label (p i (col i s)) = label (p i (a i)) := by
    by_cases hs : s = 0
    · simp only [col, ite_eq_left hs]
    · simpa only [col, ite_eq_right hs] using (same_colour i).symm
  refine false_of_monochromatic_four_cycle prefixes grows initial initial_eq facet restriction
    label facet_mem restriction_nonempty new_faces mixed (fun s => p i (col i s))
    (fun s => p k (col k s)) (label (p i (a i))) ?_ ?_ ?_ (col_colour i) ?_
  · intro r s
    rw [final_eq]
    exact cross hik (col i r) (col k s)
  · rw [final_eq]
    exact diagonal i (col_ne i)
  · rw [final_eq]
    exact diagonal k (col_ne k)
  · intro s
    exact (col_colour k s).trans same_rows.symm

end

end D5.S3.Topology.StableCategory.ShellingColourObstruction
