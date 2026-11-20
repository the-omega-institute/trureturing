/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TwentyTwoSingletonLabels
   generality: G
   mirror-B: none(waiver:covered-by-q9-twenty-two-paired-exclusion-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Matching]
   utility: none
   digest: Label the high vertices and subdivision edges in a singleton compression. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoCompression
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoSingletonPlacements

/-! Assign the three attachment labels in the cubical search to the actual
vertices attached in pairs to the six-cycle. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoSingletonLabels

open Finset SimpleGraph
open private cycleLabel pairingModel singleton_class_cycle from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoCompression
open private attachment solid hollow labels hollowEdges from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoSingletonPlacements
open private SideHigh compressed from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointCompression

private def representative (opposite : Bool) : Fin 3 → Fin 6 :=
  if opposite then ![0, 1, 2] else ![0, 1, 3]

private def rootIndex (i : Fin 3) : Fin 10 := ⟨i.val + 1, by omega⟩

private theorem pair_labels :
    ∀ (opposite : Bool) (j : Fin 3) (i : Fin 6),
      (i = representative opposite j ∨ i = pairingModel opposite (representative opposite j)) ↔
        attachment opposite i = rootIndex j := by
  decide +kernel

private theorem representative_label :
    ∀ (opposite : Bool) (j : Fin 3),
      attachment opposite (representative opposite j) = rootIndex j := by
  decide

private theorem cycleLabel_injective (shift : Fin 6) (reverse : Bool) :
    Function.Injective (cycleLabel shift reverse) := by
  exact (show ∀ (t : Fin 6) (b : Bool) (i j : Fin 6), cycleLabel t b i = cycleLabel t b j → i = j
    by decide +kernel) shift reverse

/-- The three attachment vertices can be labeled so that their incidences
to the cycle vertices agree exactly with the model used by the search. -/
theorem label_attachments {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (A : Finset V) (hA : A.card = 3)
    (cyc : Fin 6 ↪ V) (opposite : Bool)
    (hpair : ∀ i : Fin 6, ∃ x ∈ A, H.neighborFinset x = {cyc i, cyc (pairingModel opposite i)}) :
    ∃ roots : Fin 3 ↪ V, Finset.univ.image roots = A ∧
      ∀ j i, H.Adj (roots j) (cyc i) ↔ attachment opposite i = rootIndex j := by
  choose r hr hrN using fun j : Fin 3 => hpair (representative opposite j)
  have hlink (j : Fin 3) (i : Fin 6) :
      H.Adj (r j) (cyc i) ↔ attachment opposite i = rootIndex j := by
    rw [← H.mem_neighborFinset, hrN]
    simpa only [Finset.mem_insert, Finset.mem_singleton, cyc.injective.eq_iff] using
      pair_labels opposite j i
  have hinj : Function.Injective r := by
    intro j k h
    have hj := (hlink j (representative opposite j)).mpr (representative_label opposite j)
    rw [h] at hj
    have he := (hlink k (representative opposite j)).mp hj
    rw [representative_label] at he
    apply Fin.ext
    have hv := congrArg Fin.val he
    change j.val + 1 = k.val + 1 at hv
    omega
  let roots : Fin 3 ↪ V := ⟨r, hinj⟩
  refine ⟨roots, Finset.eq_of_subset_of_card_le ?_ ?_, hlink⟩
  · intro x hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    exact hr j
  · rw [hA, Finset.card_image_of_injective _ roots.injective, Finset.card_univ, Fintype.card_fin]

/-- Apply the labeling to the cycle isomorphism and the dihedral relabeling
produced by the actual compression. -/
theorem label_paired_cycle {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (A B : Finset V) (hA : A.card = 3)
    (e : cycleGraph 6 ≃g H.induce (B : Set V)) (shift : Fin 6) (reverse opposite : Bool)
    (hpair : ∀ i : Fin 6, ∃ x ∈ A, H.neighborFinset x =
      {(e (cycleLabel shift reverse i)).val,
        (e (cycleLabel shift reverse (pairingModel opposite i))).val}) :
    ∃ roots : Fin 3 ↪ V, Finset.univ.image roots = A ∧
      ∀ j i, H.Adj (roots j) (e (cycleLabel shift reverse i)).val ↔
        attachment opposite i = rootIndex j := by
  let c : Fin 6 ↪ V := ⟨fun i => (e (cycleLabel shift reverse i)).val,
    fun _ _ h => cycleLabel_injective shift reverse (e.injective (Subtype.ext h))⟩
  exact label_attachments H A hA c opposite hpair

#print axioms label_paired_cycle

private def cycleIndex (i : Fin 6) : Fin 10 := ⟨i.val + 4, by omega⟩

private theorem split_index :
    ∀ i : Fin 10, i = 0 ∨ (∃ j, i = rootIndex j) ∨ ∃ j, i = cycleIndex j := by
  decide

private theorem solid_cases :
    ∀ i j : Fin 10, solid i j = true ↔
      (i = 0 ∧ ∃ k, j = rootIndex k) ∨ j = 0 ∧ ∃ k, i = rootIndex k := by
  decide

private theorem hollow_cases :
    ∀ (b : Bool) (i j : Fin 10), hollow b i j = true →
      (∃ u v, i = cycleIndex u ∧ j = cycleIndex v ∧ (cycleGraph 6).Adj u v) ∨
      (∃ u v, i = rootIndex u ∧ j = cycleIndex v ∧ attachment b v = rootIndex u) ∨
      ∃ u v, i = cycleIndex v ∧ j = rootIndex u ∧ attachment b v = rootIndex u := by
  decide +kernel

private theorem cycleLabel_adj :
    ∀ (shift : Fin 6) (reverse : Bool) (i j : Fin 6),
      (cycleGraph 6).Adj i j →
        (cycleGraph 6).Adj (cycleLabel shift reverse i) (cycleLabel shift reverse j) := by
  decide +kernel

attribute [local instance] Classical.propDecidable

/-- The singleton-parity compression realizes the two labeled graphs used by
the embedding search, with ten actual high vertices and a degree-two
subdivision of each specified hollow edge. -/
theorem singleton_model {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hp : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {x y}, G.Adj x y → G.degree x = 2 → G.degree y = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL : Fintype.card (SideHigh G L) = 1)
    (hR : Fintype.card (SideHigh G R) = 9) :
    ∃ (b : Bool) (p : Fin 10 ↪ V), (∀ i, G.degree (p i) = 3) ∧
      (∀ i j, G.Adj (p i) (p j) ↔ solid i j = true) ∧
      ∀ i j, hollow b i j = true →
        ∃ m, G.degree m = 2 ∧ G.Adj (p i) m ∧ G.Adj (p j) m := by
  obtain ⟨r, ha, _, _, e, shift, reverse, b, hpair⟩ :=
    singleton_class_cycle hp hdeg (fun hxy hx hy => hlow hxy hx hy) hg hL hR
  let A := Finset.univ.filter (fun x : SideHigh G R => G.Adj r.val x.val)
  let B := Finset.univ \ A
  let H := compressed G R
  obtain ⟨roots, hroots, hlink⟩ := label_paired_cycle H A B ha e shift reverse b hpair
  let cyc : Fin 6 ↪ SideHigh G R := ⟨fun i => (e (cycleLabel shift reverse i)).val,
    fun _ _ h => cycleLabel_injective shift reverse (e.injective (Subtype.ext h))⟩
  have hrA (i : Fin 3) : roots i ∈ A := by
    rw [← hroots]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hcB (i : Fin 6) : cyc i ∈ B := (e (cycleLabel shift reverse i)).property
  have hrc (i : Fin 3) (j : Fin 6) : roots i ≠ cyc j :=
    fun he => (Finset.mem_sdiff.mp (hcB j)).2 (he ▸ hrA i)
  have hLR (x : SideHigh G R) : r.val ≠ x.val := by
    intro he
    have hr := (Finset.mem_filter.mp r.property).1
    have hx := (Finset.mem_filter.mp x.property).1
    exact Set.disjoint_left.mp hp.disjoint hr (he.symm ▸ hx)
  let p : Fin 10 → V :=
    Fin.append (Fin.cases r.val (fun i : Fin 3 => (roots i).val)) (fun i => (cyc i).val)
  have p0 : p 0 = r.val := by rfl
  have pr (i : Fin 3) : p (rootIndex i) = (roots i).val := by
    change p (i.succ.castAdd 6) = _
    simp only [p, Fin.append_left, Fin.cases_succ]
  have pc (i : Fin 6) : p (cycleIndex i) = (cyc i).val := by
    have hi : cycleIndex i = i.natAdd 4 := Fin.ext (by simp [cycleIndex, Nat.add_comm])
    simp only [p, hi, Fin.append_right]
  have hinj : Function.Injective p := by
    intro i j he
    rcases split_index i with rfl | ⟨u, rfl⟩ | ⟨u, rfl⟩ <;>
      rcases split_index j with rfl | ⟨v, rfl⟩ | ⟨v, rfl⟩
    · rfl
    · exact (hLR (roots v) (by simpa only [p0, pr] using he)).elim
    · exact (hLR (cyc v) (by simpa only [p0, pc] using he)).elim
    · exact (hLR (roots u) (by simpa only [p0, pr] using he.symm)).elim
    · exact congrArg rootIndex (roots.injective (Subtype.ext (by simpa only [pr] using he)))
    · exact (hrc u v (Subtype.ext (by simpa only [pr, pc] using he))).elim
    · exact (hLR (cyc u) (by simpa only [p0, pc] using he.symm)).elim
    · exact (hrc v u (Subtype.ext (by simpa only [pr, pc] using he.symm))).elim
    · exact congrArg cycleIndex (cyc.injective (Subtype.ext (by simpa only [pc] using he)))
  let p' : Fin 10 ↪ V := ⟨p, hinj⟩
  have haR (u v : SideHigh G R) : ¬G.Adj u.val v.val := by
    intro huv
    have hu := (Finset.mem_filter.mp u.property).1
    have hv := (Finset.mem_filter.mp v.property).1
    exact Set.disjoint_left.mp hp.disjoint (hp.mem_of_mem_adj' hu huv.symm) hv
  have hr_adj (i : Fin 3) : G.Adj r.val (roots i).val :=
    (Finset.mem_filter.mp (hrA i)).2
  have hc_non (i : Fin 6) : ¬G.Adj r.val (cyc i).val :=
    fun h => (Finset.mem_sdiff.mp (hcB i)).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  refine ⟨b, p', ?_, ?_, ?_⟩
  · intro i
    change G.degree (p i) = 3
    rcases split_index i with rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [p0]; exact (Finset.mem_filter.mp r.property).2
    · rw [pr]; exact (Finset.mem_filter.mp (roots j).property).2
    · rw [pc]; exact (Finset.mem_filter.mp (cyc j).property).2
  · intro i j
    change G.Adj (p i) (p j) ↔ _
    have hzero : ∀ j, solid 0 j = true ↔ ∃ i, j = rootIndex i := by decide
    have hsym : ∀ i j, solid i j = solid j i := by decide
    have hroot : ∀ i, rootIndex i ≠ 0 := by decide
    have hcyc : ∀ i, cycleIndex i ≠ 0 := by decide
    have hnone : ∀ i j, cycleIndex i ≠ rootIndex j := by decide
    rcases split_index i with rfl | ⟨u, rfl⟩ | ⟨u, rfl⟩ <;>
      rcases split_index j with rfl | ⟨v, rfl⟩ | ⟨v, rfl⟩
    · simp only [p0, G.loopless.irrefl, hzero]
      exact ⟨False.elim, fun ⟨i, h⟩ => hroot i h.symm⟩
    · simp [p0, pr, hzero, hr_adj v]
    · simp [p0, pc, hzero, hc_non v, hnone]
    · rw [G.adj_comm, hsym]; simp [p0, pr, hzero, hr_adj u]
    · simp [pr, solid_cases, hroot, haR]
    · simp [pr, pc, solid_cases, hroot, hcyc, haR]
    · rw [G.adj_comm, hsym]; simp [p0, pc, hzero, hc_non u, hnone]
    · simp [pr, pc, solid_cases, hroot, hcyc, haR]
    · simp [pc, solid_cases, hcyc, haR]
  · intro i j hij
    change ∃ m, G.degree m = 2 ∧ G.Adj (p i) m ∧ G.Adj (p j) m
    rcases hollow_cases b i j hij with ⟨u, v, rfl, rfl, huv⟩ |
      ⟨u, v, rfl, rfl, huv⟩ | ⟨u, v, rfl, rfl, huv⟩
    · have hc : H.Adj (cyc u) (cyc v) :=
        e.map_rel_iff.mpr (cycleLabel_adj shift reverse u v huv)
      simpa only [pc] using hc.2
    · have hx : H.Adj (roots u) (cyc v) := (hlink u v).mpr huv
      simpa only [pr, pc] using hx.2
    · have hx : H.Adj (cyc v) (roots u) := ((hlink u v).mpr huv).symm
      simpa only [pr, pc] using hx.2

#print axioms singleton_model

private theorem mem_hollowEdges (b : Bool) (e : Fin 10 × Fin 10) :
    e ∈ hollowEdges b ↔ e.1 < e.2 ∧ hollow b e.1 e.2 = true := by
  rcases e with ⟨i, j⟩
  simp [hollowEdges, labels, List.mem_flatMap, List.mem_map]

/-- Choose distinct degree-two subdivision vertices for a list of ordered
endpoint pairs of an injective vertex placement. -/
theorem select_subdivision_vertices_of_paths {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (p : Fin 10 ↪ V) (edges : List (Fin 10 × Fin 10))
    (ordered : ∀ e ∈ edges, e.1 < e.2)
    (hmid : ∀ e ∈ edges, ∃ m, G.degree m = 2 ∧ G.Adj (p e.1) m ∧ G.Adj (p e.2) m) :
    ∃ f : Fin 10 × Fin 10 → V,
      (∀ e ∈ edges, G.degree (f e) = 2 ∧ G.neighborFinset (f e) = {p e.1, p e.2}) ∧
      Set.InjOn f {e | e ∈ edges} := by
  let f (e : Fin 10 × Fin 10) : V :=
    if he : e ∈ edges then Classical.choose (hmid e he) else p 0
  have hf (e : Fin 10 × Fin 10) (he : e ∈ edges) :
      G.degree (f e) = 2 ∧ G.neighborFinset (f e) = {p e.1, p e.2} := by
    have hlt := ordered e he
    have hdata : G.degree (f e) = 2 ∧ G.Adj (p e.1) (f e) ∧ G.Adj (p e.2) (f e) := by
      have hfe : f e = Classical.choose (hmid e he) := dite_eq_left he
      rw [hfe]
      exact Classical.choose_spec (hmid e he)
    refine ⟨hdata.1, (Finset.eq_of_subset_of_card_le ?_ ?_).symm⟩
    · rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨(G.mem_neighborFinset _ _).mpr hdata.2.1.symm,
        (G.mem_neighborFinset _ _).mpr hdata.2.2.symm⟩
    · simp [G.card_neighborFinset_eq_degree, hdata.1, p.injective.ne hlt.ne]
  refine ⟨f, hf, ?_⟩
  intro e he d hd hed
  have he' := ordered e he
  have hd' := ordered d hd
  have heq : ({p e.1, p e.2} : Finset V) = {p d.1, p d.2} := by
    rw [← (hf e he).2, hed, (hf d hd).2]
  have h1 : p e.1 ∈ ({p d.1, p d.2} : Finset V) := by rw [← heq]; exact mem_insert_self _ _
  have h2 : p e.2 ∈ ({p d.1, p d.2} : Finset V) := by rw [← heq]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton, p.injective.eq_iff] at h1 h2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact (he'.ne (h1.trans h2.symm)).elim
  · exact Prod.ext h1 h2
  · exact (he'.not_ge (h2.trans_lt (hd'.trans_eq h1.symm)).le).elim
  · exact (he'.ne (h1.trans h2.symm)).elim

/-- Choose the twelve distinct subdivision vertices, with their exact
two-element neighborhoods, from a realization of the singleton model. -/
theorem select_subdivision_vertices {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (b : Bool) (p : Fin 10 ↪ V)
    (hmid : ∀ i j, hollow b i j = true →
      ∃ m, G.degree m = 2 ∧ G.Adj (p i) m ∧ G.Adj (p j) m) :
    ∃ f : Fin 10 × Fin 10 → V,
      (∀ e ∈ hollowEdges b, G.degree (f e) = 2 ∧ G.neighborFinset (f e) = {p e.1, p e.2}) ∧
      Set.InjOn f {e | e ∈ hollowEdges b} :=
  select_subdivision_vertices_of_paths G p (hollowEdges b)
    (fun e he => ((mem_hollowEdges b e).mp he).1)
    (fun e he => hmid _ _ ((mem_hollowEdges b e).mp he).2)

#print axioms select_subdivision_vertices

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoSingletonLabels
