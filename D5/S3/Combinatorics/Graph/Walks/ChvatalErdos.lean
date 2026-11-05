/- GID: D5/S3/Combinatorics/Graph/Walks/ChvatalErdos
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/ChvatalErdos
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Hamiltonian]
   utility: none
   digest: Deletion connectivity and the matching independence bound force Hamiltonicity. -/
import D5.S3.Combinatorics.Graph.Walks.ConnectivityFan
import D5.S3.Combinatorics.Graph.Walks.CycleDetour

/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in
docs/reports/licenses/menger-hamiltonian-LICENSE.txt.
Authors: Juan Pablo Traverso Gianini

Adapted from MengerHamilton/ChvatalErdosAux.lean, chvatal_erdos_aux, in
jtraverso/menger-hamiltonian at 35c5f684f9bfbd244bd0999ce725623ab571adb6.
Cycle rotation and native darts express the successor relation without cyclic arrays.
Source pins: Lean v4.35.0-rc3, Mathlib c55e6e786f49471c72fbddbec5415808896aec1e.
Receiver pins: Lean v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.ChvatalErdos

open SimpleGraph ConnectivityFan CycleDetour
open scoped Classical

universe u
variable {V : Type u} {G : SimpleGraph V} {base : V}

private noncomputable def successor (cycle : G.Walk base base)
    (vertex : {vertex // vertex ∈ cycle.support}) : V :=
  (cycle.rotate vertex.val vertex.property).snd

private lemma successor_dart_mem (cycle : G.Walk base base) (hcycle : cycle.IsCycle)
    (vertex : {vertex // vertex ∈ cycle.support}) :
    (cycle.rotate vertex.val vertex.property).firstDart
      (hcycle.rotate vertex.property).not_nil ∈ cycle.darts :=
  (cycle.rotate_darts vertex.val vertex.property).perm.mem_iff.mp
    (Walk.firstDart_mem_darts (hcycle.rotate vertex.property).not_nil)

private lemma successor_mem (cycle : G.Walk base base) (hcycle : cycle.IsCycle)
    (vertex : {vertex // vertex ∈ cycle.support}) : successor cycle vertex ∈ cycle.support :=
  cycle.dart_snd_mem_support_of_mem_darts (successor_dart_mem cycle hcycle vertex)

private lemma successor_injective (cycle : G.Walk base base) (hcycle : cycle.IsCycle) :
    Function.Injective (successor cycle) := by
  intro left right heq
  have hnodup : (cycle.darts.map (fun dart : G.Dart => dart.snd)).Nodup := by
    rw [Walk.map_snd_darts]
    exact hcycle.support_nodup
  have hdarts := List.inj_on_of_nodup_map hnodup
    (successor_dart_mem cycle hcycle left) (successor_dart_mem cycle hcycle right) heq
  exact Subtype.ext (congrArg (fun dart : G.Dart => dart.fst) hdarts)

private lemma longer_cycle (cycle : G.Walk base base) (hcycle : cycle.IsCycle)
    (left right : {vertex // vertex ∈ cycle.support}) (hne : left.val ≠ right.val)
    (detour : G.Walk left.val right.val) (hdetour : detour.IsPath)
    (hlength : 2 ≤ detour.length)
    (hclean : ∀ vertex ∈ detour.support, vertex ∈ cycle.support →
      vertex = left.val ∨ vertex = right.val)
    (hadj : G.Adj (successor cycle left) (successor cycle right)) :
    ∃ root, ∃ extended : G.Walk root root,
      extended.IsCycle ∧ extended.length = cycle.length + detour.length - 1 := by
  classical
  let rotated := cycle.rotate left.val left.property
  have hrotated : rotated.IsCycle := hcycle.rotate left.property
  let closing := rotated.adj_snd hrotated.not_nil
  let path := rotated.tail
  have hcons : path.cons closing = rotated := rotated.cons_tail_eq hrotated.not_nil
  have hright : right.val ∈ path.support := by
    have hmem : right.val ∈ rotated.support :=
      (cycle.mem_support_rotate_iff left.val left.property).mpr right.property
    rw [← hcons, Walk.support_cons, List.mem_cons] at hmem
    exact hmem.resolve_left (Ne.symm hne)
  obtain ⟨index, hvertex, hindexLe⟩ := Walk.mem_support_iff_exists_getVert.mp hright
  have hindex : index < path.length := by
    by_contra hnot
    have heq : index = path.length := by omega
    rw [heq, Walk.getVert_length] at hvertex
    exact hne hvertex
  let dart := path.darts[index]'(by simpa using hindex)
  have hfst : dart.fst = right.val := by
    simpa only [dart, Walk.darts_getElem_eq_getVert] using hvertex
  have hsnd : dart.snd = path.getVert (index + 1) := by
    simp only [dart, Walk.darts_getElem_eq_getVert]
  have hdart : dart ∈ cycle.darts := by
    apply (cycle.rotate_darts left.val left.property).perm.mem_iff.mp
    change dart ∈ rotated.darts
    rw [← hcons, Walk.darts_cons]
    exact List.mem_cons_of_mem _ (List.getElem_mem _)
  have hnodup : (cycle.darts.map (fun dart : G.Dart => dart.fst)).Nodup := by
    rw [Walk.map_fst_darts]
    exact hcycle.nodup_dropLast_support
  have hdeq := List.inj_on_of_nodup_map hnodup hdart
    (successor_dart_mem cycle hcycle right) hfst
  have hsuccessor : path.getVert (index + 1) = successor cycle right :=
    hsnd.symm.trans (congrArg (fun dart : G.Dart => dart.snd) hdeq)
  obtain ⟨extended, hextended, hextendedLength, _⟩ := exists_cycle_through_detour closing path
    (by rw [hcons]; exact hrotated) index hindex (detour.copy rfl hvertex.symm)
    (by simpa using hdetour) (by simpa using hlength) (by
      intro vertex hmem hcycleMem
      have hmem' : vertex ∈ cycle.support := by
        rw [hcons] at hcycleMem
        exact (cycle.mem_support_rotate_iff left.val left.property).mp hcycleMem
      simpa only [hvertex] using hclean vertex (by simpa using hmem) hmem') (by
      rw [hsuccessor]
      exact hadj)
  refine ⟨_, extended, hextended, ?_⟩
  simpa only [hcons, rotated, Walk.length_rotate, Walk.length_copy] using hextendedLength

theorem isHamiltonian_of_connectivity_independence [Finite V] (G : SimpleGraph V) (k : ℕ)
    (hn : 3 ≤ Nat.card V)
    (hconn : ∀ S : Set V, S.ncard < k → (G.induce Sᶜ).Connected)
    (hindependence : ∀ S : Set V, G.IsIndepSet S → S.ncard ≤ k) :
    letI := Fintype.ofFinite V
    G.IsHamiltonian := by
  classical
  letI := Fintype.ofFinite V
  have hn' : 3 ≤ Fintype.card V := by simpa only [Nat.card_eq_fintype_card] using hn
  by_cases hall : ∀ left right : V, left ≠ right → G.Adj left right
  · have htop : G = ⊤ := by
      ext left right
      exact ⟨fun hadj => hadj.ne, hall left right⟩
    rw [htop]
    exact SimpleGraph.isHamiltonian_top hn'
  push Not at hall
  obtain ⟨left, right, hne, hnonadjacent⟩ := hall
  have hk : 2 ≤ k := by
    have hbound := hindependence {left, right} (by
      intro first hfirst second hsecond hdistinct
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hfirst hsecond
      rcases hfirst with rfl | rfl <;> rcases hsecond with rfl | rfl
      · exact (hdistinct rfl).elim
      · exact hnonadjacent
      · exact fun hadj => hnonadjacent hadj.symm
      · exact (hdistinct rfl).elim)
    rwa [Set.ncard_pair hne] at hbound
  obtain ⟨root, cycle, hcycle, hmaximal, hfans⟩ := exists_maximal_cycle_fans hn hk hconn
  by_contra hnot
  obtain ⟨outside, houtside⟩ : ∃ outside, outside ∉ cycle.support := by
    by_contra! hfull
    exact hnot (Walk.isHamiltonianCycle_iff_isCycle_and_forall_mem_support.mpr
      ⟨hcycle, hfull⟩).isHamiltonian
  obtain ⟨endpoint, paths, hpaths, hdisjoint, hinjective⟩ := hfans outside houtside
  let terminal := fun index => (⟨endpoint index, (hpaths index).1⟩ :
    {vertex // vertex ∈ cycle.support})
  let next := fun index => successor cycle (terminal index)
  have hnextMem : ∀ index, next index ∈ cycle.support :=
    fun index => successor_mem cycle hcycle (terminal index)
  have hnextAdj : ∀ index, G.Adj (endpoint index) (next index) :=
    fun index => (cycle.rotate (endpoint index) (hpaths index).1).adj_snd
      (hcycle.rotate (hpaths index).1).not_nil
  have hlonger : ∀ (first second : {vertex // vertex ∈ cycle.support})
      (detour : G.Walk first.val second.val), first.val ≠ second.val →
      detour.IsPath → 2 ≤ detour.length →
      (∀ vertex ∈ detour.support, vertex ∈ cycle.support →
        vertex = first.val ∨ vertex = second.val) →
      G.Adj (successor cycle first) (successor cycle second) → False := by
    intro first second detour hne hpath hlength hclean hadj
    obtain ⟨base, extended, hextended, hlength'⟩ :=
      longer_cycle cycle hcycle first second hne detour hpath hlength hclean hadj
    have hbound := hmaximal base extended hextended
    omega
  have hpathLength : ∀ index, 1 ≤ (paths index).length := by
    intro index
    by_contra hzero
    have heq := Walk.eq_of_length_eq_zero (by omega : (paths index).length = 0)
    exact houtside (heq ▸ (hpaths index).1)
  have htail : ∀ index, outside ∉ (paths index).support.tail := by
    intro index hmem
    have hnodup := (hpaths index).2.1.support_nodup
    rw [← Walk.cons_tail_support] at hnodup
    exact (List.nodup_cons.mp hnodup).1 hmem
  have hpair : ∀ first second, first ≠ second → ¬ G.Adj (next first) (next second) := by
    intro first second hne hadj
    apply hlonger (terminal first) (terminal second) ((paths first).reverse.append (paths second))
      (fun heq => hne (hinjective heq)) _ _ _ hadj
    · rw [Walk.isPath_def, Walk.support_append, Walk.support_reverse, List.nodup_append]
      refine ⟨List.nodup_reverse.mpr (hpaths first).2.1.support_nodup,
        (hpaths second).2.1.support_nodup.sublist (List.tail_sublist _), ?_⟩
      intro vertex hfirst other hsecond heq
      subst heq
      have heq' := hdisjoint first second hne vertex (List.mem_reverse.mp hfirst)
        (List.mem_of_mem_tail hsecond)
      exact htail second (heq' ▸ hsecond)
    · simp only [Walk.length_append, Walk.length_reverse]
      have := hpathLength first
      have := hpathLength second
      omega
    · intro vertex hmem hmemCycle
      rw [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse] at hmem
      rcases hmem with hmem | hmem
      · exact Or.inl ((hpaths first).2.2 vertex hmem hmemCycle)
      · exact Or.inr ((hpaths second).2.2 vertex hmem hmemCycle)
  have hconsecutive : ∀ first second, endpoint second ≠ next first := by
    intro first second heq
    by_cases hsame : first = second
    · subst hsame
      exact (hnextAdj first).ne heq
    · apply hpair first second hsame
      rw [← heq]
      exact hnextAdj second
  have houtsideNext : ∀ index, ¬ G.Adj outside (next index) := by
    intro index hadj
    have hne := (hnextAdj index).ne
    have hmissing : next index ∉ (paths index).support := fun hmem =>
      hne ((hpaths index).2.2 _ hmem (hnextMem index)).symm
    apply hlonger (terminal index) ⟨next index, hnextMem index⟩
      ((paths index).reverse.concat hadj) hne _ _ _
      ((cycle.rotate (next index) (hnextMem index)).adj_snd
        (hcycle.rotate (hnextMem index)).not_nil)
    · rw [Walk.isPath_def, Walk.support_concat, Walk.support_reverse, List.nodup_append]
      refine ⟨List.nodup_reverse.mpr (hpaths index).2.1.support_nodup,
        List.nodup_singleton _, ?_⟩
      intro vertex hvertex other hother heq
      rw [List.mem_singleton] at hother
      subst hother heq
      exact hmissing (List.mem_reverse.mp hvertex)
    · simp only [Walk.length_concat, Walk.length_reverse]
      have := hpathLength index
      omega
    · intro vertex hmem hmemCycle
      rw [Walk.support_concat, Walk.support_reverse, List.mem_append,
        List.mem_reverse, List.mem_singleton] at hmem
      rcases hmem with hmem | rfl
      · exact Or.inl ((hpaths index).2.2 vertex hmem hmemCycle)
      · exact Or.inr rfl
  have hsize : k ≤ min k cycle.length := by
    by_contra hsmall
    have hcycleSize : cycle.length ≤ min k cycle.length := by omega
    have hpositive : 0 < min k cycle.length := by
      have := hcycle.three_le_length
      omega
    let first : Fin (min k cycle.length) := ⟨0, hpositive⟩
    have hcover : Finset.univ.image endpoint = cycle.support.toFinset := by
      apply Finset.eq_of_subset_of_card_le
      · intro vertex hmem
        obtain ⟨index, _, rfl⟩ := Finset.mem_image.mp hmem
        simpa using (hpaths index).1
      · rw [Finset.card_image_of_injective _ hinjective, Finset.card_univ, Fintype.card_fin,
          Walk.IsCycle.support_toFinset_card hcycle]
        exact hcycleSize
    have hmem : next first ∈ Finset.univ.image endpoint := by
      rw [hcover]
      simpa using hnextMem first
    obtain ⟨second, _, heq⟩ := Finset.mem_image.mp hmem
    exact hconsecutive first second heq
  have hnextInjective : Function.Injective next := by
    intro first second heq
    have heq' := successor_injective cycle hcycle heq
    exact hinjective (congrArg Subtype.val heq')
  let independent := insert outside (Finset.univ.image next)
  have hcard : independent.card = min k cycle.length + 1 := by
    rw [Finset.card_insert_of_notMem, Finset.card_image_of_injective _ hnextInjective,
      Finset.card_univ, Fintype.card_fin]
    intro hmem
    obtain ⟨index, _, heq⟩ := Finset.mem_image.mp hmem
    exact houtside (heq ▸ hnextMem index)
  have hindependent : G.IsIndepSet (independent : Set V) := by
    intro first hfirst second hsecond hne hadj
    simp only [independent, Finset.coe_insert, Finset.coe_image, Finset.coe_univ,
      Set.image_univ, Set.mem_insert_iff, Set.mem_range] at hfirst hsecond
    rcases hfirst with rfl | ⟨first, rfl⟩ <;> rcases hsecond with rfl | ⟨second, rfl⟩
    · exact hne rfl
    · exact houtsideNext second hadj
    · exact houtsideNext first hadj.symm
    · exact hpair first second (fun heq => hne (heq ▸ rfl)) hadj
  have hbound := hindependence _ hindependent
  rw [Set.ncard_coe_finset, hcard] at hbound
  omega

end D5.S3.Combinatorics.Graph.Walks.ChvatalErdos
