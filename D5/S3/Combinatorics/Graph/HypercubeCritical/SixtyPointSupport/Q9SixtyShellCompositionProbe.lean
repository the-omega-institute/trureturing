/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SixtyPointSupport/Q9SixtyShellCompositionProbe
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SixtyPointSupport/Q9SixtyShellCompositionProbe
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Count the layers of a sixty-vertex support with respect to each root, using cubic degree and the minimum distance between vertices of each parity. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.SixtyPointSupport.Q9FourthLeafSignProbe
import D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Clique

/-! Distance counts for the sixty-point case. -/

noncomputable section

attribute [local instance] Classical.propDecidable

open SimpleGraph
open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical
open BalancedCriticalSpectrum (Q)
open private distance_double_count distance_parity from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction
open private cubeParity from D5.S3.Combinatorics.Graph.HypercubeSubQuorum

private def shell (C : Finset (Q 9)) (x : Q 9) (k : ℕ) : Finset (Q 9) :=
  C.filter (fun y => hammingDist x y = k)

private lemma literal_half_small_of_sixty_partner_bound (C : Finset (Q 9))
    (hc : C.card = 60)
    (hdiam : ∀ x ∈ C, ∀ y ∈ C, hammingDist x y ≤ 7)
    (hregular : ∀ x ∈ C, (shell C x 1).card = 3)
    (hparity : ∀ b : Bool, (C.filter (fun x => cubeParity x = b)).card = 30)
    (h₂ : ∀ x ∈ C, 6 ≤ (shell C x 2).card)
    (h₃ : ∀ x ∈ C, 12 ≤ (shell C x 3).card)
    (h₂₄ : ∀ x ∈ C, 18 ≤ (shell C x 2).card + (shell C x 4).card)
    (h₇ : ∀ x ∈ C, (shell C x 7).card ≤ 5) :
    ∃ i : Fin 9, ∃ b : Bool, (C.filter (fun x => x i = b)).card ≤ 21 := by
  have root_sum (x : Q 9) (hx : x ∈ C) : (∑ y ∈ C, hammingDist x y) ≤ 250 := by
    have hsum (f : ℕ → ℕ) : (∑ k ∈ Finset.range 8, (shell C x k).card * f k) =
        ∑ y ∈ C, f (hammingDist x y) := by
      simpa only [shell, Finset.sum_const, smul_eq_mul] using
        Finset.sum_fiberwise_of_maps_to' (s := C) (t := Finset.range 8)
          (g := hammingDist x) (fun y hy => Finset.mem_range.mpr (by
            have := hdiam x hx y hy
            omega)) f
    have hzero : (shell C x 0).card = 1 := by
      have heq : shell C x 0 = {x} := by
        ext y
        simp only [shell, Finset.mem_filter, Finset.mem_singleton, hammingDist_eq_zero]
        constructor
        · exact fun h => h.2.symm
        · rintro rfl
          exact ⟨hx, rfl⟩
      simp [heq]
    have heven : (∑ y ∈ C, if hammingDist x y % 2 = 0 then 1 else 0) = 30 := by
      rw [← Finset.card_filter]
      have heq : (C.filter fun y => hammingDist x y % 2 = 0) =
          C.filter (fun y => cubeParity y = cubeParity x) := by
        ext y
        simp only [Finset.mem_filter, distance_parity]
        exact and_congr_right (fun _ => eq_comm)
      rw [heq, hparity]
    have hall := hsum (fun _ => 1)
    have he := (hsum (fun k => if k % 2 = 0 then 1 else 0)).trans heven
    have hd := hsum id
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMod, ite_true,
      Nat.mul_one, Nat.mul_zero, Nat.zero_add, Nat.add_zero, id_eq] at hall he hd
    simp only [Finset.sum_const, smul_eq_mul, Nat.mul_one, hc] at hall
    have hh₁ := hregular x hx
    have hh₂ := h₂ x hx
    have hh₃ := h₃ x hx
    have hh₂₄ := h₂₄ x hx
    have hh₇ := h₇ x hx
    omega
  by_contra! hlarge
  have hprod (i : Fin 9) : 836 ≤
      (C.filter (fun x => x i = false)).card * (C.filter (fun x => x i = true)).card := by
    have hparts := Finset.card_filter_add_card_filter_not (s := C) (fun x => x i = false)
    have hnot : C.filter (fun x => ¬x i = false) = C.filter (fun x => x i = true) := by
      ext x
      cases x i <;> simp
    rw [hnot, hc] at hparts
    obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le (show 22 ≤ _ from hlarge i false)
    obtain ⟨v, hv⟩ := Nat.exists_eq_add_of_le (show 22 ≤ _ from hlarge i true)
    nlinarith [Nat.zero_le (u * v)]
  have hupper : (∑ x ∈ C, ∑ y ∈ C, hammingDist x y) ≤ 15000 := by
    calc
      _ ≤ ∑ _x ∈ C, 250 := Finset.sum_le_sum root_sum
      _ = _ := by simp [hc]
  have hlower := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hprod i)
  norm_num only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hlower
  rw [distance_double_count] at hupper
  omega

open Finset SimpleGraph

private theorem sevenDistancePartnerCapacity (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v = 0 ∨ G.degree v = 2 ∨ G.degree v = 4)
    (he : 6 ≤ G.edgeFinset.card) :
    12 ≤ G.edgeFinset.card + (univ.filter (fun v => G.degree v = 2)).card +
      (G.cliqueFinset 3).card := by
  classical
  let A := univ.filter (fun v : Fin 6 => 0 < G.degree v)
  let L := univ.filter (fun v : Fin 6 => G.degree v = 2)
  let H := univ.filter (fun v : Fin 6 => G.degree v = 4)
  have hA : L ∪ H = A := by
    ext v
    simp only [L, H, A, mem_union, mem_filter, mem_univ, true_and]
    rcases hdeg v with h | h | h <;> simp [h]
  have hdis : Disjoint L H := by
    refine disjoint_left.mpr fun v hv hw => ?_
    have h₁ := (mem_filter.mp hv).2
    have h₂ := (mem_filter.mp hw).2
    omega
  have hcount : L.card + H.card = A.card := by
    rw [← card_union_of_disjoint hdis, hA]
  have hsumH : ∑ v ∈ H, G.degree v = 4 * H.card := by
    rw [sum_congr rfl (fun v hv => (mem_filter.mp hv).2)]
    simp [mul_comm, H]
  have hsumL : ∑ v ∈ L, G.degree v = 2 * L.card := by
    rw [sum_congr rfl (fun v hv => (mem_filter.mp hv).2)]
    simp [mul_comm, L]
  have hsumA : ∑ v ∈ A, G.degree v = ∑ v : Fin 6, G.degree v := by
    apply sum_subset (filter_subset _ _)
    simp only [mem_univ, mem_filter, true_and, not_lt, Nat.le_zero]
    exact fun _ _ h => h
  have hsum := G.sum_degrees_eq_twice_card_edges
  rw [← hsumA, ← hA, sum_union hdis, hsumL, hsumH] at hsum
  have hbase : G.edgeFinset.card + L.card = 2 * A.card := by omega
  by_cases hA6 : 6 ≤ A.card
  · change 12 ≤ G.edgeFinset.card + L.card + (G.cliqueFinset 3).card
    omega
  have hH : H.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    have hcard : H.card = 0 := by simp [h]
    omega
  obtain ⟨a, ha⟩ := hH
  have hd : G.degree a = 4 := (mem_filter.mp ha).2
  have neighbor_active {x y : Fin 6} (hxy : G.Adj x y) : y ∈ A := by
    simp only [A, mem_filter, mem_univ, true_and]
    rw [← card_neighborFinset_eq_degree, card_pos]
    exact ⟨x, (G.mem_neighborFinset y x).mpr hxy.symm⟩
  have haA : a ∈ A := by simp [A, hd]
  have hsub : G.neighborFinset a ⊆ A.erase a := by
    intro y hy
    have hn := (G.mem_neighborFinset a y).mp hy
    exact mem_erase.mpr ⟨hn.ne.symm, neighbor_active hn⟩
  have hcard : (A.erase a).card = 4 := by
    have hle := card_le_card hsub
    rw [card_neighborFinset_eq_degree, hd] at hle
    rw [card_erase_of_mem haA] at hle ⊢
    omega
  have hnb := eq_of_subset_of_card_le hsub
    (by rw [hcard, card_neighborFinset_eq_degree, hd])
  have hA5 : A.card = 5 := by rw [card_erase_of_mem haA] at hcard; omega
  let E := G.edgeFinset \ G.incidenceFinset a
  have hE : E.card + 4 = G.edgeFinset.card := by
    simpa only [E, card_incidenceFinset_eq_degree, hd] using
      card_sdiff_add_card_eq_card (G.incidenceFinset_subset a)
  have hAvoid {edge : Sym2 (Fin 6)} (hedge : edge ∈ E) : a ∉ edge.toFinset := by
    rw [Sym2.mem_toFinset]
    have hm := mem_sdiff.mp hedge
    intro hmem
    exact hm.2 (by rw [incidenceFinset_eq_filter]; exact mem_filter.mpr ⟨hm.1, hmem⟩)
  have hTriangles : E.card ≤ (G.cliqueFinset 3).card := by
    refine card_le_card_of_injOn (fun e => insert a e.toFinset) ?_ ?_
    · intro edge hedge
      revert hedge
      refine Sym2.inductionOn edge ?_
      intro x y hedge
      have hxy : G.Adj x y := G.mem_edgeFinset.mp (mem_sdiff.mp hedge).1
      have ha' := hAvoid hedge
      have hax : G.Adj a x := by
        apply (G.mem_neighborFinset a _).mp
        rw [hnb]
        exact mem_erase.mpr ⟨fun hx => ha' (by simp [hx]), neighbor_active hxy.symm⟩
      have hay : G.Adj a y := by
        apply (G.mem_neighborFinset a _).mp
        rw [hnb]
        exact mem_erase.mpr ⟨fun hy => ha' (by simp [hy]), neighbor_active hxy⟩
      have hs : (s(x, y) : Sym2 (Fin 6)).toFinset = {x, y} := by
        ext z
        simp [Sym2.mem_toFinset, Sym2.mem_iff]
      change insert a (s(x, y) : Sym2 (Fin 6)).toFinset ∈ G.cliqueFinset 3
      rw [hs, mem_cliqueFinset_iff, is3Clique_iff]
      exact ⟨a, x, y, hax, hay, hxy, rfl⟩
    · intro edge he₁ edge' he₂ heq
      have hs : edge.toFinset = edge'.toFinset := by
        have ht := congrArg (fun s : Finset (Fin 6) => s.erase a) heq
        simpa [erase_insert, hAvoid he₁, hAvoid he₂, erase_eq_of_notMem] using ht
      exact Sym2.ext (fun v => by
        rw [← Sym2.mem_toFinset, ← Sym2.mem_toFinset, hs])
  change 12 ≤ G.edgeFinset.card + L.card + (G.cliqueFinset 3).card
  omega

open private paritySide parity_union parity_bipartite from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private root_data from D5.S3.Combinatorics.Graph.HypercubeCritical.HammingSeven
open private second third second_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyFourLayerRegularity
open private second_distance third_distance from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction

private lemma thin_half_of_sixty (C : Finset (Q 9))
    (hc : C.card = 60)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : BalancedCriticalSpectrum.IsBalanced C)
    (hdiam : ∀ x ∈ C, ∀ y ∈ C, hammingDist x y ≤ 7)
    (h₂₄ : ∀ x ∈ C, 18 ≤ (shell C x 2).card + (shell C x 4).card)
    (hpartner : ∀ x ∈ C, ∃ (G : SimpleGraph (Fin 6)) (_ : DecidableRel G.Adj),
      G.edgeFinset.card = (shell C x 7).card ∧
      (∀ v, G.degree v = 0 ∨ G.degree v = 2 ∨ G.degree v = 4) ∧
      G.edgeFinset.card + (univ.filter (fun v => G.degree v = 2)).card +
        (G.cliqueFinset 3).card ≤ (shell C x 6).card) :
    ∃ i : Fin 9, ∃ b : Bool, (C.filter (fun x => x i = b)).card ≤ 21 := by
  let G := (hypercube 9).induce (C : Set (Q 9))
  have hg := BalancedCubeGirth.eight_le_egirth C hb
  have hcardC : Fintype.card (C : Set (Q 9)) = 60 := by simpa using hc
  have hcardParity (b : Bool) : (paritySide C b).card = 30 := by
    have hs := SimpleGraph.isBipartiteWith_sum_degrees_eq (parity_bipartite C)
    simp only [hr.degree_eq, Finset.sum_const, smul_eq_mul] at hs
    have hu := congrArg Finset.card (parity_union C)
    rw [Finset.card_union_of_disjoint (by
      apply Finset.disjoint_left.mpr
      intro z hz hz'
      exact Bool.false_ne_true ((Finset.mem_filter.mp hz).2.symm.trans
        (Finset.mem_filter.mp hz').2)), Finset.card_univ, hcardC] at hu
    cases b <;> omega
  have hparity (b : Bool) : (C.filter (fun x => cubeParity x = b)).card = 30 := by
    rw [← hcardParity b]
    exact Finset.card_bij (fun x hx => (⟨x,(Finset.mem_filter.mp hx).1⟩ : (C : Set (Q 9))))
      (by intro x hx; simpa [paritySide] using (Finset.mem_filter.mp hx).2)
      (by intro x hx y hy he; exact congrArg Subtype.val he)
      (by
        intro x hx
        have h : cubeParity x.val = b := by simpa [paritySide] using hx
        exact ⟨x.val, Finset.mem_filter.mpr ⟨x.property,h⟩, rfl⟩)
  have hshell (x : (C : Set (Q 9))) (k : ℕ) :
      (shell C x.val k).card =
        (univ.filter (fun y : (C : Set (Q 9)) => hammingDist x.val y.val = k)).card := by
    apply Finset.card_bij (fun y hy => (⟨y,(Finset.mem_filter.mp hy).1⟩ : (C : Set (Q 9))))
    · intro y hy
      simp [(Finset.mem_filter.mp hy).2]
    · intro y hy z hz he
      exact congrArg Subtype.val he
    · intro y hy
      exact ⟨y.val, Finset.mem_filter.mpr ⟨y.property,(Finset.mem_filter.mp hy).2⟩, rfl⟩
  apply literal_half_small_of_sixty_partner_bound C hc hdiam ?_ hparity ?_ ?_ h₂₄ ?_
  · intro x hx
    let z : (C : Set (Q 9)) := ⟨x,hx⟩
    rw [hshell z 1]
    have heq : univ.filter (fun y : (C : Set (Q 9)) => hammingDist z.val y.val = 1) =
        G.neighborFinset z := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, G.mem_neighborFinset]
      rfl
    rw [heq, G.card_neighborFinset_eq_degree, hr.degree_eq]
  · intro x hx
    let z : (C : Set (Q 9)) := ⟨x,hx⟩
    rw [hshell z 2, ← second_card hg (hr.degree_eq z) (fun y _ => hr.degree_eq y)]
    exact Finset.card_le_card (fun y hy => by simp [second_distance hy])
  · intro x hx
    let z : (C : Set (Q 9)) := ⟨x,hx⟩
    have hthird := (root_data (parity_bipartite C) hg hr.degree_eq z).2.1
    rw [hshell z 3, ← hthird]
    exact Finset.card_le_card (fun y hy => by simp [third_distance hy])
  · intro x hx
    obtain ⟨H,hH,hedge,hdeg,hbound⟩ := hpartner x hx
    by_contra! h7
    have hcap := sevenDistancePartnerCapacity H hdeg (by omega)
    have hsum (f : ℕ → ℕ) : (∑ k ∈ Finset.range 8, (shell C x k).card * f k) =
        ∑ y ∈ C, f (hammingDist x y) := by
      simpa only [shell, Finset.sum_const, smul_eq_mul] using
        Finset.sum_fiberwise_of_maps_to' (s := C) (t := Finset.range 8)
          (g := hammingDist x) (fun y hy => Finset.mem_range.mpr (by
            have := hdiam x hx y hy
            omega)) f
    have heven : (∑ y ∈ C, if hammingDist x y % 2 = 0 then 1 else 0) = 30 := by
      rw [← Finset.card_filter]
      have heq : (C.filter fun y => hammingDist x y % 2 = 0) =
          C.filter (fun y => cubeParity y = cubeParity x) := by
        ext y
        simp only [Finset.mem_filter, distance_parity]
        exact and_congr_right (fun _ => eq_comm)
      rw [heq, hparity]
    have he := (hsum (fun k => if k % 2 = 0 then 1 else 0)).trans heven
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMod, ite_true,
      Nat.mul_one, Nat.mul_zero, Nat.zero_add, Nat.add_zero] at he
    have hzero : 1 ≤ (shell C x 0).card := Finset.card_pos.mpr
      ⟨x, Finset.mem_filter.mpr ⟨hx, hammingDist_self x⟩⟩
    have h := h₂₄ x hx
    omega

#print axioms thin_half_of_sixty

open private balanced_cubic_hamming_two_four from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixtyPointSupport.Q9FourthLeafSignProbe

private lemma thin_half_of_sixty_with_partner_geometry (C : Finset (Q 9))
    (hc : C.card = 60)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : BalancedCriticalSpectrum.IsBalanced C)
    (hdiam : ∀ x ∈ C, ∀ y ∈ C, hammingDist x y ≤ 7)
    (hpartner : ∀ x ∈ C, ∃ (G : SimpleGraph (Fin 6)) (_ : DecidableRel G.Adj),
      G.edgeFinset.card = (shell C x 7).card ∧
      (∀ v, G.degree v = 0 ∨ G.degree v = 2 ∨ G.degree v = 4) ∧
      G.edgeFinset.card + (univ.filter (fun v => G.degree v = 2)).card +
        (G.cliqueFinset 3).card ≤ (shell C x 6).card) :
    ∃ i : Fin 9, ∃ b : Bool, (C.filter (fun x => x i = b)).card ≤ 21 := by
  apply thin_half_of_sixty C hc hr hb hdiam ?_ hpartner
  intro x hx
  let z : (C : Set (Q 9)) := ⟨x,hx⟩
  have hs (k : ℕ) :
      (shell C x k).card =
        (univ.filter (fun y : (C : Set (Q 9)) => hammingDist z.val y.val = k)).card := by
    apply Finset.card_bij (fun y hy => (⟨y,(Finset.mem_filter.mp hy).1⟩ : (C : Set (Q 9))))
    · intro y hy
      change ⟨y,(Finset.mem_filter.mp hy).1⟩ ∈
        univ.filter (fun y : (C : Set (Q 9)) => hammingDist x y.val = k)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩
    · intro y hy w hw he
      exact congrArg Subtype.val he
    · intro y hy
      exact ⟨y.val, Finset.mem_filter.mpr ⟨y.property,(Finset.mem_filter.mp hy).2⟩, rfl⟩
  rw [hs 2, hs 4]
  exact balanced_cubic_hamming_two_four hr hb z

#print axioms thin_half_of_sixty_with_partner_geometry
