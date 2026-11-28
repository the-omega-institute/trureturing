import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FourteenMaskSevenAxisClassification
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.Destutter

/-! The seven-axis, seventeen-mask branch.

The complement has four edges.  Sorting its seven vertices by complement degree
leaves nine monotone degree profiles, of which the first two are impossible.
The remaining seven rows are closed by the small `Q9DegreeRows` enumeration.
The representatives are the nine graph6 classes emitted by
`geng -q -d3 7 17:17`.  The mask words and certified roots are retained here as
an auditable link to the contact-graph screen.
-/

set_option autoImplicit false
set_option maxRecDepth 50000
set_option cbv.maxSteps 2500000
set_option Elab.async false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement
namespace Q9SeventeenMaskSevenAxisClassification

open Finset
open scoped BigOperators
open Q9SharedContactCNF (Axis Word)
open private vertices encode encodeEdges enumerateRows enumerateRows_complete contactAdj contactAdj_encode from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FourteenMaskSevenAxisClassification
open private axesOf from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9EightMaskClauses

abbrev Vertex := Fin 7
abbrev Pair := Vertex × Vertex
abbrev Code := Fin (2 ^ 21)

/-- The graph6 representatives, in the order used by `geng`. -/
def graph6Name : Fin 9 → String :=
  !["FE~~w", "FFz~w", "FQ~~w", "FUz~w", "FU~vw", "FTz~w", "F]znw", "F]y~w", "F]~vo"]

/-- Roots used by the small-axis screen, including the two final residual roots. -/
def certifiedRoot : Fin 9 → Vertex × Vertex :=
  ![(2,4), (0,3), (0,2), (1,3), (0,2), (1,5), (3,6), (1,3), (0,2)]

/-- The seventeen mask words for each graph6 representative. -/
def maskWords (kind : Fin 9) : List Word :=
  ![
    [9, 10, 17, 18, 20, 24, 33, 34, 36, 40, 48, 65, 66, 68, 72, 80, 96], /- FE~~w -/
    [9, 10, 12, 17, 18, 20, 33, 34, 36, 40, 48, 65, 66, 68, 72, 80, 96], /- FFz~w -/
    [5, 10, 17, 18, 20, 24, 33, 34, 36, 40, 48, 65, 66, 68, 72, 80, 96], /- FQ~~w -/
    [5, 9, 10, 17, 18, 20, 33, 34, 36, 40, 48, 65, 66, 68, 72, 80, 96], /- FUz~w -/
    [5, 9, 10, 17, 18, 20, 24, 33, 34, 36, 40, 65, 66, 68, 72, 80, 96], /- FU~vw -/
    [5, 9, 12, 17, 18, 20, 33, 34, 36, 40, 48, 65, 66, 68, 72, 80, 96], /- FTz~w -/
    [5, 6, 9, 10, 17, 18, 20, 33, 34, 36, 48, 65, 66, 68, 72, 80, 96], /- F]znw -/
    [5, 6, 9, 10, 17, 18, 20, 33, 36, 40, 48, 65, 66, 68, 72, 80, 96], /- F]y~w -/
    [5, 6, 9, 10, 17, 18, 20, 24, 33, 34, 36, 40, 65, 66, 68, 72, 80] /- F]~vo -/
  ] kind

/-- The seven sorted graphical complement profiles, preceded by two empty rows. -/
private def degreeProfile (k : Fin 9) : Vertex → ℕ :=
  ![
    ![0,0,0,0,2,3,3],
    ![0,0,0,1,1,3,3],
    ![0,0,0,1,2,2,3],
    ![0,0,0,2,2,2,2],
    ![0,0,1,1,1,2,3],
    ![0,0,1,1,2,2,2],
    ![0,1,1,1,1,1,3],
    ![0,1,1,1,1,2,2],
    ![1,1,1,1,1,1,2]
  ] k

private theorem vertices_toFinset : vertices.toFinset = univ := by
  ext a
  simp [vertices]

set_option maxHeartbeats 900000 in
private theorem find_profile (d : Vertex → ℕ) (hbound : ∀ a, d a ≤ 3)
    (hsort : Monotone d) (hsum : ∑ a : Vertex, d a = 8) :
    ∃ k : Fin 9, ∀ a, d a = degreeProfile k a := by
  have hb6 := hbound 6
  have h01 := hsort (by decide : (0 : Vertex) ≤ 1)
  have h12 := hsort (by decide : (1 : Vertex) ≤ 2)
  have h23 := hsort (by decide : (2 : Vertex) ≤ 3)
  have h34 := hsort (by decide : (3 : Vertex) ≤ 4)
  have h45 := hsort (by decide : (4 : Vertex) ≤ 5)
  have h56 := hsort (by decide : (5 : Vertex) ≤ 6)
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Nat.add_zero] at hsum
  change d 0 + (d 1 + (d 2 + (d 3 + (d 4 + (d 5 + d 6))))) = 8 at hsum
  have assemble (k : Fin 9) (h0 : d 0 = degreeProfile k 0) (h1 : d 1 = degreeProfile k 1)
      (h2 : d 2 = degreeProfile k 2) (h3 : d 3 = degreeProfile k 3)
      (h4 : d 4 = degreeProfile k 4) (h5 : d 5 = degreeProfile k 5)
      (h6 : d 6 = degreeProfile k 6) : ∃ k : Fin 9, ∀ i, d i = degreeProfile k i :=
    ⟨k, fun i => by fin_cases i <;> assumption⟩
  by_cases h0 : d 0 = 0
  · by_cases h1 : d 1 = 0
    · by_cases h2 : d 2 = 0
      · by_cases h3 : d 3 = 0
        · by_cases h4 : d 4 = 2
          · refine assemble 0
              (by change d 0 = 0; omega) (by change d 1 = 0; omega)
              (by change d 2 = 0; omega) (by change d 3 = 0; omega)
              (by change d 4 = 2; omega) (by change d 5 = 3; omega)
              (by change d 6 = 3; omega)
          · exfalso
            omega
        · by_cases h31 : d 3 = 1
          · by_cases h4 : d 4 = 1
            · refine assemble 1
                (by change d 0 = 0; omega) (by change d 1 = 0; omega)
                (by change d 2 = 0; omega) (by change d 3 = 1; omega)
                (by change d 4 = 1; omega) (by change d 5 = 3; omega)
                (by change d 6 = 3; omega)
            · refine assemble 2
                (by change d 0 = 0; omega) (by change d 1 = 0; omega)
                (by change d 2 = 0; omega) (by change d 3 = 1; omega)
                (by change d 4 = 2; omega) (by change d 5 = 2; omega)
                (by change d 6 = 3; omega)
          · refine assemble 3
              (by change d 0 = 0; omega) (by change d 1 = 0; omega)
              (by change d 2 = 0; omega) (by change d 3 = 2; omega)
              (by change d 4 = 2; omega) (by change d 5 = 2; omega)
              (by change d 6 = 2; omega)
      · by_cases h21 : d 2 = 1
        · by_cases h31 : d 3 = 1
          · by_cases h4 : d 4 = 1
            · refine assemble 4
                (by change d 0 = 0; omega) (by change d 1 = 0; omega)
                (by change d 2 = 1; omega) (by change d 3 = 1; omega)
                (by change d 4 = 1; omega) (by change d 5 = 2; omega)
                (by change d 6 = 3; omega)
            · refine assemble 5
                (by change d 0 = 0; omega) (by change d 1 = 0; omega)
                (by change d 2 = 1; omega) (by change d 3 = 1; omega)
                (by change d 4 = 2; omega) (by change d 5 = 2; omega)
                (by change d 6 = 2; omega)
          · exfalso
            omega
        · exfalso
          omega
    · by_cases h11 : d 1 = 1
      · by_cases h21 : d 2 = 1
        · by_cases h31 : d 3 = 1
          · by_cases h51 : d 5 = 1
            · refine assemble 6
                (by change d 0 = 0; omega) (by change d 1 = 1; omega)
                (by change d 2 = 1; omega) (by change d 3 = 1; omega)
                (by change d 4 = 1; omega) (by change d 5 = 1; omega)
                (by change d 6 = 3; omega)
            · refine assemble 7
                (by change d 0 = 0; omega) (by change d 1 = 1; omega)
                (by change d 2 = 1; omega) (by change d 3 = 1; omega)
                (by change d 4 = 1; omega) (by change d 5 = 2; omega)
                (by change d 6 = 2; omega)
          · exfalso
            omega
        · exfalso
          omega
      · exfalso
        omega
  · by_cases h1 : d 1 = 1
    · by_cases h2 : d 2 = 1
      · by_cases h3 : d 3 = 1
        · refine assemble 8
            (by change d 0 = 1; omega) (by change d 1 = 1; omega)
            (by change d 2 = 1; omega) (by change d 3 = 1; omega)
            (by change d 4 = 1; omega) (by change d 5 = 1; omega)
            (by change d 6 = 2; omega)
        · exfalso
          omega
      · exfalso
        omega
    · exfalso
      omega

/-- The mask family itself, without adding a separate normalized root word. -/
def maskFamily (kind : Fin 9) : Finset (Finset Axis) :=
  (maskWords kind).map axesOf |>.toFinset

/-- The explicit representative contact graphs. -/
def representativeGraph (kind : Fin 9) : SimpleGraph Vertex :=
  SimpleGraph.fromRel fun a b =>
    ({a.castLE (by decide), b.castLE (by decide)} : Finset Axis) ∈ maskFamily kind

instance (kind : Fin 9) : DecidableRel (representativeGraph kind).Adj := by
  unfold representativeGraph
  infer_instance

set_option maxHeartbeats 0 in
theorem representative_data (kind : Fin 9) :
    (maskWords kind).length = 17 ∧
      ({(certifiedRoot kind).1.castLE (by decide),
          (certifiedRoot kind).2.castLE (by decide)} : Finset Axis) ∈ maskFamily kind ∧
      (representativeGraph kind).edgeFinset.card = 17 := by
  fin_cases kind <;> decide +kernel

theorem representativeGraph_adj (kind : Fin 9) (a b : Vertex) :
    (representativeGraph kind).Adj a b ↔
      a ≠ b ∧ ({a.castLE (by decide), b.castLE (by decide)} : Finset Axis) ∈ maskFamily kind := by
  simp [representativeGraph, Finset.pair_comm (b.castLE (by decide : 7 ≤ 9))
    (a.castLE (by decide : 7 ≤ 9))]

private def representativeCode : Fin 9 → Code :=
  ![2115, 32835, 2117, 34881, 264257, 32961, 100353, 35329, 1312769]

private def representativeAdj (kind : Fin 9) (a b : Vertex) : Bool :=
  contactAdj (representativeCode kind) a b

set_option maxHeartbeats 0 in
private theorem representativeCode_spec (kind : Fin 9) :
    ∀ a b, representativeAdj kind a b = true ↔ (representativeGraph kind).Adj a b := by
  fin_cases kind <;> decide +kernel

private def representativeBlock (kind : Fin 9) (degree : ℕ) : List Vertex :=
  vertices.filter fun a =>
    decide (vertices.countP (fun b => a != b && !representativeAdj kind a b) = degree)

private def representativeOrders (kind : Fin 9) : List (List Vertex) :=
  let p0 := (representativeBlock kind 0).permutations'
  let p1 := (representativeBlock kind 1).permutations'
  let p2 := (representativeBlock kind 2).permutations'
  let p3 := (representativeBlock kind 3).permutations'
  p0.flatMap fun a => p1.flatMap fun b => p2.flatMap fun c =>
    p3.map fun d => a ++ b ++ c ++ d

private def profileRepresentatives (k : Fin 9) : List (Fin 9) :=
  ![[], [], [0], [2], [5], [1,3], [6], [4,7], [8]] k

private abbrev Witness := Fin 9 × List Vertex

private def witnesses (k : Fin 9) : List Witness :=
  (profileRepresentatives k).flatMap fun kind =>
    (representativeOrders kind).map fun p => (kind, p)

private def relabel (p : List Vertex) (a : Vertex) : Vertex :=
  p.getD a.val 0

private def witnessCode (w : Witness) : Code :=
  encode fun a b => !representativeAdj w.1 (relabel w.2 a) (relabel w.2 b)

private theorem enumerateRows_complete' (vs : List Vertex) (hvs : vs.Nodup)
    (d : Vertex → ℕ) (E : Finset Pair) (hE : E ∈ Q9DegreeRows.degreeEdges vs d) :
    ∃ F ∈ enumerateRows vs d, F.toFinset = E := by
  exact enumerateRows_complete vs hvs d E hE

private def candidates (k : Fin 9) : List Code :=
  ((enumerateRows vertices (degreeProfile k)).map (fun E => encode fun a b => E.contains (a, b) || E.contains (b, a))).mergeSort

private def expectedCandidates : Fin 9 → ℕ :=
  ![0, 0, 1, 3, 3, 7, 10, 18, 45]

private def representativeCodes (k : Fin 9) : List Code :=
  ((witnesses k).map witnessCode |>.mergeSort).destutter (· ≠ ·)

private def coverCheck (k : Fin 9) : Bool :=
  let cs := candidates k
  (cs.length == expectedCandidates k) &&
    ((cs == representativeCodes k) &&
      (witnesses k).all (fun w => decide (w.2.length = 7 ∧ w.2.Nodup)))

set_option maxHeartbeats 12000000 in
private theorem cover_0 : coverCheck 0 = true := by cbv
set_option maxHeartbeats 12000000 in
private theorem cover_1 : coverCheck 1 = true := by cbv
set_option maxHeartbeats 12000000 in
private theorem cover_2 : coverCheck 2 = true := by cbv
set_option maxHeartbeats 12000000 in
private theorem cover_3 : coverCheck 3 = true := by cbv
set_option maxHeartbeats 12000000 in
private theorem cover_4 : coverCheck 4 = true := by cbv
set_option maxHeartbeats 12000000 in
private theorem cover_5 : coverCheck 5 = true := by cbv
set_option maxHeartbeats 12000000 in
private theorem cover_6 : coverCheck 6 = true := by cbv
set_option maxHeartbeats 12000000 in
private theorem cover_7 : coverCheck 7 = true := by cbv
set_option cbv.maxSteps 10000000 in
set_option maxHeartbeats 12000000 in
private theorem cover_8 : coverCheck 8 = true := by cbv

private theorem finite_cover (k : Fin 9) :
    (candidates k).length = expectedCandidates k ∧
    candidates k = representativeCodes k ∧
    (witnesses k).all (fun w => decide (w.2.length = 7 ∧ w.2.Nodup)) = true := by
  have h : coverCheck k = true := by
    fin_cases k
    · exact cover_0
    · exact cover_1
    · exact cover_2
    · exact cover_3
    · exact cover_4
    · exact cover_5
    · exact cover_6
    · exact cover_7
    · exact cover_8
  simp only [coverCheck, Bool.and_eq_true] at h
  exact ⟨eq_of_beq h.1, eq_of_beq h.2.1, h.2.2⟩

private theorem candidate_of_degreeEdges (k : Fin 9) {E : Finset Pair}
    (hE : E ∈ Q9DegreeRows.degreeEdges vertices (degreeProfile k)) :
    encodeEdges E ∈ candidates k := by
  have hvs : vertices.Nodup := List.nodup_finRange 7
  obtain ⟨F, hF, hFe⟩ := enumerateRows_complete' vertices hvs (degreeProfile k) E hE
  apply List.mem_mergeSort.mpr
  refine List.mem_map.mpr ⟨F, hF, ?_⟩
  unfold encodeEdges
  congr 1
  funext a b
  rw [← hFe]
  by_cases ha : (a,b) ∈ F <;> by_cases hb : (b,a) ∈ F <;> simp [ha, hb]

private theorem witness_bijective (w : Witness) (h : w.2.length = 7 ∧ w.2.Nodup) :
    Function.Bijective (relabel w.2) := by
  apply Function.Injective.bijective_of_finite
  intro a b hab
  apply Fin.ext
  have ha : a.val < w.2.length := h.1.symm ▸ a.isLt
  have hb : b.val < w.2.length := h.1.symm ▸ b.isLt
  exact (List.Nodup.getD_inj ha hb h.2).mp hab

private theorem witness_adj (w : Witness) (a b : Vertex) :
    contactAdj (witnessCode w) a b = true ↔
      (representativeGraph w.1).Adj (relabel w.2 a) (relabel w.2 b) := by
  apply contactAdj_encode (G := (representativeGraph w.1).comap (relabel w.2))
  intro x y _
  change (!representativeAdj w.1 (relabel w.2 x) (relabel w.2 y)) = true ↔
    ¬ (representativeGraph w.1).Adj (relabel w.2 x) (relabel w.2 y)
  rw [← representativeCode_spec w.1]
  cases representativeAdj w.1 (relabel w.2 x) (relabel w.2 y) <;> decide

private theorem classify_sorted (G : SimpleGraph Vertex) [DecidableRel G.Adj] (k : Fin 9)
    (hd : ∀ a, Gᶜ.degree a = degreeProfile k a) :
    ∃ kind : Fin 9, Nonempty (G ≃g representativeGraph kind) := by
  have hdegree (a : Vertex) (_ : a ∈ vertices.toFinset) :
      degreeProfile k a = (vertices.toFinset.filter (Gᶜ.Adj a)).card := by
    rw [← hd a, vertices_toFinset, ← SimpleGraph.neighborFinset_eq_filter,
      SimpleGraph.card_neighborFinset_eq_degree]
  obtain ⟨E, hE, hAdj⟩ := Q9DegreeRows.complete Gᶜ vertices
    (List.nodup_finRange _) (degreeProfile k) hdegree
  let m := encodeEdges E
  have hm (a b : Vertex) : contactAdj m a b = true ↔ G.Adj a b := by
    apply contactAdj_encode (G := G)
    intro x y hxy
    have h := hAdj x (by simp [vertices_toFinset]) y (by simp [vertices_toFinset])
    rw [SimpleGraph.compl_adj] at h
    simpa [hxy] using h.symm
  have hmem : m ∈ candidates k := candidate_of_degreeEdges k hE
  rw [(finite_cover k).2.1] at hmem
  have hcodes : m ∈ ((witnesses k).map witnessCode).mergeSort :=
    (List.destutter_sublist (· ≠ ·) _).subset hmem
  obtain ⟨w, hw, hcode⟩ := List.mem_map.mp (List.mem_mergeSort.mp hcodes)
  have hvalid := of_decide_eq_true (List.all_eq_true.mp (finite_cover k).2.2 w hw)
  refine ⟨w.1, ⟨{
    toEquiv := Equiv.ofBijective (relabel w.2) (witness_bijective w hvalid)
    map_rel_iff' := ?_ }⟩⟩
  intro a b
  have hwitness := witness_adj w a b
  rw [hcode] at hwitness
  exact hwitness.symm.trans (hm a b)

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Every seven-vertex graph with seventeen edges and minimum degree three is
isomorphic to one of the nine explicit graph6 representatives above. -/
theorem seventeen_edges_on_seven_vertices (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = 7) (hE : G.edgeFinset.card = 17)
    (hmin : ∀ a, 3 ≤ G.degree a) :
    ∃ kind : Fin 9, Nonempty (representativeGraph kind ≃g G) := by
  let e₀ : Vertex ≃ V := (Fintype.equivFinOfCardEq hV).symm
  let d₀ (a : Vertex) := Gᶜ.degree (e₀ a)
  let e := (Tuple.sort d₀).trans e₀
  let H := G.comap e
  let iso : H ≃g G := SimpleGraph.Iso.comap e G
  let isoC : Hᶜ ≃g Gᶜ :=
    { toEquiv := e
      map_rel_iff' := by
        intro a b
        change (e a ≠ e b ∧ ¬ G.Adj (e a) (e b)) ↔
          (a ≠ b ∧ ¬ G.Adj (e a) (e b))
        exact and_congr (not_congr e.injective.eq_iff) Iff.rfl }
  let d (a : Vertex) := Hᶜ.degree a
  have hdeg (a : Vertex) : G.degree (e a) = H.degree a := iso.degree_eq a
  have hsort : Monotone d := by
    intro a b hab
    change Hᶜ.degree a ≤ Hᶜ.degree b
    rw [← isoC.degree_eq a, ← isoC.degree_eq b]
    exact Tuple.monotone_sort d₀ hab
  have htotal : (∑ a : Vertex, H.degree a) = 34 := by
    rw [H.sum_degrees_eq_twice_card_edges, iso.card_edgeFinset_eq, hE]
  have hcard : Fintype.card Vertex = 7 := Fintype.card_fin _
  have hsumAt (a : Vertex) : H.degree a + d a = 6 := by
    have hle := H.degree_lt_card_verts a
    rw [hcard] at hle
    change H.degree a + Hᶜ.degree a = 6
    rw [H.degree_compl, hcard]
    omega
  have hminH (a : Vertex) : 3 ≤ H.degree a := hdeg a ▸ hmin (e a)
  have hbound (a : Vertex) : d a ≤ 3 := by
    have := hsumAt a
    have := hminH a
    omega
  have hsum : (∑ a : Vertex, d a) = 8 := by
    have hs : (∑ a : Vertex, (H.degree a + d a)) = 42 := by
      simp [hsumAt, hcard]
    rw [Finset.sum_add_distrib, htotal] at hs
    omega
  obtain ⟨k, hk⟩ := find_profile d hbound hsort hsum
  obtain ⟨kind, ⟨toRepresentative⟩⟩ := classify_sorted H k hk
  exact ⟨kind, ⟨toRepresentative.symm.trans iso⟩⟩

end Q9SeventeenMaskSevenAxisClassification
end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement
