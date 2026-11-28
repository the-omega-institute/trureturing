import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9DegreeRows
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FifteenMaskNineAxisClassification
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ThirteenMaskSevenAxisShapes
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.Destutter

/-! Fourteen contact edges on seven axes. Sort the complement by degree,
enumerate its prescribed-degree rows, and compare the surviving adjacency
words with those obtained by relabeling the audited recipes. -/

set_option autoImplicit false
set_option maxRecDepth 50000
set_option cbv.maxSteps 2500000
set_option Elab.async false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement
namespace Q9FourteenMaskSevenAxisClassification

open Finset
open scoped BigOperators
open Q9SharedContactCNF (Axis Word)
open Q9FifteenMaskNineAxisClassification (LocalLaws)
open private square_of_iso from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TenMaskGraph
open private second_of_iso from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TwelveMaskSevenAxisShapes
open private every_square_of_iso from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ThirteenMaskSevenAxisShapes

abbrev Vertex := Fin 7

private def vertices : List Vertex := List.finRange 7

private theorem vertices_toFinset : vertices.toFinset = univ := by
  ext a
  simp [vertices]

private def degreeProfile (k : Fin 8) : Vertex → ℕ :=
  ![![0,0,2,3,3,3,3], ![0,1,1,3,3,3,3], ![0,1,2,2,3,3,3], ![0,2,2,2,2,3,3],
    ![1,1,1,2,3,3,3], ![1,1,2,2,2,3,3], ![1,2,2,2,2,2,3], ![2,2,2,2,2,2,2]] k

set_option maxHeartbeats 900000 in
private theorem find_profile (d : Vertex → ℕ) (hbound : ∀ a, d a ≤ 3)
    (hsort : Monotone d) (hsum : ∑ a : Vertex, d a = 14) :
    ∃ k : Fin 8, ∀ a, d a = degreeProfile k a := by
  have h01 := hsort (by decide : (0 : Vertex) ≤ 1)
  have h12 := hsort (by decide : (1 : Vertex) ≤ 2)
  have h23 := hsort (by decide : (2 : Vertex) ≤ 3)
  have h34 := hsort (by decide : (3 : Vertex) ≤ 4)
  have h45 := hsort (by decide : (4 : Vertex) ≤ 5)
  have h56 := hsort (by decide : (5 : Vertex) ≤ 6)
  have hlast : d 6 ≤ 3 := hbound 6
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Nat.add_zero] at hsum
  change d 0 + (d 1 + (d 2 + (d 3 + (d 4 + (d 5 + d 6))))) = 14 at hsum
  have assemble (k : Fin 8) (h0 : d 0 = degreeProfile k 0) (h1 : d 1 = degreeProfile k 1)
      (h2 : d 2 = degreeProfile k 2) (h3 : d 3 = degreeProfile k 3)
      (h4 : d 4 = degreeProfile k 4) (h5 : d 5 = degreeProfile k 5)
      (h6 : d 6 = degreeProfile k 6) : ∃ k : Fin 8, ∀ i, d i = degreeProfile k i :=
    ⟨k, fun i => by fin_cases i <;> assumption⟩
  -- The sum and monotonicity force the tail once the small entries are fixed.
  by_cases ha0 : d 0 = 0
  · by_cases hb0 : d 1 = 0
    · refine assemble 0 ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · show d 0 = 0; omega
      · show d 1 = 0; omega
      · show d 2 = 2; omega
      · show d 3 = 3; omega
      · show d 4 = 3; omega
      · show d 5 = 3; omega
      · show d 6 = 3; omega
    · by_cases hb1 : d 1 = 1
      · by_cases hc1 : d 2 = 1
        · refine assemble 1 ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · show d 0 = 0; omega
          · show d 1 = 1; omega
          · show d 2 = 1; omega
          · show d 3 = 3; omega
          · show d 4 = 3; omega
          · show d 5 = 3; omega
          · show d 6 = 3; omega
        · refine assemble 2 ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · show d 0 = 0; omega
          · show d 1 = 1; omega
          · show d 2 = 2; omega
          · show d 3 = 2; omega
          · show d 4 = 3; omega
          · show d 5 = 3; omega
          · show d 6 = 3; omega
      · refine assemble 3 ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · show d 0 = 0; omega
        · show d 1 = 2; omega
        · show d 2 = 2; omega
        · show d 3 = 2; omega
        · show d 4 = 2; omega
        · show d 5 = 3; omega
        · show d 6 = 3; omega
  · by_cases ha1 : d 0 = 1
    · by_cases hb1 : d 1 = 1
      · by_cases hc1 : d 2 = 1
        · refine assemble 4 ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · show d 0 = 1; omega
          · show d 1 = 1; omega
          · show d 2 = 1; omega
          · show d 3 = 2; omega
          · show d 4 = 3; omega
          · show d 5 = 3; omega
          · show d 6 = 3; omega
        · refine assemble 5 ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · show d 0 = 1; omega
          · show d 1 = 1; omega
          · show d 2 = 2; omega
          · show d 3 = 2; omega
          · show d 4 = 2; omega
          · show d 5 = 3; omega
          · show d 6 = 3; omega
      · refine assemble 6 ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · show d 0 = 1; omega
        · show d 1 = 2; omega
        · show d 2 = 2; omega
        · show d 3 = 2; omega
        · show d 4 = 2; omega
        · show d 5 = 2; omega
        · show d 6 = 3; omega
    · refine assemble 7 ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · show d 0 = 2; omega
      · show d 1 = 2; omega
      · show d 2 = 2; omega
      · show d 3 = 2; omega
      · show d 4 = 2; omega
      · show d 5 = 2; omega
      · show d 6 = 2; omega

private abbrev Code := Fin (2 ^ 21)
private abbrev Pair := Vertex × Vertex

private def pairAt : Fin 21 → Pair :=
  ![(0,1), (0,2), (0,3), (0,4), (0,5), (0,6), (1,2), (1,3), (1,4), (1,5),
    (1,6), (2,3), (2,4), (2,5), (2,6), (3,4), (3,5), (3,6), (4,5), (4,6), (5,6)]

private def pairIndex (a b : Vertex) : Fin 21 :=
  ![![0,0,1,2,3,4,5], ![0,0,6,7,8,9,10], ![1,6,0,11,12,13,14],
    ![2,7,11,0,15,16,17], ![3,8,12,15,0,18,19],
    ![4,9,13,16,18,0,20], ![5,10,14,17,19,20,0]] a b

private theorem pairIndex_symm : ∀ a b, pairIndex a b = pairIndex b a := by
  decide +kernel

private theorem pairAt_index : ∀ a b : Vertex, a < b → pairAt (pairIndex a b) = (a,b) := by
  decide +kernel

private def encode (bits : Vertex → Vertex → Bool) : Code :=
  ((BitVec.ofBoolListLE (List.ofFn fun k => bits (pairAt k).1 (pairAt k).2)).cast
    List.length_ofFn).toFin

private theorem encode_bit (bits : Vertex → Vertex → Bool) (k : Fin 21) :
    (BitVec.ofFin (encode bits)).getLsb k = bits (pairAt k).1 (pairAt k).2 := by
  change (BitVec.ofFin (encode bits)).getLsbD k.val = _
  have hk : k.val < (List.ofFn fun t => bits (pairAt t).1 (pairAt t).2).length := by
    simpa only [List.length_ofFn] using k.isLt
  rw [encode, BitVec.ofFin_toFin, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    ← List.getElem_eq_getD (h := hk) false, List.getElem_ofFn]

private def contactAdj (m : Code) (a b : Vertex) : Bool :=
  if a = b then false else !(BitVec.ofFin m).getLsb (pairIndex a b)

private theorem contactAdj_symm (m : Code) (a b : Vertex) :
    contactAdj m a b = contactAdj m b a := by
  by_cases h : a = b
  · subst b
    rfl
  · simp only [contactAdj, ite_eq_right, h, Ne.symm h, pairIndex_symm a b]

private theorem contactAdj_encode {G : SimpleGraph Vertex}
    (bits : Vertex → Vertex → Bool)
    (h : ∀ a b, a ≠ b → (bits a b = true ↔ ¬ G.Adj a b)) (a b : Vertex) :
    contactAdj (encode bits) a b = true ↔ G.Adj a b := by
  classical
  have ordered (x y : Vertex) (hxy : x < y) :
      contactAdj (encode bits) x y = true ↔ G.Adj x y := by
    simp only [contactAdj, if_neg hxy.ne, encode_bit, pairAt_index x y hxy, Prod.fst, Prod.snd]
    have hnot : (!bits x y) = true ↔ ¬ (bits x y = true) := by
      cases bits x y <;> decide
    exact hnot.trans ((not_congr (h x y hxy.ne)).trans not_not)
  rcases lt_trichotomy a b with hab | rfl | hba
  · exact ordered a b hab
  · simp [contactAdj]
  · rw [contactAdj_symm _ a b, G.adj_comm a b]
    exact ordered b a hba

private def encodeEdges (E : Finset Pair) : Code :=
  encode fun a b => decide ((a,b) ∈ E ∨ (b,a) ∈ E)

private def neighbors (m : Code) (a : Vertex) : List Vertex :=
  vertices.filter (contactAdj m a)

private def other (N : Vertex → List Vertex) (a b c : Vertex) : Bool :=
  (N b).any fun d => d != a && (N c).contains d

private def passes (k : Fin 8) (m : Code) : Bool :=
  let N := neighbors m
  vertices.all fun a => (N a).all fun b =>
    ((N a).any fun c => c != b && other N a b c) &&
    (if degreeProfile k a = 3 ∧ degreeProfile k b = 3 then
      (N a).all fun c =>
        (if c = b then true else other N a b c) &&
        (if (N b).contains c then decide (degreeProfile k c ≠ 3) && other N c a b else true)
    else true)

private theorem passes_of_laws (k : Fin 8) (m : Code) (G : SimpleGraph Vertex)
    [DecidableRel G.Adj] (hm : ∀ a b, contactAdj m a b = true ↔ G.Adj a b)
    (hcubic : ∀ a, G.degree a = 3 ↔ degreeProfile k a = 3)
    (laws : LocalLaws G) : passes k m = true := by
  let N := neighbors m
  have adj (a b : Vertex) : b ∈ N a ↔ G.Adj a b := by
    simp [N, neighbors, vertices, hm]
  have other_of (a b c : Vertex) (h : ∃ d, d ≠ a ∧ G.Adj b d ∧ G.Adj c d) :
      other N a b c = true := by
    obtain ⟨d, hda, hbd, hcd⟩ := h
    apply List.any_eq_true.mpr
    refine ⟨d, (adj _ _).mpr hbd, ?_⟩
    simp [hda, List.contains_iff_mem, (adj _ _).mpr hcd]
  unfold passes
  apply List.all_eq_true.mpr
  intro a _
  apply List.all_eq_true.mpr
  intro b hb
  have hab := (adj a b).mp hb
  simp only [Bool.and_eq_true]
  constructor
  · obtain ⟨c, hac, hcb, hd⟩ := laws.edgeSquare hab
    exact List.any_eq_true.mpr ⟨c, (adj _ _).mpr hac, by
      change (c != b && other N a b c) = true
      simp [hcb, Ne.symm hcb, other_of a b c hd]⟩
  · split
    next h =>
      have ha := (hcubic a).mpr h.1
      have hb' := (hcubic b).mpr h.2
      apply List.all_eq_true.mpr
      intro c hc
      have hac := (adj a c).mp hc
      simp only [Bool.and_eq_true]
      constructor
      · by_cases he : c = b
        · simp [he]
        · simpa [he] using other_of a b c (laws.cubicSquare hab hac (Ne.symm he) ha hb')
      · split
        next hbc =>
          have hbc' := (adj b c).mp (List.contains_iff_mem.mp hbc)
          have hnc : degreeProfile k c ≠ 3 := fun hc' =>
            laws.noCubicTriangle a b c hab hbc' hac.symm ha hb' ((hcubic c).mpr hc')
          rw [Bool.and_eq_true]
          exact ⟨decide_eq_true hnc, other_of c a b (laws.secondNeighbor hab ha hb' hac hbc')⟩
        next => rfl
    next => rfl

/-- The thirteen non-root words of each recipe in audit order.
The replay recipe adds the common root word 3. -/
def maskWords (kind : Fin 27) : List Word :=
  ![
    [6, 10, 18, 33, 34, 36, 40, 48, 65, 66, 68, 72, 80] /- F?~vw -/,
    [20, 24, 33, 34, 36, 40, 48, 65, 66, 68, 72, 80, 96] /- FCZ~w -/,
    [6, 10, 18, 20, 33, 34, 36, 40, 65, 66, 68, 72, 80] /- FCzvw -/,
    [6, 10, 18, 20, 33, 36, 40, 48, 65, 66, 68, 72, 80] /- FC~vo -/,
    [6, 10, 18, 20, 33, 36, 40, 48, 65, 66, 68, 72, 96] /- FC~vW -/,
    [6, 10, 17, 18, 20, 33, 34, 40, 66, 68, 72, 80, 96] /- FEh~w -/,
    [6, 10, 17, 18, 20, 34, 36, 40, 65, 68, 72, 80, 96] /- FEj~o -/,
    [6, 10, 18, 20, 24, 33, 34, 36, 40, 65, 66, 68, 72] /- FEzfw -/,
    [6, 10, 18, 20, 24, 33, 34, 36, 40, 65, 68, 72, 80] /- FEzvo -/,
    [6, 10, 20, 24, 33, 36, 40, 48, 65, 68, 72, 80, 96] /- FEzvg -/,
    [6, 10, 20, 24, 33, 34, 36, 40, 65, 66, 68, 72, 80] /- FEzno -/,
    [6, 10, 17, 18, 20, 34, 36, 40, 48, 65, 66, 68, 72] /- FEnfw -/,
    [6, 18, 20, 24, 33, 34, 36, 40, 65, 66, 68, 72, 80] /- FEnvo -/,
    [6, 18, 20, 24, 33, 36, 40, 48, 65, 68, 72, 80, 96] /- FEnvg -/,
    [6, 10, 17, 18, 20, 36, 40, 48, 65, 66, 68, 72, 96] /- FEnvW -/,
    [6, 17, 18, 24, 34, 36, 40, 48, 65, 66, 68, 72, 80] /- FEl~o -/,
    [6, 10, 17, 20, 24, 33, 36, 40, 65, 68, 72, 80, 96] /- FFzfo -/,
    [12, 20, 24, 33, 34, 36, 40, 65, 66, 68, 72, 80, 96] /- FQjvw -/,
    [5, 6, 10, 18, 24, 33, 34, 36, 40, 66, 68, 72, 80] /- FQzVw -/,
    [6, 9, 10, 18, 20, 34, 36, 40, 48, 65, 68, 72, 80] /- FQzvo -/,
    [6, 9, 10, 18, 20, 36, 40, 48, 65, 66, 68, 72, 80] /- FQzvg -/,
    [5, 6, 10, 24, 34, 36, 40, 48, 65, 66, 68, 72, 80] /- FQz^o -/,
    [6, 9, 10, 17, 18, 20, 34, 36, 40, 68, 72, 80, 96] /- FUZvo -/,
    [5, 6, 9, 10, 18, 20, 40, 48, 66, 68, 72, 80, 96] /- FUZvW -/,
    [5, 10, 20, 24, 33, 36, 40, 48, 66, 68, 72, 80, 96] /- FUZuw -/,
    [10, 12, 17, 18, 20, 33, 36, 40, 65, 68, 72, 80, 96] /- FUxvo -/,
    [9, 12, 17, 18, 20, 33, 34, 36, 40, 66, 68, 72, 80] /- FUzro -/
  ] kind

def recipeFamily (kind : Fin 27) : Finset (Finset Axis) :=
  (Q9FifteenMaskLargeAxesReplay.recipe (maskWords kind)).family

/-- Vertices carry the original bit indices of the audited recipes. -/
def recipeGraph (kind : Fin 27) : SimpleGraph Vertex :=
  SimpleGraph.fromRel fun a b =>
    ({a.castLE (by decide), b.castLE (by decide)} : Finset Axis) ∈ recipeFamily kind

instance (kind : Fin 27) : DecidableRel (recipeGraph kind).Adj := by
  unfold recipeGraph
  infer_instance

theorem recipeGraph_adj (kind : Fin 27) (a b : Vertex) :
    (recipeGraph kind).Adj a b ↔
      a ≠ b ∧ ({a.castLE (by decide), b.castLE (by decide)} : Finset Axis) ∈ recipeFamily kind := by
  simp [recipeGraph, Finset.pair_comm (b.castLE (by decide : 7 ≤ 9))
    (a.castLE (by decide : 7 ≤ 9))]

-- The 21 complement bits of each recipe in its original labeling.
-- recipeAdj_spec ties these constants to the audited maskWords.
private def recipeCode (kind : Fin 27) : Code :=
  ![1087502, 2510, 1345550, 1083918, 559630, 305190, 298006,
    1837070, 1313806, 3854, 1313038, 1607702, 1312910, 3726,
    559638, 1054870, 265990, 262606, 1316908, 1084442, 1083930,
    1055004, 298034, 43576, 2924, 296518, 1343714] kind

private def recipeAdj (kind : Fin 27) (a b : Vertex) : Bool :=
  contactAdj (recipeCode kind) a b

set_option maxHeartbeats 0 in
private theorem recipeAdj_spec (kind : Fin 27) :
    ∀ a b, recipeAdj kind a b = true ↔ (recipeGraph kind).Adj a b := by
  fin_cases kind <;> decide +kernel

private def recipeBlock (kind : Fin 27) (degree : ℕ) : List Vertex :=
  vertices.filter fun a =>
    decide (vertices.countP (fun b => a != b && !recipeAdj kind a b) = degree)

/-- The images of consecutive sorted labels are chosen within each degree
block. Recipe 26 has a seven-cycle complement in the order 0,2,1,3,4,5,6.
Rotating fixes the first image to 0 and reflection permits the second image
to be chosen in {1,2,3}. The finite comparison checks this reduction. -/
private def recipeOrders (kind : Fin 27) : List (List Vertex) :=
  if kind = 26 then
    ([1,2,3] : List Vertex).flatMap fun b =>
      ((vertices.erase 0).erase b).permutations'.map (fun tail => 0 :: b :: tail)
  else
    let p0 := (recipeBlock kind 0).permutations'
    let p1 := (recipeBlock kind 1).permutations'
    let p2 := (recipeBlock kind 2).permutations'
    let p3 := (recipeBlock kind 3).permutations'
    p0.flatMap fun a => p1.flatMap fun b => p2.flatMap fun c =>
      p3.map fun d => a ++ b ++ c ++ d

private def profileRecipes (k : Fin 8) : List (Fin 27) :=
  ![[1], [0], [2,5,17], [7,11,18], [4,13,15], [3,6,9,10,12,14,20,21,23,24],
    [8,16,19,22,25], [26]] k

private abbrev Witness := Fin 27 × List Vertex

private def witnesses (k : Fin 8) : List Witness :=
  (profileRecipes k).flatMap fun kind => (recipeOrders kind).map fun p => (kind,p)

private def relabel (p : List Vertex) (a : Vertex) : Vertex :=
  p.getD a.val 0

private def witnessCode (w : Witness) : Code :=
  encode fun a b => !recipeAdj w.1 (relabel w.2 a) (relabel w.2 b)

-- List-valued rows keep the small closed checks on computable lists.
private def enumerateRows : List Vertex → (Vertex → ℕ) → List (List Pair)
  | [], _ => [[]]
  | v :: tail, d =>
      ((tail.sublistsLen (d v)).filter fun N => N.all fun u => decide (0 < d u)).flatMap
        fun N => (enumerateRows tail (fun u => d u - if u ∈ N then 1 else 0)).map
          fun F => F ++ N.map (fun u => (v,u))

private theorem enumerateRows_complete (vs : List Vertex) (hvs : vs.Nodup)
    (d : Vertex → ℕ) (E : Finset Pair) (hE : E ∈ Q9DegreeRows.degreeEdges vs d) :
    ∃ F ∈ enumerateRows vs d, F.toFinset = E := by
  induction vs generalizing d E with
  | nil =>
      have h : E = ∅ := by simpa [Q9DegreeRows.degreeEdges] using hE
      exact ⟨[], by simp [enumerateRows], h.symm⟩
  | cons v vs ih =>
      rw [Q9DegreeRows.degreeEdges] at hE
      obtain ⟨N, hN, hE⟩ := Finset.mem_biUnion.mp hE
      obtain ⟨E', hE', rfl⟩ := Finset.mem_image.mp hE
      simp only [Finset.mem_filter] at hN
      obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hN.1
      let L := vs.filter fun u => decide (u ∈ N)
      have hLsub : List.Sublist L vs := List.filter_sublist
      have hLfin : L.toFinset = N := by
        ext u
        simp only [List.mem_toFinset, L, List.mem_filter, decide_eq_true_eq]
        exact ⟨And.right, fun hu => ⟨List.mem_toFinset.mp (hsub hu), hu⟩⟩
      have hLlen : L.length = d v := by
        rw [← List.toFinset_card_of_nodup (hLsub.nodup (List.nodup_cons.mp hvs).2), hLfin]
        exact hcard
      have hL (u : Vertex) : u ∈ L ↔ u ∈ N := by
        rw [← hLfin, List.mem_toFinset]
      have hLrow : L ∈ (vs.sublistsLen (d v)).filter
          (fun N => N.all fun u => decide (0 < d u)) := by
        apply List.mem_filter.mpr
        refine ⟨List.mem_sublistsLen.mpr ⟨hLsub, hLlen⟩, List.all_eq_true.mpr ?_⟩
        intro u hu
        exact decide_eq_true (hN.2 u ((hL u).mp hu))
      have hd : (fun u => d u - if u ∈ N then 1 else 0) =
          (fun u => d u - if u ∈ L then 1 else 0) := by
        funext u
        simp only [hL]
      rw [hd] at hE'
      obtain ⟨F, hF, hFe⟩ := ih (List.nodup_cons.mp hvs).2 _ _ hE'
      refine ⟨F ++ L.map (fun u => (v,u)), ?_, ?_⟩
      · exact List.mem_flatMap.mpr ⟨L, hLrow, List.mem_map.mpr ⟨F, hF, rfl⟩⟩
      · rw [List.toFinset_append, hFe]
        congr 1
        ext e
        simp only [List.mem_toFinset, List.mem_map, Finset.mem_image, hL]

private def candidates (k : Fin 8) : List Code :=
  ((enumerateRows vertices (degreeProfile k)).map
    (fun E => encode fun a b => E.contains (a,b) || E.contains (b,a))).mergeSort

private theorem candidate_of_degreeEdges (k : Fin 8) {E : Finset Pair}
    (hE : E ∈ Q9DegreeRows.degreeEdges vertices (degreeProfile k)) :
    encodeEdges E ∈ candidates k := by
  have hvs : vertices.Nodup := List.nodup_finRange 7
  obtain ⟨F, hF, hFe⟩ := enumerateRows_complete vertices hvs (degreeProfile k) E hE
  apply List.mem_mergeSort.mpr
  refine List.mem_map.mpr ⟨F, hF, ?_⟩
  unfold encodeEdges
  congr 1
  funext a b
  rw [← hFe]
  by_cases ha : (a,b) ∈ F <;> by_cases hb : (b,a) ∈ F <;> simp [ha, hb]

private def survivors (k : Fin 8) : List Code :=
  (candidates k).filter (passes k)

private def recipeCodes (k : Fin 8) : List Code :=
  ((witnesses k).map witnessCode |>.mergeSort).destutter (· ≠ ·)

private def coverCheck (k : Fin 8) : Bool :=
  let cs := candidates k
  let ss := cs.filter (passes k)
  (cs.length == (![6,13,27,54,63,130,250,465] : Fin 8 → ℕ) k) &&
    ((ss.length == (![6,1,15,42,45,117,250,360] : Fin 8 → ℕ) k) &&
      ((ss == recipeCodes k) &&
        (witnesses k).all (fun w => decide (w.2.length = 7 ∧ w.2.Nodup))))

-- Each closed check is kernel-verified separately.
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

private theorem finite_cover (k : Fin 8) :
    (candidates k).length = (![6,13,27,54,63,130,250,465] : Fin 8 → ℕ) k ∧
    (survivors k).length = (![6,1,15,42,45,117,250,360] : Fin 8 → ℕ) k ∧
    survivors k = recipeCodes k ∧
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
  simp only [coverCheck, Bool.and_eq_true] at h
  exact ⟨eq_of_beq h.1, eq_of_beq h.2.1, eq_of_beq h.2.2.1, h.2.2.2⟩

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
      (recipeGraph w.1).Adj (relabel w.2 a) (relabel w.2 b) := by
  apply contactAdj_encode (G := (recipeGraph w.1).comap (relabel w.2))
  intro x y _
  change (!recipeAdj w.1 (relabel w.2 x) (relabel w.2 y)) = true ↔
    ¬ (recipeGraph w.1).Adj (relabel w.2 x) (relabel w.2 y)
  rw [← recipeAdj_spec w.1]
  cases recipeAdj w.1 (relabel w.2 x) (relabel w.2 y) <;> decide

private theorem classify_sorted (G : SimpleGraph Vertex) [DecidableRel G.Adj] (k : Fin 8)
    (hd : ∀ a, Gᶜ.degree a = degreeProfile k a)
    (hcubic : ∀ a, G.degree a = 3 ↔ degreeProfile k a = 3)
    (laws : LocalLaws G) : ∃ kind : Fin 27, Nonempty (G ≃g recipeGraph kind) := by
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
  have hsurv : m ∈ survivors k := by
    apply List.mem_filter.mpr
    refine ⟨candidate_of_degreeEdges k hE, ?_⟩
    exact passes_of_laws k m G hm hcubic laws
  rw [(finite_cover k).2.2.1] at hsurv
  have hcodes : m ∈ ((witnesses k).map witnessCode).mergeSort :=
    (List.destutter_sublist (· ≠ ·) _).subset hsurv
  obtain ⟨w, hw, hcode⟩ := List.mem_map.mp (List.mem_mergeSort.mp hcodes)
  have hvalid := of_decide_eq_true (List.all_eq_true.mp (finite_cover k).2.2.2 w hw)
  refine ⟨w.1, ⟨{
    toEquiv := Equiv.ofBijective (relabel w.2) (witness_bijective w hvalid)
    map_rel_iff' := ?_ }⟩⟩
  intro a b
  have hwitness := witness_adj w a b
  rw [hcode] at hwitness
  exact hwitness.symm.trans (hm a b)

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

private theorem pull_laws {G : SimpleGraph V} {H : SimpleGraph Vertex}
    [DecidableRel G.Adj] [DecidableRel H.Adj] (e : H ≃g G) (laws : LocalLaws G) :
    LocalLaws H := by
  refine ⟨square_of_iso e laws.cubicSquare, second_of_iso e laws.secondNeighbor, ?_, ?_⟩
  · intro a b c hab hbc hca ha hb hc
    exact laws.noCubicTriangle _ _ _ (e.map_adj_iff.mpr hab) (e.map_adj_iff.mpr hbc)
      (e.map_adj_iff.mpr hca) ((e.degree_eq a).trans ha) ((e.degree_eq b).trans hb)
      ((e.degree_eq c).trans hc)
  · have h : Q9ThirteenMaskSevenAxisShapes.EveryEdgeSquare G := by
      intro a b hab
      obtain ⟨c, hac, hcb, d, hda, hbd, hcd⟩ := laws.edgeSquare hab
      exact ⟨c, d, hcb, hda, hac, hcd, hbd.symm⟩
    intro a b hab
    obtain ⟨c, d, hcb, hda, hac, hcd, hdb⟩ := every_square_of_iso e h hab
    exact ⟨c, hac, hcb, d, hda, hdb.symm, hcd⟩

/-- Every seven-vertex graph with fourteen edges, minimum degree three, and
the four contact-graph laws is isomorphic to an audited replay recipe. -/
theorem fourteen_edges_on_seven_vertices (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = 7) (hE : G.edgeFinset.card = 14)
    (hmin : ∀ a, 3 ≤ G.degree a) (laws : LocalLaws G) :
    ∃ kind : Fin 27, Nonempty (recipeGraph kind ≃g G) := by
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
  have htotal : (∑ a : Vertex, H.degree a) = 28 := by
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
  have hsum : (∑ a : Vertex, d a) = 14 := by
    have hs : (∑ a : Vertex, (H.degree a + d a)) = 42 := by
      simp [hsumAt, hcard]
    rw [Finset.sum_add_distrib, htotal] at hs
    omega
  obtain ⟨k, hk⟩ := find_profile d hbound hsort hsum
  have hcubic (a : Vertex) : H.degree a = 3 ↔ degreeProfile k a = 3 := by
    rw [← hk a]
    have := hsumAt a
    omega
  obtain ⟨kind, ⟨toRecipe⟩⟩ := classify_sorted H k hk hcubic (pull_laws iso laws)
  exact ⟨kind, ⟨toRecipe.symm.trans iso⟩⟩

end Q9FourteenMaskSevenAxisClassification
end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement
