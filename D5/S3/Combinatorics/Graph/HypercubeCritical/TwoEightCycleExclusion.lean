/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/TwoEightCycleExclusion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/TwoEightCycleExclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/Combinatorics/Graph/HypercubeCritical/TwoEightCycleExclusion.claim; result=D5/S3/Combinatorics/Graph/HypercubeCritical/TwoEightCycleExclusion.result; claim=D5/S3/Combinatorics/Graph/HypercubeCritical/TwoEightCycleExclusion.claim
   digest: A real two-disjoint-C8 high-cycle branch cannot occur in a finite induced cube slice. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricLowPartners
import D5.S3.Combinatorics.Graph.HypercubeCritical.SubdividedMobiusKantor
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Ring.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-! Hong, Wu and Xia, arXiv:2610.09483v1, section 7 Problem 2 asks whether
f2(Q9) is three or four. This module excludes the branch in which all high
vertices induce exactly two disjoint eight-cycles. It does not classify the
other high graphs or settle the external problem. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.TwoEightCycleExclusion

open SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting
open D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricLowPartners

open private unique_low_partner from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricLowPartners
open private lowPair low_pair_excluded_by_common_high low_pair_excluded_by_short_paths from
  D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceLabels
open private three_walk_endpoint_injective from
  D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting
open private graph edges from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SubdividedMobiusKantor

private def distance (a b : Fin 8) : Nat := min (a - b).val (b - a).val
private def Separated (p : Fin 8 → Fin 8) : Prop :=
  (∀ i, 3 ≤ distance (p i) (p (i + 1))) ∧
    ∀ i, 2 ≤ distance (p i) (p (i + 2))
private theorem local_three_points :
    ∀ a b c : Fin 8,
      3 ≤ distance a b → 3 ≤ distance b c → 2 ≤ distance a c →
        (b = a + 3 ∧ c = b + 3) ∨ (b = a + 5 ∧ c = b + 5) := by
  decide +kernel
private theorem one_twice : ∀ i : Fin 8, (i + 1) + 1 = i + 2 := by decide +kernel
private theorem three_ne_five : ∀ a : Fin 8, a + 3 ≠ a + 5 := by decide +kernel
private theorem local_at (p : Fin 8 → Fin 8) (h : Separated p) (i : Fin 8) :
    (p (i + 1) = p i + 3 ∧ p (i + 2) = p (i + 1) + 3) ∨
      (p (i + 1) = p i + 5 ∧ p (i + 2) = p (i + 1) + 5) := by
  apply local_three_points (p i) (p (i + 1)) (p (i + 2)) (h.1 i)
  · simpa only [one_twice] using h.1 (i + 1)
  · exact h.2 i
private theorem propagate (p : Fin 8 → Fin 8) (h : Separated p)
    (d : Fin 8) (hd : d = 3 ∨ d = 5) (i : Fin 8)
    (hi : p (i + 1) = p i + d) :
    p (i + 2) = p (i + 1) + d := by
  rcases hd with rfl | rfl
  · rcases local_at p h i with hs | hs
    · exact hs.2
    · exact False.elim (three_ne_five (p i) (hi.symm.trans hs.1))
  · rcases local_at p h i with hs | hs
    · exact False.elim (three_ne_five (p i) (hs.1.symm.trans hi))
    · exact hs.2
private def chain (a d : Fin 8) (i : Fin 8) : Fin 8 :=
  Nat.rec a (fun _ x => x + d) i.val
private theorem chain_eq_affine : ∀ a d i : Fin 8, chain a d i = a + d * i := by
  decide +kernel
private theorem affine_of_first (p : Fin 8 → Fin 8) (h : Separated p)
    (d : Fin 8) (hd : d = 3 ∨ d = 5) (h1 : p 1 = p 0 + d) :
    ∀ i, p i = p 0 + d * i := by
  have h2 : p 2 = p 1 + d := propagate p h d hd 0 h1
  have h3 : p 3 = p 2 + d := propagate p h d hd 1 h2
  have h4 : p 4 = p 3 + d := propagate p h d hd 2 h3
  have h5 : p 5 = p 4 + d := propagate p h d hd 3 h4
  have h6 : p 6 = p 5 + d := propagate p h d hd 4 h5
  have h7 : p 7 = p 6 + d := propagate p h d hd 5 h6
  intro i
  calc
    p i = chain (p 0) d i := by fin_cases i <;> simp [chain, h1, h2, h3, h4, h5, h6, h7]
    _ = p 0 + d * i := chain_eq_affine _ _ _
private theorem matching_classification (p : Fin 8 → Fin 8) (h : Separated p) :
    (∀ i, p i = p 0 + 3 * i) ∨ (∀ i, p i = p 0 + 5 * i) := by
  rcases local_at p h 0 with hs | hs
  · exact Or.inl (affine_of_first p h 3 (Or.inl rfl) hs.1)
  · exact Or.inr (affine_of_first p h 5 (Or.inr rfl) hs.1)

private theorem bipartition_color
    {m : ℕ} {G : SimpleGraph (Fin m)} {L R : Finset (Fin m)}
    (hpart : G.IsBipartiteWith (L : Set (Fin m)) (R : Set (Fin m)))
    {a b : Fin m} (hab : G.Adj a b) :
    decide (a ∈ L) ≠ decide (b ∈ L) := by
  rcases hpart.mem_of_adj hab with ⟨haL, hbR⟩ | ⟨haR, hbL⟩
  · change a ∈ L at haL
    have hbnot : b ∉ L := fun hbL => Set.disjoint_left.mp hpart.disjoint hbL hbR
    simp [haL, hbnot]
  · change b ∈ L at hbL
    have hanot : a ∉ L := fun haL => Set.disjoint_left.mp hpart.disjoint haL haR
    simp [hanot, hbL]
private theorem bool_ne_ne : ∀ a b c : Bool, a ≠ b → b ≠ c → a = c := by decide +kernel
private theorem cycle_successor : ∀ i : Fin 8, (cycleGraph 8).Adj i (i + 1) := by decide +kernel
private theorem index_ne_add_two : ∀ i : Fin 8, i ≠ i + 2 := by decide +kernel
private theorem cycle_color_parity :
    ∀ c : Fin 8 → Bool, (∀ i, c i ≠ c (i + 1)) →
      ∀ a b : Fin 8, (c a = c b ↔ a.val % 2 = b.val % 2) := by decide +kernel
private theorem distance_three_of_parity :
    ∀ a b : Fin 8, a.val % 2 ≠ b.val % 2 → ¬ (cycleGraph 8).Adj a b →
      3 ≤ distance a b := by decide +kernel
private theorem distance_two_of_parity :
    ∀ a b : Fin 8, a ≠ b → a.val % 2 = b.val % 2 → 2 ≤ distance a b := by decide +kernel
private theorem separated_of_coloring (p : Fin 8 → Fin 8) (hp : Function.Injective p)
    (c : Fin 8 → Bool) (hc : ∀ i, c i ≠ c (i + 1))
    (hmatch : ∀ i, c (p i) ≠ c (p (i + 1)))
    (hnoadj : ∀ i, ¬ (cycleGraph 8).Adj (p i) (p (i + 1))) : Separated p := by
  refine ⟨?_, ?_⟩
  · intro i
    apply distance_three_of_parity (p i) (p (i + 1)) ?_ (hnoadj i)
    intro he
    exact hmatch i ((cycle_color_parity c hc _ _).mpr he)
  · intro i
    apply distance_two_of_parity (p i) (p (i + 2))
    · intro he; exact index_ne_add_two i (hp he)
    · apply (cycle_color_parity c hc _ _).mp
      apply bool_ne_ne _ _ _ (hmatch i)
      simpa only [one_twice] using hmatch (i + 1)
private theorem matching_endpoints_not_adjacent
    {m : ℕ} {G : SimpleGraph (Fin m)} {L R : Finset (Fin m)}
    (hpart : G.IsBipartiteWith (L : Set (Fin m)) (R : Set (Fin m)))
    (hg : (8 : ℕ∞) ≤ G.egirth) (u v ell : Fin 8 → Fin m) (p : Fin 8 → Fin 8)
    (huv : ∀ i j, u i ≠ v j) (hlu : ∀ i j, ell i ≠ u j) (hlv : ∀ i j, ell i ≠ v j)
    (hru : ∀ i, G.Adj (u i) (ell i)) (hrv : ∀ i, G.Adj (v (p i)) (ell i))
    {i j : Fin 8} (hij : G.Adj (u i) (u j)) : ¬ G.Adj (v (p i)) (v (p j)) := by
  intro hbottom
  have forbidden (L' R' : Finset (Fin m))
      (hp : G.IsBipartiteWith (L' : Set (Fin m)) (R' : Set (Fin m)))
      (hi : ell i ∈ L') : False := by
    have he := three_walk_endpoint_injective hp hg hi hi
      (hru i).symm hij (hru j) (hrv i).symm hbottom (hrv j)
      (hlu i j) (hlu j i).symm (hlv i (p j)) (hlv j (p i)).symm ⟨rfl, rfl⟩
    exact huv i (p i) he.2.1
  rcases hpart.mem_of_adj (hru i) with hs | hs
  · exact forbidden R L hpart.symm hs.2
  · exact forbidden L R hpart hs.2
private theorem separated_of_actual_cycles
    {m : ℕ} {G : SimpleGraph (Fin m)} {L R : Finset (Fin m)}
    (hpart : G.IsBipartiteWith (L : Set (Fin m)) (R : Set (Fin m)))
    (hg : (8 : ℕ∞) ≤ G.egirth) (u v ell : Fin 8 → Fin m) (p : Fin 8 → Fin 8)
    (hp : Function.Injective p) (huv : ∀ i j, u i ≠ v j)
    (hlu : ∀ i j, ell i ≠ u j) (hlv : ∀ i j, ell i ≠ v j)
    (hu : ∀ i, G.Adj (u i) (u (i + 1)))
    (hv : ∀ i j, (cycleGraph 8).Adj i j → G.Adj (v i) (v j))
    (hru : ∀ i, G.Adj (u i) (ell i))
    (hrv : ∀ i, G.Adj (v (p i)) (ell i)) : Separated p := by
  let c : Fin 8 → Bool := fun i => decide (v i ∈ L)
  have hc : ∀ i, c i ≠ c (i + 1) := by
    intro i; exact bipartition_color hpart (hv i (i + 1) (cycle_successor i))
  have hr : ∀ i, c (p i) = decide (u i ∈ L) := by
    intro i; exact bool_ne_ne _ _ _ (bipartition_color hpart (hrv i))
      (bipartition_color hpart (hru i)).symm
  have hmatch : ∀ i, c (p i) ≠ c (p (i + 1)) := by
    intro i; rw [hr i, hr (i + 1)]
    exact bipartition_color hpart (hu i)
  apply separated_of_coloring p hp c hc hmatch
  intro i hij
  exact matching_endpoints_not_adjacent hpart hg u v ell p huv hlu hlv hru hrv
    (hu i) (hv (p i) (p (i + 1)) hij)

private theorem cycle_adj_iff : ∀ i j : Fin 8,
    (cycleGraph 8).Adj i j ↔ j = i + 1 ∨ j = i + 7 := by
  decide +kernel

open Classical in
/-- Existence of an actual induced cube slice with the two-C8 high graph. -/
def claim : Prop :=
  ∃ m n : ℕ, ∃ G : SimpleGraph (Fin m), ∃ L R : Finset (Fin m),
    ∃ f : Fin m → (Fin n → Bool),
    ∃ u v : Fin 8 → Fin m,
      (Function.Injective f ∧
       (∀ a b, G.Adj a b ↔ (hypercube n).Adj (f a) (f b)) ∧
       G.IsBipartiteWith (L : Set (Fin m)) (R : Set (Fin m)) ∧
       (∀ x, G.degree x = 2 ∨ G.degree x = 3) ∧
       (∀ {x y}, G.Adj x y → G.degree x = 2 → G.degree y = 2 → False) ∧
       (8 : ℕ∞) ≤ G.egirth ∧
       (Function.Injective u ∧ Function.Injective v) ∧
       (∀ i j, u i ≠ v j) ∧
       (∀ i, G.degree (u i) = 3) ∧ (∀ i, G.degree (v i) = 3) ∧
       (∀ x, G.degree x = 3 → ∃ i, x = u i ∨ x = v i) ∧
       (∀ i j, G.Adj (u i) (u j) ↔ (cycleGraph 8).Adj i j) ∧
       (∀ i j, G.Adj (v i) (v j) ↔ (cycleGraph 8).Adj i j) ∧
       (∀ i j, ¬ G.Adj (u i) (v j)))

open Classical in
private theorem high_neighbor_count
    {m : ℕ} {G : SimpleGraph (Fin m)}
    {u v : Fin 8 → Fin m}
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hdu : ∀ i, G.degree (u i) = 3)
    (hdv : ∀ i, G.degree (v i) = 3)
    (hcover : ∀ x, G.degree x = 3 → ∃ i, x = u i ∨ x = v i)
    (hcycleU : ∀ i j, G.Adj (u i) (u j) ↔ (cycleGraph 8).Adj i j)
    (hcycleV : ∀ i j, G.Adj (v i) (v j) ↔ (cycleGraph 8).Adj i j)
    (hcross : ∀ i j, ¬ G.Adj (u i) (v j)) :
    (∀ i, (degreeThree G (G.neighborFinset (u i))).card = 2) ∧
    (∀ i, (degreeThree G (G.neighborFinset (v i))).card = 2) := by
  have oneU (i : Fin 8) :
      degreeThree G (G.neighborFinset (u i)) = {u (i + 1), u (i + 7)} := by
    ext x
    constructor
    · intro hx
      have hxa : G.Adj (u i) x :=
        (G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hx).1
      obtain ⟨j, hj⟩ := hcover x (Finset.mem_filter.mp hx).2
      rcases hj with rfl | rfl
      · have hc : (cycleGraph 8).Adj i j := (hcycleU i j).mp hxa
        rw [cycle_adj_iff i j] at hc
        rcases hc with rfl | rfl <;> simp
      · exact False.elim (hcross i j hxa)
    · intro hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_filter.mpr
          ⟨(G.mem_neighborFinset _ _).mpr ((hcycleU i (i + 1)).mpr
            (by rw [cycle_adj_iff]; simp)), hdu _⟩
      · exact Finset.mem_filter.mpr
          ⟨(G.mem_neighborFinset _ _).mpr ((hcycleU i (i + 7)).mpr
            (by rw [cycle_adj_iff]; simp)), hdu _⟩
  have oneV (i : Fin 8) :
      degreeThree G (G.neighborFinset (v i)) = {v (i + 1), v (i + 7)} := by
    ext x
    constructor
    · intro hx
      have hxa : G.Adj (v i) x :=
        (G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hx).1
      obtain ⟨j, hj⟩ := hcover x (Finset.mem_filter.mp hx).2
      rcases hj with rfl | rfl
      · exact False.elim (hcross j i hxa.symm)
      · have hc : (cycleGraph 8).Adj i j := (hcycleV i j).mp hxa
        rw [cycle_adj_iff i j] at hc
        rcases hc with rfl | rfl <;> simp
    · intro hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_filter.mpr
          ⟨(G.mem_neighborFinset _ _).mpr ((hcycleV i (i + 1)).mpr
            (by rw [cycle_adj_iff]; simp)), hdv _⟩
      · exact Finset.mem_filter.mpr
          ⟨(G.mem_neighborFinset _ _).mpr ((hcycleV i (i + 7)).mpr
            (by rw [cycle_adj_iff]; simp)), hdv _⟩
  constructor
  · intro i
    rw [oneU i]
    have hn : i + 1 ≠ i + 7 := (by decide : ∀ k : Fin 8, k + 1 ≠ k + 7) i
    exact Finset.card_pair_eq_two_iff.mpr (fun he => hn (huinj he))
  · intro i
    rw [oneV i]
    have hn : i + 1 ≠ i + 7 := (by decide : ∀ k : Fin 8, k + 1 ≠ k + 7) i
    exact Finset.card_pair_eq_two_iff.mpr (fun he => hn (hvinj he))

open Classical in
private theorem same_cycle_low_pair_excluded
    {m : ℕ} {G : SimpleGraph (Fin m)} {L R : Finset (Fin m)}
    (hpart : G.IsBipartiteWith (L : Set (Fin m)) (R : Set (Fin m)))
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (u : Fin 8 → Fin m) (huinj : Function.Injective u)
    (hdu : ∀ i, G.degree (u i) = 3)
    (hcycle : ∀ i j, G.Adj (u i) (u j) ↔ (cycleGraph 8).Adj i j)
    {i j : Fin 8} (hij : i ≠ j) :
    ¬ lowPair G (u i) (u j) := by
  intro hpair
  obtain ⟨w, hw, hiw, hjw⟩ := hpair
  let c : Fin 8 → Bool := fun k => decide (u k ∈ L)
  have hc : ∀ k, c k ≠ c (k + 1) := by
    intro k
    exact bipartition_color hpart ((hcycle _ _).mpr (cycle_successor k))
  have heq : c i = c j := bool_ne_ne _ _ _
    (bipartition_color hpart hiw) (bipartition_color hpart hjw).symm
  have hpar : i.val % 2 = j.val % 2 := (cycle_color_parity c hc i j).mp heq
  have hcases : j = i + 2 ∨ j = i + 4 ∨ j = i + 6 :=
    (by decide +kernel : ∀ a b : Fin 8, a ≠ b → a.val % 2 = b.val % 2 →
      b = a + 2 ∨ b = a + 4 ∨ b = a + 6) i j hij hpar
  have hne : u i ≠ u j := fun he => hij (huinj he)
  have forbidden (L' R' : Finset (Fin m))
      (hp : G.IsBipartiteWith (L' : Set (Fin m)) (R' : Set (Fin m)))
      (hiR : u i ∈ R') : False := by
    rcases hcases with rfl | rfl | rfl
    · exact low_pair_excluded_by_common_high hp hg hiR (hdu (i + 1))
        ((hcycle _ _).mpr (by exact (by decide : ∀ k : Fin 8,
          (cycleGraph 8).Adj k (k + 1)) i))
        ((hcycle _ _).mpr (by exact (by decide : ∀ k : Fin 8,
          (cycleGraph 8).Adj (k + 2) (k + 1)) i)) hne ⟨w, hw, hiw, hjw⟩
    · exact low_pair_excluded_by_short_paths hp hg hiR (hdu (i + 1)) (hdu (i + 3))
        ((hcycle _ _).mpr (cycle_successor i))
        ((hcycle _ _).mpr ((by decide : ∀ k : Fin 8,
          (cycleGraph 8).Adj (k + 1) (k + 2)) i))
        ((hcycle _ _).mpr ((by decide : ∀ k : Fin 8,
          (cycleGraph 8).Adj (k + 2) (k + 3)) i))
        ((hcycle _ _).mpr ((by decide : ∀ k : Fin 8,
          (cycleGraph 8).Adj (k + 4) (k + 3)) i)) hne
        (fun he => ((by decide : ∀ k : Fin 8, k ≠ k + 2) i) (huinj he))
        (fun he => ((by decide : ∀ k : Fin 8, k + 1 ≠ k + 3) i) (huinj he))
        ⟨w, hw, hiw, hjw⟩
    · exact low_pair_excluded_by_common_high hp hg hiR (hdu (i + 7))
        ((hcycle _ _).mpr ((by decide : ∀ k : Fin 8,
          (cycleGraph 8).Adj k (k + 7)) i))
        ((hcycle _ _).mpr ((by decide : ∀ k : Fin 8,
          (cycleGraph 8).Adj (k + 6) (k + 7)) i)) hne ⟨w, hw, hiw, hjw⟩
  rcases hpart.mem_of_adj hiw with hs | hs
  · exact forbidden R L hpart.symm hs.1
  · exact forbidden L R hpart hs.1


private def blockIndex (t : Fin 3) (i : Fin 8) : Fin 24 :=
  ⟨8 * t.val + i.val, by omega⟩

private def decode (a : Fin 24) : Fin 3 × Fin 8 :=
  (⟨a.val / 8, by omega⟩, ⟨a.val % 8, by omega⟩)

private theorem encode_decode : ∀ a, blockIndex (decode a).1 (decode a).2 = a := by
  decide +kernel

private def blockMap {m : ℕ} (p : Fin 8 → Fin 8)
    (u v ell : Fin 8 → Fin m) (t : Fin 3) (i : Fin 8) : Fin m :=
  if t = 0 then u i else if t = 1 then v (p i) else ell i

private def mkMap {m : ℕ} (p : Fin 8 → Fin 8)
    (u v ell : Fin 8 → Fin m) (a : Fin 24) : Fin m :=
  blockMap p u v ell (decode a).1 (decode a).2

private def blockAdj (t s : Fin 3) (i j : Fin 8) : Prop :=
  (t = 0 ∧ s = 0 ∧ (cycleGraph 8).Adj i j) ∨
  (t = 1 ∧ s = 1 ∧ (j = i + 3 ∨ j = i + 5)) ∨
  (t = 0 ∧ s = 2 ∧ i = j) ∨ (t = 2 ∧ s = 0 ∧ i = j) ∨
  (t = 1 ∧ s = 2 ∧ i = j) ∨ (t = 2 ∧ s = 1 ∧ i = j)

private instance (t s : Fin 3) (i j : Fin 8) : Decidable (blockAdj t s i j) := by
  unfold blockAdj
  infer_instance

private instance : DecidableRel graph.Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ ((a, b) ∈ edges ∨ (b, a) ∈ edges)))

private theorem graph_blockAdj : ∀ t s i j,
    graph.Adj (blockIndex t i) (blockIndex s j) ↔ blockAdj t s i j := by
  decide +kernel

private theorem affine_cycle_transport_three : ∀ a i j : Fin 8,
    (cycleGraph 8).Adj (a + 3 * i) (a + 3 * j) ↔
      j = i + 3 ∨ j = i + 5 := by
  decide +kernel

private theorem affine_cycle_transport_five : ∀ a i j : Fin 8,
    (cycleGraph 8).Adj (a + 5 * i) (a + 5 * j) ↔
      j = i + 3 ∨ j = i + 5 := by
  decide +kernel

open Classical in
private theorem top_low_adj
    {m : ℕ} {G : SimpleGraph (Fin m)} (u v ell : Fin 8 → Fin m)
    (p : Fin 8 → Fin 8) (huv : ∀ i j, u i ≠ v j)
    (huinj : Function.Injective u)
    (hN : ∀ j, G.neighborFinset (ell j) = {u j, v (p j)}) :
    ∀ i j, G.Adj (u i) (ell j) ↔ i = j := by
  intro i j
  constructor
  · intro h
    have hm : u i ∈ G.neighborFinset (ell j) :=
      (G.mem_neighborFinset _ _).mpr h.symm
    rw [hN j] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm
    · exact huinj hm
    · exact False.elim (huv i (p j) hm)
  · intro hij
    subst j
    have hm : u i ∈ G.neighborFinset (ell i) := by rw [hN i]; simp
    exact (G.mem_neighborFinset _ _).mp hm |>.symm

open Classical in
private theorem bottom_low_adj
    {m : ℕ} {G : SimpleGraph (Fin m)} (u v ell : Fin 8 → Fin m)
    (p : Fin 8 → Fin 8) (huv : ∀ i j, u i ≠ v j)
    (hvinj : Function.Injective v) (hpinj : Function.Injective p)
    (hN : ∀ j, G.neighborFinset (ell j) = {u j, v (p j)}) :
    ∀ i j, G.Adj (v (p i)) (ell j) ↔ i = j := by
  intro i j
  constructor
  · intro h
    have hm : v (p i) ∈ G.neighborFinset (ell j) :=
      (G.mem_neighborFinset _ _).mpr h.symm
    rw [hN j] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm
    · exact False.elim (huv j (p i) hm.symm)
    · exact hpinj (hvinj hm)
  · intro hij
    subst j
    have hm : v (p i) ∈ G.neighborFinset (ell i) := by rw [hN i]; simp
    exact (G.mem_neighborFinset _ _).mp hm |>.symm

open Classical in
private theorem low_low_nonadj
    {m : ℕ} {G : SimpleGraph (Fin m)} (ell : Fin 8 → Fin m)
    (hell2 : ∀ i, G.degree (ell i) = 2)
    (hlow : ∀ {x y}, G.Adj x y → G.degree x = 2 → G.degree y = 2 → False) :
    ∀ i j, ¬ G.Adj (ell i) (ell j) := by
  intro i j h
  exact hlow h (hell2 i) (hell2 j)

private theorem labels_map_injective
    {m : ℕ}
    (p : Fin 8 → Fin 8) (u v ell : Fin 8 → Fin m)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hellinj : Function.Injective ell) (hpinj : Function.Injective p)
    (huv : ∀ i j, u i ≠ v j)
    (hlu : ∀ i j, ell i ≠ u j) (hlv : ∀ i j, ell i ≠ v j) :
    Function.Injective (mkMap p u v ell) := by
  have hb : ∀ t s i j, blockMap p u v ell t i = blockMap p u v ell s j →
      t = s ∧ i = j := by
    intro t s i j he
    fin_cases t <;> fin_cases s <;> simp only [blockMap] at he
    · exact ⟨rfl, huinj he⟩
    · exact False.elim (huv i (p j) he)
    · exact False.elim (hlu j i he.symm)
    · exact False.elim (huv j (p i) he.symm)
    · exact ⟨rfl, hpinj (hvinj he)⟩
    · exact False.elim (hlv j (p i) he.symm)
    · exact False.elim (hlu i j he)
    · exact False.elim (hlv i (p j) he)
    · exact ⟨rfl, hellinj he⟩
  intro a b he
  have hd : decode a = decode b := Prod.ext
    (hb _ _ _ _ he).1 (hb _ _ _ _ he).2
  calc
    a = blockIndex (decode a).1 (decode a).2 := (encode_decode a).symm
    _ = blockIndex (decode b).1 (decode b).2 := by rw [hd]
    _ = b := encode_decode b

private theorem labels_map_adj
    {m : ℕ} {G : SimpleGraph (Fin m)} (p : Fin 8 → Fin 8)
    (u v ell : Fin 8 → Fin m)
    (hcross : ∀ i j, ¬ G.Adj (u i) (v j))
    (hcycleU : ∀ i j, G.Adj (u i) (u j) ↔ (cycleGraph 8).Adj i j)
    (hbottom : ∀ i j, G.Adj (v (p i)) (v (p j)) ↔
      (j = i + 3 ∨ j = i + 5))
    (htoplow : ∀ i j, G.Adj (u i) (ell j) ↔ i = j)
    (hbotlow : ∀ i j, G.Adj (v (p i)) (ell j) ↔ i = j)
    (hlowlow : ∀ i j, ¬ G.Adj (ell i) (ell j)) :
    ∀ a b, graph.Adj a b ↔ G.Adj (mkMap p u v ell a) (mkMap p u v ell b) := by
  have hb : ∀ t s i j, blockAdj t s i j ↔
      G.Adj (blockMap p u v ell t i) (blockMap p u v ell s j) := by
    intro t s i j
    fin_cases t <;> fin_cases s <;>
      simp [blockMap, blockAdj]
    · exact (hcycleU i j).symm
    · exact hcross i (p j)
    · exact (htoplow i j).symm
    · exact fun h => hcross j (p i) h.symm
    · exact (hbottom i j).symm
    · exact (hbotlow i j).symm
    · rw [G.adj_comm, htoplow, eq_comm]
    · rw [G.adj_comm, hbotlow, eq_comm]
    · exact hlowlow i j
  intro a b
  conv_lhs => rw [← encode_decode a, ← encode_decode b]
  rw [graph_blockAdj]
  exact hb _ _ _ _

open Classical in
private theorem labels_refute
    {m n : ℕ} {G : SimpleGraph (Fin m)}
    {f : Fin m → (Fin n → Bool)} {u v ell : Fin 8 → Fin m}
    (hf : Function.Injective f)
    (hind : ∀ a b, G.Adj a b ↔ (hypercube n).Adj (f a) (f b))
    (p : Fin 8 → Fin 8)
    (hcycleU : ∀ i j, G.Adj (u i) (u j) ↔ (cycleGraph 8).Adj i j)
    (hcycleV : ∀ i j, G.Adj (v i) (v j) ↔ (cycleGraph 8).Adj i j)
    (hplus : (∀ i, p i = p 0 + 3 * i) ∨ (∀ i, p i = p 0 + 5 * i))
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hellinj : Function.Injective ell) (hpinj : Function.Injective p)
    (huv : ∀ i j, u i ≠ v j)
    (hlu : ∀ i j, ell i ≠ u j) (hlv : ∀ i j, ell i ≠ v j)
    (hN : ∀ i, G.neighborFinset (ell i) = {u i, v (p i)})
    (hcross : ∀ i j, ¬ G.Adj (u i) (v j))
    (hellow : ∀ i j, ¬ G.Adj (ell i) (ell j)) : False := by
  classical
  have hbottom : ∀ i j, G.Adj (v (p i)) (v (p j)) ↔
      (j = i + 3 ∨ j = i + 5) := by
    intro i j
    rw [hcycleV]
    rcases hplus with hs | hs
    · rw [hs i, hs j]
      exact affine_cycle_transport_three _ _ _
    · rw [hs i, hs j]
      exact affine_cycle_transport_five _ _ _
  have htoplow := top_low_adj u v ell p huv huinj hN
  have hbotlow := bottom_low_adj u v ell p huv hvinj hpinj hN
  have hmapinj := labels_map_injective p u v ell huinj hvinj hellinj hpinj huv hlu hlv
  have hmapadj := labels_map_adj p u v ell hcross hcycleU
    hbottom htoplow hbotlow hellow
  apply (D5.S3.Combinatorics.Graph.HypercubeCritical.SubdividedMobiusKantor.result)
  refine ⟨n, fun a => f (mkMap p u v ell a), ?_, ?_⟩
  · exact fun a b hab => hmapinj (hf hab)
  · intro a b
    rw [hmapadj a b, hind]

/-- This high-cycle branch occurs in no finite induced cube slice. -/
theorem result : ¬ claim := by
  classical
  rintro ⟨m, n, G, L, R, f, u, v, ⟨hf, hind, hpart, hdeg, hlow, hg,
    ⟨huinj, hvinj⟩, huv, hdu, hdv, hcover, hcycleU, hcycleV,
    hcross⟩⟩
  have hcounts := high_neighbor_count huinj hvinj hdu hdv hcover hcycleU hcycleV hcross
  have hexU : ∀ i : Fin 8, ∃ w y : Fin m,
      G.degree w = 2 ∧ G.degree y = 3 ∧ u i ≠ y ∧
      G.Adj (u i) w ∧ G.Adj y w ∧ G.neighborFinset w = {u i, y} ∧
      (∀ z, u i ≠ z → lowPair G (u i) z → z = y) ∧
      (∀ w', G.degree w' = 2 → G.Adj (u i) w' → w' = w) := by
    intro i
    exact unique_low_partner hdeg hlow (hdu i) (hcounts.1 i)
  have hexV : ∀ i : Fin 8, ∃ w y : Fin m,
      G.degree w = 2 ∧ G.degree y = 3 ∧ v i ≠ y ∧
      G.Adj (v i) w ∧ G.Adj y w ∧ G.neighborFinset w = {v i, y} ∧
      (∀ z, v i ≠ z → lowPair G (v i) z → z = y) ∧
      (∀ w', G.degree w' = 2 → G.Adj (v i) w' → w' = w) := by
    intro i
    exact unique_low_partner hdeg hlow (hdv i) (hcounts.2 i)
  choose ell yu hell using hexU
  choose ellV yv hellV using hexV
  have hellU (i : Fin 8) :
      G.degree (ell i) = 2 ∧ G.degree (yu i) = 3 ∧ u i ≠ yu i ∧
      G.Adj (u i) (ell i) ∧ G.Adj (yu i) (ell i) ∧
      G.neighborFinset (ell i) = {u i, yu i} ∧
      (∀ z, u i ≠ z → lowPair G (u i) z → z = yu i) ∧
      (∀ w', G.degree w' = 2 → G.Adj (u i) w' → w' = ell i) := hell i
  have hellV' (i : Fin 8) :
      G.degree (ellV i) = 2 ∧ G.degree (yv i) = 3 ∧ v i ≠ yv i ∧
      G.Adj (v i) (ellV i) ∧ G.Adj (yv i) (ellV i) ∧
      G.neighborFinset (ellV i) = {v i, yv i} ∧
      (∀ z, v i ≠ z → lowPair G (v i) z → z = yv i) ∧
      (∀ w', G.degree w' = 2 → G.Adj (v i) w' → w' = ellV i) := hellV i
  have hEll2 : ∀ i, G.degree (ell i) = 2 := fun i => (hellU i).1
  have hUell : ∀ i, G.Adj (u i) (ell i) :=
    fun i => (hellU i).2.2.2.1
  have hYell : ∀ i, G.Adj (yu i) (ell i) :=
    fun i => (hellU i).2.2.2.2.1
  have hNell : ∀ i, G.neighborFinset (ell i) = {u i, yu i} :=
    fun i => (hellU i).2.2.2.2.2.1
  have hVlowuniq : ∀ i w', G.degree w' = 2 → G.Adj (v i) w' → w' = ellV i :=
    fun i => (hellV' i).2.2.2.2.2.2.2
  have hsameU : ∀ i j, i ≠ j → ¬ lowPair G (u i) (u j) := by
    intro i j hij
    exact same_cycle_low_pair_excluded hpart hg u huinj hdu hcycleU hij
  have hyu_not_u : ∀ i j, yu i ≠ u j := by
    intro i j he
    by_cases hji : i = j
    · subst j; exact (hellU i).2.2.1 he.symm
    · apply (hsameU i j hji)
      exact ⟨ell i, hEll2 i, hUell i,
        he ▸ hYell i⟩
  have hyu_v : ∀ i, ∃ j, yu i = v j := by
    intro i
    obtain ⟨j, hj⟩ := hcover (yu i) (hellU i).2.1
    rcases hj with hj | hj
    · exact False.elim (hyu_not_u i _ hj)
    · exact ⟨j, hj⟩
  choose p hp using hyu_v
  have hp_pair : ∀ i, yu i = v (p i) := hp
  have hell_low_ne_high : (∀ i j, ell i ≠ u j) ∧ (∀ i j, ell i ≠ v j) := by
    constructor
    · intro i j he
      have hedeg := congrArg (fun z : Fin m => G.degree z) he
      rw [(hellU i).1, hdu j] at hedeg
      omega
    · intro i j he
      have hedeg := congrArg (fun z : Fin m => G.degree z) he
      rw [(hellU i).1, hdv j] at hedeg
      omega
  have hell_inj : Function.Injective ell := by
    intro i j hij
    by_contra hne
    apply hsameU i j hne
    exact ⟨ell j, hEll2 j, hij ▸ hUell i, hUell j⟩
  have hp_inj : Function.Injective p := by
    intro i j hpij
    have hlowi : G.Adj (v (p i)) (ell i) := by
      simpa [hp_pair i] using hYell i
    have hlowj : G.Adj (v (p j)) (ell j) := by
      simpa [hp_pair j] using hYell j
    have heq : ell i = ell j := by
      have hei := hVlowuniq (p i) (ell i) (hEll2 i) hlowi
      have hej := hVlowuniq (p i) (ell j) (hEll2 j) (by simpa [hpij] using hlowj)
      exact hei.trans hej.symm
    exact hell_inj heq
  have hsep := separated_of_actual_cycles hpart hg u v ell p hp_inj huv
    hell_low_ne_high.1 hell_low_ne_high.2
    (fun i => (hcycleU i (i + 1)).mpr (by rw [cycle_adj_iff]; simp))
    (fun i j h => (hcycleV i j).mpr h)
    hUell
    (fun i => by simpa [hp_pair i] using hYell i)
  have hclass := matching_classification p hsep
  have hellow : ∀ i j, ¬ G.Adj (ell i) (ell j) :=
    low_low_nonadj ell hEll2 hlow
  apply labels_refute hf hind p hcycleU hcycleV hclass huinj hvinj hell_inj hp_inj huv
    hell_low_ne_high.1 hell_low_ne_high.2
    (fun i => by simpa [hp_pair i] using hNell i)
    hcross hellow

end D5.S3.Combinatorics.Graph.HypercubeCritical.TwoEightCycleExclusion
