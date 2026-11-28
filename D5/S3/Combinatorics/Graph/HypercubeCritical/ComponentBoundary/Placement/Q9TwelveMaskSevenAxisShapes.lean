import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TenMaskGraph
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ContactGraphTriangles
import Init.Data.BitVec.Lemmas

/-!
# Twelve contact edges on seven axes

A cubic root is labeled 0, with neighbors 1, 2, 3. The remaining nine edges
are encoded in fifteen bits. The rooted witnesses permute the two triples
independently. A separate table changes the root label where necessary to
give five unrooted templates.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement
namespace Q9TwelveMaskSevenAxisShapes

open Finset
open scoped BigOperators
open Q9TenMaskGraph (SquareCompletion)
open private square_of_iso from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TenMaskGraph

universe u v

/-- The common-neighbor condition for an edge whose endpoints both have degree three. -/
abbrev SecondCommonNeighbor {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ ⦃x y w : V⦄, G.Adj x y → G.degree x = 3 → G.degree y = 3 →
    G.Adj x w → G.Adj y w → ∃ z, z ≠ w ∧ G.Adj x z ∧ G.Adj y z

private abbrev Pair := Fin 7 × Fin 7

private def tailPair : Fin 15 → Pair :=
  ![(1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 3), (2, 4), (2, 5),
    (2, 6), (3, 4), (3, 5), (3, 6), (4, 5), (4, 6), (5, 6)]

-- The entries involving 0 or the diagonal are unused.
private def tailIndex (i j : Fin 7) : Fin 15 :=
  ![![0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 2, 3, 4], ![0, 0, 0, 5, 6, 7, 8],
    ![0, 1, 5, 0, 9, 10, 11], ![0, 2, 6, 9, 0, 12, 13],
    ![0, 3, 7, 10, 12, 0, 14], ![0, 4, 8, 11, 13, 14, 0]] i j

private theorem tailIndex_symm : ∀ i j, tailIndex i j = tailIndex j i := by
  decide +kernel

private theorem tailPair_index :
    ∀ i j : Fin 7, i ≠ 0 → i < j → tailPair (tailIndex i j) = (i, j) := by
  decide +kernel

private theorem tailPair_spec : ∀ k,
    (tailPair k).1 ≠ 0 ∧ (tailPair k).1 < (tailPair k).2 ∧
      tailIndex (tailPair k).1 (tailPair k).2 = k := by
  decide +kernel

private abbrev Near (i : Fin 7) : Prop := i ≠ 0 ∧ i ≤ 3

private def adjacency (m : BitVec 15) (i j : Fin 7) : Bool :=
  if i = j then false
  else if i = 0 then decide (j ≤ 3)
  else if j = 0 then decide (i ≤ 3)
  else m.getLsb (tailIndex i j)

private theorem adjacency_symm (m : BitVec 15) (i j : Fin 7) :
    adjacency m i j = adjacency m j i := by
  by_cases hij : i = j
  · subst j
    rfl
  have hji : j ≠ i := fun h => hij h.symm
  simp only [adjacency, ite_eq_right hij, ite_eq_right hji, tailIndex_symm i j]
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [hi, hj]

private def graphOfWord (m : BitVec 15) : SimpleGraph (Fin 7) where
  Adj i j := adjacency m i j = true
  symm := ⟨fun i j h => (adjacency_symm m j i).trans h⟩
  loopless := ⟨fun i => by simp [adjacency]⟩

private instance (m : BitVec 15) : DecidableRel (graphOfWord m).Adj :=
  fun i j => inferInstanceAs (Decidable (adjacency m i j = true))

private theorem root_row (m : BitVec 15) (j : Fin 7) :
    (graphOfWord m).Adj 0 j ↔ Near j := by
  change adjacency m 0 j = true ↔ Near j
  by_cases h : j = 0
  · subst j
    simp [adjacency]
  · have h' : (0 : Fin 7) ≠ j := fun e => h e.symm
    simp [adjacency, h, h']

private def encode (adj : Fin 7 → Fin 7 → Bool) : BitVec 15 :=
  (BitVec.ofBoolListLE (List.ofFn fun k => adj (tailPair k).1 (tailPair k).2)).cast
    List.length_ofFn

private theorem encode_bit (adj : Fin 7 → Fin 7 → Bool) (k : Fin 15) :
    (encode adj).getLsb k = adj (tailPair k).1 (tailPair k).2 := by
  change (encode adj).getLsbD k.val = _
  have hk : k.val < (List.ofFn fun t => adj (tailPair t).1 (tailPair t).2).length := by
    simpa only [List.length_ofFn] using k.isLt
  rw [encode, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    ← List.getElem_eq_getD (h := hk) false, List.getElem_ofFn]

private theorem encode_adjacency (m : BitVec 15) : encode (adjacency m) = m := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  change (encode (adjacency m)).getLsb ⟨k, hk⟩ = m.getLsb ⟨k, hk⟩
  rw [encode_bit]
  obtain ⟨hi, hij, hindex⟩ := tailPair_spec ⟨k, hk⟩
  have hj : (tailPair ⟨k, hk⟩).2 ≠ 0 := by
    intro h
    rw [h] at hij
    exact (not_lt_of_ge (Fin.zero_le _)) hij
  simp [adjacency, hi, hj, hij.ne, hindex]

private theorem decode (K : SimpleGraph (Fin 7)) [DecidableRel K.Adj]
    (hroot : ∀ j, K.Adj 0 j ↔ Near j) :
    graphOfWord (encode (fun i j => decide (K.Adj i j))) = K := by
  ext i j
  let m := encode (fun i j => decide (K.Adj i j))
  change (graphOfWord m).Adj i j ↔ K.Adj i j
  have step (a b : Fin 7) (hab : a < b) :
      (graphOfWord m).Adj a b ↔ K.Adj a b := by
    by_cases ha : a = 0
    · subst a
      exact (root_row _ _).trans (hroot _).symm
    have hb : b ≠ 0 := by
      intro h
      subst b
      exact (not_lt_of_ge (Fin.zero_le _)) hab
    change adjacency m a b = true ↔ K.Adj a b
    simp only [adjacency, if_neg hab.ne, if_neg ha, if_neg hb]
    change (encode (fun i j => decide (K.Adj i j))).getLsb (tailIndex a b) = true ↔ K.Adj a b
    simp only [encode_bit, tailPair_index a b ha hab, Prod.fst, Prod.snd, decide_eq_true_eq]
  rcases lt_trichotomy i j with h | rfl | h
  · exact step i j h
  · exact ⟨fun h => ((graphOfWord m).irrefl h).elim, fun h => (K.irrefl h).elim⟩
  · exact ⟨fun h' => ((step j i h).mp h'.symm).symm,
      fun h' => ((step j i h).mpr h'.symm).symm⟩

private def orderedEdges (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj] : Finset Pair :=
  univ.filter fun p => p.1 < p.2 ∧ G.Adj p.1 p.2

-- The ordered representatives give the same cardinality as the Sym2 edge set.
private theorem card_orderedEdges (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj] :
    (orderedEdges G).card = G.edgeFinset.card := by
  apply Finset.card_bij (fun (p : Pair) _ => Sym2.mk p.1 p.2)
  · intro p hp
    exact SimpleGraph.mem_edgeFinset.mpr (mem_filter.mp hp).2.2
  · rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd he
    change Sym2.mk a b = Sym2.mk c d at he
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact ((not_lt_of_gt (mem_filter.mp hab).2.1) (mem_filter.mp hcd).2.1).elim
  · intro q hq
    obtain ⟨a, b⟩ := q
    have h : G.Adj a b := SimpleGraph.mem_edgeFinset.mp hq
    rcases lt_or_gt_of_ne h.ne with hab | hba
    · exact ⟨(a, b), mem_filter.mpr ⟨mem_univ _, hab, h⟩, rfl⟩
    · exact ⟨(b, a), mem_filter.mpr ⟨mem_univ _, hba, h.symm⟩, Sym2.eq_swap⟩

private def rootPairs : Finset Pair := {(0, 1), (0, 2), (0, 3)}

private theorem mem_rootPairs :
    ∀ i j : Fin 7, (i, j) ∈ rootPairs ↔ i = 0 ∧ Near j := by
  decide +kernel

private def tailEmbedding : Fin 15 ↪ Pair where
  toFun := tailPair
  inj' := by
    intro a b h
    change tailPair a = tailPair b at h
    have ha := (tailPair_spec a).2.2
    rw [h, (tailPair_spec b).2.2] at ha
    exact ha.symm

private def selected (m : BitVec 15) : Finset (Fin 15) :=
  univ.filter fun k => m.getLsb k = true

private theorem card_graphOfWord (m : BitVec 15) :
    (graphOfWord m).edgeFinset.card = 3 + (selected m).card := by
  rw [← card_orderedEdges]
  have hdisj : Disjoint rootPairs ((selected m).map tailEmbedding) := by
    apply disjoint_left.mpr
    rintro ⟨i, j⟩ hroot htail
    obtain ⟨k, _, hk⟩ := mem_map.mp htail
    change tailPair k = (i, j) at hk
    have h0 := (mem_rootPairs i j).mp hroot
    exact (tailPair_spec k).1 ((congrArg Prod.fst hk).trans h0.1)
  have hE : orderedEdges (graphOfWord m) = rootPairs ∪ (selected m).map tailEmbedding := by
    apply Finset.ext
    rintro ⟨i, j⟩
    simp only [orderedEdges, mem_filter, mem_univ, true_and, mem_union, mem_rootPairs]
    constructor
    · rintro ⟨hij, hijAdj⟩
      by_cases hi : i = 0
      · subst i
        exact Or.inl ⟨rfl, (root_row m j).mp hijAdj⟩
      · right
        have hj : j ≠ 0 := by
          intro h
          subst j
          exact (not_lt_of_ge (Fin.zero_le _)) hij
        refine mem_map.mpr ⟨tailIndex i j, ?_, tailPair_index i j hi hij⟩
        change adjacency m i j = true at hijAdj
        simpa only [selected, mem_filter, mem_univ, true_and,
          adjacency, if_neg hij.ne, if_neg hi, if_neg hj] using hijAdj
    · rintro (⟨rfl, hj⟩ | htail)
      · exact ⟨Fin.pos_iff_ne_zero.mpr hj.1, (root_row m j).mpr hj⟩
      · obtain ⟨k, hk, hp⟩ := mem_map.mp htail
        change tailPair k = (i, j) at hp
        obtain ⟨hi, hij, hindex⟩ := tailPair_spec k
        rw [hp] at hi hij hindex
        have hj : j ≠ 0 := by
          intro h
          subst j
          exact (not_lt_of_ge (Fin.zero_le _)) hij
        have hbit : m.getLsb k = true := by simpa only [selected, mem_filter, mem_univ,
          true_and] using hk
        refine ⟨hij, ?_⟩
        change adjacency m i j = true
        simpa only [adjacency, if_neg hij.ne, if_neg hi, if_neg hj, hindex] using hbit
  rw [hE, card_union_of_disjoint hdisj, card_map, show rootPairs.card = 3 by decide +kernel]

private theorem count_finRange_eq_card {n : ℕ} (p : Fin n → Bool) :
    (List.finRange n).countP p = (univ.filter fun i => p i = true).card := by
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup
    ((List.nodup_finRange n).filter p), List.toFinset_filter, List.toFinset_finRange]

private def degreeOfWord (m : BitVec 15) (a : Fin 7) : ℕ :=
  (List.finRange 7).countP (adjacency m a)

private theorem degreeOfWord_eq (m : BitVec 15) (a : Fin 7) :
    degreeOfWord m a = (graphOfWord m).degree a := by
  rw [degreeOfWord, count_finRange_eq_card, ← SimpleGraph.card_neighborFinset_eq_degree,
    SimpleGraph.neighborFinset_eq_filter]
  apply congrArg Finset.card
  ext v
  simp only [mem_filter, mem_univ, true_and]
  rfl

private def hasOtherCommonNeighbor (m : BitVec 15) (x y excluded : Fin 7) : Bool :=
  let G := graphOfWord m
  (List.finRange 7).any fun z => decide (z ≠ excluded ∧ G.Adj x z ∧ G.Adj y z)

-- Check edge count and minimum degree before checking both laws at each cubic edge.
private def admissible (m : BitVec 15) : Bool :=
  let G := graphOfWord m
  decide ((List.finRange 15).countP (fun k => m.getLsb k) = 9) &&
    (List.finRange 7).all (fun a => decide (3 ≤ degreeOfWord m a)) &&
    (List.finRange 7).all (fun a =>
      if degreeOfWord m a = 3 then
        (List.finRange 7).all fun v =>
          if G.Adj a v ∧ degreeOfWord m v = 3 then
            (List.finRange 7).all fun c =>
              if G.Adj a c then
                (if v ≠ c then hasOtherCommonNeighbor m v c a else true) &&
                  (if G.Adj v c then hasOtherCommonNeighbor m a v c else true)
              else true
          else true
      else true)

private theorem guard_eq_true {p : Prop} [Decidable p] {test : Bool} :
    (if p then test else true) = true ↔ (p → test = true) := by
  by_cases hp : p <;> simp [hp]

private theorem admissible_iff (m : BitVec 15) :
    admissible m = true ↔
      (graphOfWord m).edgeFinset.card = 12 ∧ (∀ a, 3 ≤ (graphOfWord m).degree a) ∧
      SquareCompletion (graphOfWord m) ∧ SecondCommonNeighbor (graphOfWord m) := by
  have hcount : (List.finRange 15).countP (fun k => m.getLsb k) = (selected m).card :=
    count_finRange_eq_card _
  simp only [admissible, hasOtherCommonNeighbor, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.any_eq_true, List.mem_finRange, true_and, true_implies,
    guard_eq_true]
  simp only [hcount, degreeOfWord_eq, card_graphOfWord]
  constructor
  · rintro ⟨⟨hE, hmin⟩, hlocal⟩
    refine ⟨by omega, hmin, ?_, ?_⟩
    · intro a v c hav hac hvc ha hv
      exact (hlocal a ha v ⟨hav, hv⟩ c hac).1 hvc
    · intro a v w hav ha hv haw hvw
      exact (hlocal a ha v ⟨hav, hv⟩ w haw).2 hvw
  · rintro ⟨hE, hmin, hs, ht⟩
    refine ⟨⟨by omega, hmin⟩, ?_⟩
    rintro a ha v ⟨hav, hv⟩ c hac
    exact ⟨fun hvc => hs hav hac hvc ha hv, fun hvc => ht hav ha hv hac hvc⟩

private def representative : Fin 9 → BitVec 15 :=
  ![4060, 7132, 13242, 14200, 14234, 14236, 15772, 28735, 30552]

/-- Representatives with cubic root 0 and neighbors 1, 2, 3. -/
def rootedTemplate (k : Fin 9) : SimpleGraph (Fin 7) :=
  graphOfWord (representative k)

instance (k : Fin 9) : DecidableRel (rootedTemplate k).Adj :=
  inferInstanceAs (DecidableRel (graphOfWord (representative k)).Adj)

/-- The distinguished vertex of every rooted template has degree three. -/
theorem rootedTemplate_degree_zero (k : Fin 9) : (rootedTemplate k).degree 0 = 3 := by
  have hNear : ∀ j : Fin 7, Near j ↔ j = 1 ∨ j = 2 ∨ j = 3 := by decide +kernel
  have hN : (rootedTemplate k).neighborFinset 0 = {1, 2, 3} := by
    ext j
    simp only [SimpleGraph.mem_neighborFinset, mem_insert, mem_singleton]
    exact (root_row _ j).trans (hNear j)
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hN] <;> decide +kernel

private def nearPerm (a : Fin 6) : Fin 3 → Fin 7 :=
  ![![1, 2, 3], ![1, 3, 2], ![2, 1, 3], ![2, 3, 1], ![3, 1, 2], ![3, 2, 1]] a

private def farPerm (b : Fin 6) : Fin 3 → Fin 7 :=
  ![![4, 5, 6], ![4, 6, 5], ![5, 4, 6], ![5, 6, 4], ![6, 4, 5], ![6, 5, 4]] b

private def stabilizer (a b : Fin 6) : Fin 7 → Fin 7 :=
  ![0, nearPerm a 0, nearPerm a 1, nearPerm a 2, farPerm b 0, farPerm b 1, farPerm b 2]

private abbrev FixesRoot (f : Fin 7 → Fin 7) : Prop :=
  f 0 = 0 ∧ ∀ i, Near i ↔ Near (f i)

private theorem stabilizer_spec (a : Fin 6) :
    ∀ b : Fin 6, Function.Bijective (stabilizer a b) ∧ FixesRoot (stabilizer a b) := by
  fin_cases a <;> decide +kernel

private def orbitWord (k : Fin 9) (a b : Fin 6) : BitVec 15 :=
  encode fun i j => adjacency (representative k) (stabilizer a b i) (stabilizer a b j)

-- A row (m,a,b) gives the permutation from labels of m to labels of the representative.
private def orbitTable : Fin 9 → List (BitVec 15 × Fin 6 × Fin 6) :=
  ![[(4060, 0, 0)],
    [(7132, 0, 0), (7644, 0, 2), (8028, 1, 0), (8092, 1, 2),
      (8148, 4, 0), (8152, 4, 2), (10204, 0, 1), (11740, 0, 3),
      (11996, 1, 1), (12188, 1, 3), (12236, 4, 1), (12248, 4, 3),
      (18396, 0, 4), (19420, 0, 5), (20188, 1, 4), (20316, 1, 5),
      (20428, 4, 4), (20436, 4, 5)],
    [(13242, 0, 0), (15481, 1, 0), (15751, 4, 0), (21878, 0, 2),
      (23221, 1, 2), (23371, 4, 2), (26323, 4, 3), (26413, 1, 3),
      (26862, 0, 3)],
    [(14200, 0, 0), (14230, 2, 0), (15096, 0, 1), (15246, 2, 1),
      (15573, 3, 0), (15693, 3, 1), (22362, 2, 2), (22452, 0, 2),
      (23257, 3, 2), (23437, 3, 4), (23796, 0, 4), (23886, 2, 4),
      (26457, 3, 3), (26517, 3, 5), (27354, 2, 3), (27564, 0, 3),
      (27862, 2, 5), (28012, 0, 5)],
    [(14234, 0, 0), (14264, 2, 0), (15258, 0, 1), (15288, 2, 1),
      (15577, 1, 0), (15608, 3, 0), (15705, 1, 1), (15736, 3, 1),
      (15757, 4, 0), (15758, 5, 0), (15765, 4, 1), (15766, 5, 1),
      (22358, 0, 2), (22388, 2, 2), (23253, 1, 2), (23284, 3, 2),
      (23373, 4, 2), (23374, 5, 2), (23385, 4, 4), (23386, 5, 4),
      (23445, 1, 4), (23476, 3, 4), (23894, 0, 4), (23924, 2, 4),
      (26325, 4, 3), (26326, 5, 3), (26329, 4, 5), (26330, 5, 5),
      (26445, 1, 3), (26476, 3, 3), (26509, 1, 5), (26540, 3, 5),
      (27342, 0, 3), (27372, 2, 3), (27854, 0, 5), (27884, 2, 5)],
    [(14236, 0, 0), (14296, 2, 0), (15260, 0, 1), (15320, 2, 1),
      (15580, 1, 0), (15708, 1, 1), (15820, 4, 0), (15828, 4, 1),
      (16088, 3, 0), (16216, 3, 1), (16268, 5, 0), (16276, 5, 1),
      (22364, 0, 2), (22484, 2, 2), (23260, 1, 2), (23452, 1, 4),
      (23500, 4, 2), (23512, 4, 4), (23900, 0, 4), (24020, 2, 4),
      (24276, 3, 2), (24396, 5, 2), (24408, 5, 4), (24468, 3, 4),
      (26460, 1, 3), (26524, 1, 5), (26580, 4, 3), (26584, 4, 5),
      (27356, 0, 3), (27596, 2, 3), (27868, 0, 5), (28108, 2, 5),
      (28372, 5, 3), (28376, 5, 5), (28492, 3, 3), (28556, 3, 5)],
    [(15772, 0, 0), (15832, 2, 0), (16280, 3, 0), (23388, 0, 2),
      (23508, 2, 2), (24404, 3, 2), (26332, 0, 3), (26572, 2, 3),
      (28364, 3, 3)],
    [(28735, 0, 0), (29155, 2, 0), (32291, 3, 0)],
    [(30552, 0, 0), (30612, 0, 2), (31448, 0, 1), (31628, 0, 3),
      (31956, 0, 4), (32076, 0, 5)]]

set_option maxRecDepth 4096 in
private theorem orbitTable_spec (k : Fin 9) :
    (orbitTable k).all (fun r => decide (orbitWord k r.2.1 r.2.2 = r.1)) = true := by
  fin_cases k <;> decide +kernel

private def listed (m : BitVec 15) : Bool :=
  (List.finRange 9).any fun k => (orbitTable k).any fun row => decide (row.1 = m)

private def chunkWord (hi : Fin 128) (lo : Fin 256) : BitVec 15 :=
  BitVec.ofNat 15 (256 * hi.val + lo.val)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1200000 in
-- Each closed check ranges over one block of 256 codes. The nine-edge test
-- precedes the degree and common-neighbor tests.
private theorem check_chunk (hi : Fin 128) :
    (List.finRange 256).all
      (fun lo => !admissible (chunkWord hi lo) || listed (chunkWord hi lo)) = true := by
  fin_cases hi <;> decide +kernel

private theorem find_orbit (m : BitVec 15) (hm : admissible m = true) :
    ∃ (k : Fin 9) (a b : Fin 6), orbitWord k a b = m := by
  have hmSmall : m.toNat < 32768 := m.isLt
  let hi : Fin 128 := ⟨m.toNat / 256, by omega⟩
  let lo : Fin 256 := ⟨m.toNat % 256, Nat.mod_lt _ (by decide)⟩
  have hword : chunkWord hi lo = m := by
    apply BitVec.eq_of_toNat_eq
    change (256 * (m.toNat / 256) + m.toNat % 256) % 32768 = m.toNat
    rw [show 256 * (m.toNat / 256) + m.toNat % 256 = m.toNat by omega,
      Nat.mod_eq_of_lt hmSmall]
  have h := List.all_eq_true.mp (check_chunk hi) lo (List.mem_finRange lo)
  have hl : listed m = true := by simpa [hword, hm] using h
  unfold listed at hl
  obtain ⟨k, _, hk⟩ := List.any_eq_true.mp hl
  obtain ⟨r, hr, heq⟩ := List.any_eq_true.mp hk
  have hrow := List.all_eq_true.mp (orbitTable_spec k) r hr
  exact ⟨k, r.2.1, r.2.2, (of_decide_eq_true hrow).trans (of_decide_eq_true heq)⟩

private theorem orbitIso (k : Fin 9) (a b : Fin 6) :
    ∃ e : graphOfWord (orbitWord k a b) ≃g rootedTemplate k, e 0 = 0 := by
  obtain ⟨hbij, hfix⟩ := stabilizer_spec a b
  let p := Equiv.ofBijective (stabilizer a b) hbij
  let K := (rootedTemplate k).comap p
  have hp0 : p 0 = 0 := hfix.1
  have hroot (j : Fin 7) : K.Adj 0 j ↔ Near j := by
    change (rootedTemplate k).Adj (p 0) (p j) ↔ Near j
    rw [hp0]
    exact (root_row _ _).trans (hfix.2 j).symm
  have hw : encode (fun i j => decide (K.Adj i j)) = orbitWord k a b := by
    apply congrArg encode
    funext i j
    change decide (adjacency (representative k) (stabilizer a b i) (stabilizer a b j) = true) = _
    simp
  have heq := decode K hroot
  rw [hw] at heq
  refine ⟨{ toEquiv := p, map_rel_iff' := ?_ }, hp0⟩
  intro i j
  change K.Adj i j ↔ (graphOfWord (orbitWord k a b)).Adj i j
  rw [heq]

private theorem nearPerm_complete :
    ∀ i j k : Fin 7, Near i → Near j → Near k → i ≠ j → i ≠ k → j ≠ k →
      ∃ a : Fin 6, i = nearPerm a 0 ∧ j = nearPerm a 1 ∧ k = nearPerm a 2 := by
  decide +kernel

private theorem farPerm_complete :
    ∀ i j k : Fin 7, i ≠ 0 → j ≠ 0 → k ≠ 0 → ¬ Near i → ¬ Near j → ¬ Near k →
      i ≠ j → i ≠ k → j ≠ k →
      ∃ b : Fin 6, i = farPerm b 0 ∧ j = farPerm b 1 ∧ k = farPerm b 2 := by
  decide +kernel

private theorem stabilizer_complete (p : Fin 7 → Fin 7) (hinj : Function.Injective p)
    (h : FixesRoot p) : ∃ a b, p = stabilizer a b := by
  obtain ⟨a, h1, h2, h3⟩ := nearPerm_complete (p 1) (p 2) (p 3)
    ((h.2 1).mp (by decide)) ((h.2 2).mp (by decide)) ((h.2 3).mp (by decide))
    (hinj.ne (by decide)) (hinj.ne (by decide)) (hinj.ne (by decide))
  have hn0 (j : Fin 7) (hj : j ≠ 0) : p j ≠ 0 := by
    rw [← h.1]
    exact hinj.ne hj
  obtain ⟨b, h4, h5, h6⟩ := farPerm_complete (p 4) (p 5) (p 6)
    (hn0 4 (by decide)) (hn0 5 (by decide)) (hn0 6 (by decide))
    (fun hn => (by decide : ¬ Near 4) ((h.2 4).mpr hn))
    (fun hn => (by decide : ¬ Near 5) ((h.2 5).mpr hn))
    (fun hn => (by decide : ¬ Near 6) ((h.2 6).mpr hn))
    (hinj.ne (by decide)) (hinj.ne (by decide)) (hinj.ne (by decide))
  refine ⟨a, b, ?_⟩
  funext t
  fin_cases t
  · exact h.1
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem representatives_separate (k : Fin 9) :
    ∀ (a b : Fin 6) (j : Fin 9), orbitWord k a b = representative j → j = k := by
  fin_cases k <;> decide +kernel

/-- A root-preserving isomorphism between two representatives identifies their indices. -/
theorem rootedTemplate_index_eq {i j : Fin 9} (e : rootedTemplate i ≃g rootedTemplate j)
    (he : e 0 = 0) : i = j := by
  have hfix : FixesRoot e := ⟨he, fun k => by
    have hadj : (rootedTemplate j).Adj (e 0) (e k) ↔ (rootedTemplate i).Adj 0 k :=
      e.map_adj_iff
    rw [he] at hadj
    exact (root_row _ _).symm.trans (hadj.symm.trans (root_row _ _))⟩
  obtain ⟨a, b, hp⟩ := stabilizer_complete e e.injective hfix
  have hword : orbitWord j a b = representative i := by
    rw [← encode_adjacency (representative i)]
    apply congrArg encode
    funext x y
    apply Bool.eq_iff_iff.mpr
    change adjacency (representative j) (stabilizer a b x) (stabilizer a b y) = true ↔
      adjacency (representative i) x y = true
    rw [← hp]
    exact e.map_adj_iff
  exact representatives_separate j a b i hword

/-- Every rooted representative satisfies all three laws and has twelve edges. -/
theorem rootedTemplate_spec (k : Fin 9) :
    (rootedTemplate k).edgeFinset.card = 12 ∧ (∀ a, 3 ≤ (rootedTemplate k).degree a) ∧
      SquareCompletion (rootedTemplate k) ∧ SecondCommonNeighbor (rootedTemplate k) := by
  apply (admissible_iff (representative k)).mp
  fin_cases k <;> decide +kernel

/-- The five contact shapes. Index 0 is K₃,₄ with shores {0,3,6} and {1,2,4,5}.
Index 4 is two copies of K₄ meeting at the universal vertex 0. -/
def templatePairs : Fin 5 → Finset (Fin 7 × Fin 7) :=
  ![{(0, 1), (0, 2), (0, 4), (0, 5), (1, 3), (1, 6), (2, 3), (2, 6),
      (3, 4), (3, 5), (4, 6), (5, 6)},
    {(0, 1), (0, 2), (0, 3), (1, 4), (1, 5), (1, 6), (2, 4), (2, 5),
      (2, 6), (3, 4), (3, 6), (4, 5)},
    {(0, 1), (0, 2), (0, 3), (1, 5), (1, 6), (2, 3), (2, 4), (2, 6),
      (3, 4), (3, 5), (4, 5), (4, 6)},
    {(0, 1), (0, 2), (0, 3), (1, 3), (1, 5), (1, 6), (2, 5), (2, 6),
      (3, 4), (3, 5), (4, 5), (4, 6)},
    {(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 2), (1, 3),
      (2, 3), (4, 5), (4, 6), (5, 6)}]

def contactTemplate (kind : Fin 5) : SimpleGraph (Fin 7) :=
  SimpleGraph.fromRel fun i j => (i, j) ∈ templatePairs kind

instance (kind : Fin 5) : DecidableRel (contactTemplate kind).Adj :=
  fun i j => inferInstanceAs (Decidable
    (i ≠ j ∧ ((i, j) ∈ templatePairs kind ∨ (j, i) ∈ templatePairs kind)))

/-- Map from a rooted orbit to its unrooted template. -/
def templateIndex : Fin 9 → Fin 5 := ![0, 1, 1, 2, 3, 3, 1, 4, 2]

-- Each row maps the unrooted template labels to the rooted representative labels.
private def unrootedWitness : Fin 9 → Fin 7 → Fin 7 :=
  ![![1, 0, 4, 2, 5, 6, 3], ![0, 1, 2, 3, 4, 5, 6], ![5, 1, 2, 4, 3, 0, 6],
    ![0, 1, 2, 3, 4, 5, 6], ![0, 1, 2, 3, 4, 5, 6], ![6, 1, 2, 4, 3, 5, 0],
    ![3, 6, 5, 0, 1, 4, 2], ![1, 0, 2, 3, 4, 5, 6], ![1, 0, 5, 6, 4, 2, 3]]

private theorem unrootedWitness_spec (k : Fin 9) :
    Function.Bijective (unrootedWitness k) ∧
      ∀ i j, (rootedTemplate k).Adj (unrootedWitness k i) (unrootedWitness k j) ↔
        (contactTemplate (templateIndex k)).Adj i j := by
  fin_cases k <;> decide +kernel

/-- The explicit relabeling from each unrooted contact template to its rooted representative. -/
noncomputable def unrootedIso (k : Fin 9) :
    contactTemplate (templateIndex k) ≃g rootedTemplate k where
  toEquiv := Equiv.ofBijective (unrootedWitness k) (unrootedWitness_spec k).1
  map_rel_iff' := fun {i j} => (unrootedWitness_spec k).2 i j

private theorem second_of_iso {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {T : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel T.Adj]
    (e : T ≃g G) (h : SecondCommonNeighbor G) : SecondCommonNeighbor T := by
  intro x y w hxy hx hy hxw hyw
  obtain ⟨z, hzw, hxz, hyz⟩ := h (e.map_adj_iff.mpr hxy)
    ((e.degree_eq x).trans hx) ((e.degree_eq y).trans hy)
    (e.map_adj_iff.mpr hxw) (e.map_adj_iff.mpr hyw)
  refine ⟨e.symm z, ?_, e.map_adj_iff.mp ?_, e.map_adj_iff.mp ?_⟩
  · intro hz
    exact hzw (by simpa using congrArg e hz)
  · simpa using hxz
  · simpa using hyz

/-- Each of the five unrooted shapes satisfies the hypotheses of the classification. -/
theorem contactTemplate_spec (kind : Fin 5) :
    (contactTemplate kind).edgeFinset.card = 12 ∧ (∀ a, 3 ≤ (contactTemplate kind).degree a) ∧
      SquareCompletion (contactTemplate kind) ∧ SecondCommonNeighbor (contactTemplate kind) := by
  have hsurj : Function.Surjective templateIndex := by decide +kernel
  obtain ⟨k, rfl⟩ := hsurj kind
  obtain ⟨hE, hmin, hs, ht⟩ := rootedTemplate_spec k
  let e := unrootedIso k
  exact ⟨e.card_edgeFinset_eq.trans hE, fun a => (e.degree_eq a) ▸ hmin (e a),
    square_of_iso e hs, second_of_iso e ht⟩

variable {V : Type u} [Fintype V]

-- The label extension from Q9TenMaskGraph, with the target size generalized.
private theorem extend_labels {n : ℕ} (hV : Fintype.card V = n)
    (labels : List V) (hdistinct : labels.Nodup) (hlen : labels.length ≤ n) :
    ∃ e : Fin n ≃ V, ∀ k : Fin labels.length, e (Fin.castLE hlen k) = labels.get k := by
  classical
  let s : Finset (Fin n) := univ.filter fun i => i.val < labels.length
  let f (i : Fin n) : V :=
    if hi : i.val < labels.length then labels.get ⟨i.val, hi⟩
    else (Fintype.equivFinOfCardEq hV).symm i
  have hcard : Fintype.card (Fin n) = (univ : Finset V).card := by
    rw [Fintype.card_fin, card_univ, hV]
  have hinj : Set.InjOn f (s : Set (Fin n)) := by
    intro i hi j hj hij
    have hi' : i.val < labels.length := (mem_filter.mp (show i ∈ s from hi)).2
    have hj' : j.val < labels.length := (mem_filter.mp (show j ∈ s from hj)).2
    have hget : labels.get ⟨i.val, hi'⟩ = labels.get ⟨j.val, hj'⟩ := by
      simpa only [f, dif_pos hi', dif_pos hj'] using hij
    exact Fin.ext (congrArg (fun k : Fin labels.length => k.val) (hdistinct.injective_get hget))
  obtain ⟨g, hg⟩ := Finset.exists_equiv_extend_of_card_eq hcard
    (s := s) (f := f) (subset_univ _) hinj
  refine ⟨g.trans (Equiv.subtypeUnivEquiv Finset.mem_univ), ?_⟩
  intro k
  have hk : (Fin.castLE hlen k).val < labels.length := k.isLt
  change (g (Fin.castLE hlen k) : V) = labels.get k
  calc
    _ = f (Fin.castLE hlen k) := hg _ (mem_filter.mpr ⟨mem_univ _, hk⟩)
    _ = labels.get k := dif_pos hk

private theorem normalize_root (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = 7) (r : V) (hr : G.degree r = 3) :
    ∃ e : Fin 7 ≃ V, e 0 = r ∧ ∀ j, G.Adj (e 0) (e j) ↔ Near j := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, hN⟩ :=
    card_eq_three.mp ((G.card_neighborFinset_eq_degree r).trans hr)
  have ha : G.Adj r a := (G.mem_neighborFinset r a).mp (by simp [hN])
  have hb : G.Adj r b := (G.mem_neighborFinset r b).mp (by simp [hN])
  have hc : G.Adj r c := (G.mem_neighborFinset r c).mp (by simp [hN])
  obtain ⟨e, he⟩ := extend_labels hV [r, a, b, c]
    (by simp [List.nodup_cons, ha.ne, hb.ne, hc.ne, hab, hac, hbc]) (by simp)
  have he0 : e 0 = r := he 0
  have he1 : e 1 = a := he 1
  have he2 : e 2 = b := he 2
  have he3 : e 3 = c := he 3
  have hNear : ∀ j : Fin 7, (j = 1 ∨ j = 2 ∨ j = 3) ↔ Near j := by decide +kernel
  refine ⟨e, he0, fun j => ?_⟩
  rw [he0, ← G.mem_neighborFinset r (e j), hN]
  simp only [mem_insert, mem_singleton, ← he1, ← he2, ← he3, e.apply_eq_iff_eq]
  exact hNear j

/-- With any specified cubic root, exactly one of the nine rooted templates applies. -/
theorem rooted_twelve_edges_on_seven_vertices (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = 7) (hE : G.edgeFinset.card = 12)
    (hmin : ∀ a, 3 ≤ G.degree a) (hs : SquareCompletion G) (ht : SecondCommonNeighbor G)
    (r : V) (hr : G.degree r = 3) :
    ∃! k : Fin 9, ∃ e : rootedTemplate k ≃g G, e 0 = r := by
  obtain ⟨label, hlabel, hroot⟩ := normalize_root G hV r hr
  let K := G.comap label
  let m := encode fun i j => decide (K.Adj i j)
  have hdecoded : graphOfWord m = K := decode K hroot
  let e : graphOfWord m ≃g G :=
    { toEquiv := label
      map_rel_iff' := by
        intro i j
        change K.Adj i j ↔ (graphOfWord m).Adj i j
        rw [hdecoded] }
  have hsq : SquareCompletion (graphOfWord m) := by
    classical
    exact square_of_iso e hs
  have hm : admissible m = true := (admissible_iff m).mpr
    ⟨e.card_edgeFinset_eq.trans hE, fun a => (e.degree_eq a) ▸ hmin (e a),
      hsq, second_of_iso e ht⟩
  obtain ⟨k, a, b, hw⟩ := find_orbit m hm
  have hIso := orbitIso k a b
  rw [hw] at hIso
  obtain ⟨f, hf⟩ := hIso
  have hf' : f.symm 0 = 0 := f.injective (by simpa using hf.symm)
  let rootedIso : rootedTemplate k ≃g G := RelIso.trans f.symm e
  have hrooted : rootedIso 0 = r := by
    change label (f.symm 0) = r
    rw [hf', hlabel]
  refine ⟨k, ⟨rootedIso, hrooted⟩, ?_⟩
  rintro j ⟨g, hg⟩
  apply rootedTemplate_index_eq (RelIso.trans g rootedIso.symm)
  change rootedIso.symm (g 0) = 0
  rw [hg, ← hrooted, RelIso.symm_apply_apply]

/-- A seven-vertex twelve-edge graph satisfying the three laws belongs to one
of the five unrooted isomorphism classes. -/
theorem twelve_edges_on_seven_vertices (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = 7) (hE : G.edgeFinset.card = 12)
    (hmin : ∀ a, 3 ≤ G.degree a) (hs : SquareCompletion G) (ht : SecondCommonNeighbor G) :
    ∃ kind : Fin 5, Nonempty (contactTemplate kind ≃g G) := by
  have hroot : ∃ r, G.degree r = 3 := by
    by_contra! h
    have hsum : (∑ a : V, 4) ≤ ∑ a, G.degree a :=
      sum_le_sum fun a _ => by
        have ha := hmin a
        have hne := h a
        omega
    rw [G.sum_degrees_eq_twice_card_edges, hE, sum_const, card_univ, hV, nsmul_eq_mul] at hsum
    omega
  obtain ⟨r, hr⟩ := hroot
  obtain ⟨k, ⟨e, _⟩, _⟩ := rooted_twelve_edges_on_seven_vertices G hV hE hmin hs ht r hr
  let phi := RelIso.trans (unrootedIso k) e
  exact ⟨templateIndex k, ⟨phi⟩⟩

open Q9SquareMaskGraph (activeAxes maskGraph card_edges distance_two_mask_graph_constraints)
open Q9ContactGraphTriangles (cubic_edge_common_neighbor_has_companion)
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open Q9MinimumDistanceOperator (minimumDisplacements)
open Q9WeightedSaturation (defect signedBiadjacency)
open private mem_minimumDisplacements from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator

open Classical in
/-- The seven-axis contact graph of a separated balanced cubic pair has one of the five
templates when it has twelve distance-two masks. -/
theorem distance_two_twelve_masks_on_seven_axes
    {C D : Finset (Q 9)} {b : Bool}
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcC : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hdetC : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w C false)).det = 0)
    (hdetD : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w D false)).det = 0)
    (haxes : (activeAxes (minimumDisplacements C D b 2)).card = 7)
    (hmask : (minimumDisplacements C D b 2).card = 12) :
    let F := minimumDisplacements C D b 2
    ∃ kind : Fin 5, Nonempty (contactTemplate kind ≃g maskGraph F) := by
  let F := minimumDisplacements C D b 2
  have hsize (T : Finset (Fin 9)) (hT : T ∈ F) : T.card = 2 := by
    obtain ⟨x, _, y, _, _, hd, rfl⟩ := mem_minimumDisplacements.mp hT
    exact hd
  have hV : Fintype.card (activeAxes F) = 7 := (Fintype.card_coe _).trans haxes
  have hE : (maskGraph F).edgeFinset.card = 12 := (card_edges F hsize).trans hmask
  obtain ⟨hmin, hs⟩ := distance_two_mask_graph_constraints (b := b)
    hsep hrC hrD hcC hcD hbC hbD hdetC hdetD
  have ht : SecondCommonNeighbor (maskGraph F) := by
    intro x y w hxy hx hy hxw hyw
    exact cubic_edge_common_neighbor_has_companion (b := b) hsep hrC hrD hcC hcD hbC hbD
      hdetC hdetD (i := x) (j := y) (d := w) hxy hx hy hxw hyw
  have hs' : SquareCompletion (maskGraph F) := by
    intro a v c
    exact hs
  exact twelve_edges_on_seven_vertices (maskGraph F) hV hE hmin hs' ht

end Q9TwelveMaskSevenAxisShapes
end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement
