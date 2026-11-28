import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TwelveMaskSevenAxisShapes

/-!
# Thirteen contact edges on seven axes

A cubic root has three neighbors and three nonneighbors. The same
coordinate stabilizer used for twelve masks acts on the ten nonroot
edges. The four local graph laws reduce the admissible words to twelve
unrooted templates.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement
namespace Q9ThirteenMaskSevenAxisShapes

open Finset
open scoped BigOperators
open Q9TenMaskGraph (SquareCompletion)
open Q9TwelveMaskSevenAxisShapes (SecondCommonNeighbor)
open private graphOfWord adjacency degreeOfWord degreeOfWord_eq hasOtherCommonNeighbor
  encode decode root_row Near selected card_graphOfWord count_finRange_eq_card guard_eq_true
  stabilizer stabilizer_spec chunkWord normalize_root second_of_iso from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TwelveMaskSevenAxisShapes
open private square_of_iso from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TenMaskGraph

universe u v

/-- A triangle cannot have three degree-three vertices. -/
abbrev CubicTriangleFree {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ ⦃a b c : V⦄, G.Adj a b → G.Adj b c → G.Adj c a →
    G.degree a = 3 → G.degree b = 3 → G.degree c = 3 → False

/-- Each edge belongs to a four-cycle of distinct vertices. -/
abbrev EveryEdgeSquare {V : Type u} (G : SimpleGraph V) : Prop :=
  ∀ ⦃a b : V⦄, G.Adj a b → ∃ c d, c ≠ b ∧ d ≠ a ∧
    G.Adj a c ∧ G.Adj c d ∧ G.Adj d b

private def admissible (m : BitVec 15) : Bool :=
  let G := graphOfWord m
  decide ((List.finRange 15).countP (fun k => m.getLsb k) = 10) &&
    (List.finRange 7).all (fun a => decide (3 ≤ degreeOfWord m a)) &&
    (List.finRange 7).all (fun a =>
      if degreeOfWord m a = 3 then
        (List.finRange 7).all fun b =>
          if G.Adj a b ∧ degreeOfWord m b = 3 then
            (List.finRange 7).all fun c =>
              if G.Adj a c then
                (if b ≠ c then hasOtherCommonNeighbor m b c a else true) &&
                  (if G.Adj b c then
                    hasOtherCommonNeighbor m a b c && decide (degreeOfWord m c ≠ 3)
                   else true)
              else true
          else true
      else true) &&
    (List.finRange 7).all (fun a => (List.finRange 7).all fun b =>
      if G.Adj a b then
        (List.finRange 7).any (fun c => (List.finRange 7).any fun d =>
          decide (c ≠ b ∧ d ≠ a ∧ G.Adj a c ∧ G.Adj c d ∧ G.Adj d b))
      else true)

private theorem admissible_iff (m : BitVec 15) :
    admissible m = true ↔
      (graphOfWord m).edgeFinset.card = 13 ∧ (∀ a, 3 ≤ (graphOfWord m).degree a) ∧
      SquareCompletion (graphOfWord m) ∧ SecondCommonNeighbor (graphOfWord m) ∧
      CubicTriangleFree (graphOfWord m) ∧ EveryEdgeSquare (graphOfWord m) := by
  have hcount : (List.finRange 15).countP (fun k => m.getLsb k) = (selected m).card :=
    count_finRange_eq_card _
  simp only [admissible, hasOtherCommonNeighbor, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.any_eq_true, List.mem_finRange, true_and, true_implies,
    guard_eq_true]
  simp only [hcount, degreeOfWord_eq, card_graphOfWord]
  constructor
  · rintro ⟨⟨⟨hE, hmin⟩, hlocal⟩, hsq⟩
    refine ⟨by omega, hmin, ?_, ?_, ?_, ?_⟩
    · intro a b c hab hac hbc ha hb
      exact (hlocal a ha b ⟨hab, hb⟩ c hac).1 hbc
    · intro a b c hab ha hb hac hbc
      exact ((hlocal a ha b ⟨hab, hb⟩ c hac).2 hbc).1
    · intro a b c hab hbc hca ha hb hc
      exact ((hlocal a ha b ⟨hab, hb⟩ c hca.symm).2 hbc).2 hc
    · intro a b hab
      exact hsq a b hab
  · rintro ⟨hE, hmin, hsq, ht, htri, hevery⟩
    refine ⟨⟨⟨by omega, hmin⟩, ?_⟩, ?_⟩
    · rintro a ha b ⟨hab, hb⟩ c hac
      exact ⟨fun hbc => hsq hab hac hbc ha hb,
        fun hbc => ⟨ht hab ha hb hac hbc, fun hc => htri hab hbc hac.symm ha hb hc⟩⟩
    · intro a b hab
      exact hevery hab

private def representative : Fin 22 → BitVec 15 := ![7133, 7134, 13243, 13246, 13694, 14171, 14201, 14204, 14235, 14237, 14238, 14266, 14268, 14300, 15773, 15836, 28799, 29434, 30421, 30428, 30553, 30556]

/-- The rooted orbit representatives under permutations preserving the root neighborhood. -/
def rootedTemplate (k : Fin 22) : SimpleGraph (Fin 7) := graphOfWord (representative k)

instance (k : Fin 22) : DecidableRel (rootedTemplate k).Adj :=
  inferInstanceAs (DecidableRel (graphOfWord (representative k)).Adj)

private def orbitWord (k : Fin 22) (a b : Fin 6) : BitVec 15 :=
  encode fun i j => adjacency (representative k) (stabilizer a b i) (stabilizer a b j)

private def orbitTable : Fin 22 → List (BitVec 15 × Fin 6 × Fin 6) :=
  ![[(7133, 0, 0), (7645, 0, 2), (8030, 1, 0), (8094, 1, 2), (8180, 4, 0), (8184, 4, 2), (10205, 0, 1), (11741, 0, 3), (11998, 1, 1), (12190, 1, 3), (12268, 4, 1), (12280, 4, 3), (18397, 0, 4), (19421, 0, 5), (20190, 1, 4), (20318, 1, 5), (20460, 4, 4), (20468, 4, 5)],
    [(7134, 0, 0), (7164, 2, 0), (7646, 0, 2), (7676, 2, 2), (8029, 1, 0), (8060, 3, 0), (8093, 1, 2), (8124, 3, 2), (8149, 4, 0), (8150, 5, 0), (8153, 4, 2), (8154, 5, 2), (10206, 0, 1), (10236, 2, 1), (11742, 0, 3), (11772, 2, 3), (11997, 1, 1), (12028, 3, 1), (12189, 1, 3), (12220, 3, 3), (12237, 4, 1), (12238, 5, 1), (12249, 4, 3), (12250, 5, 3), (18398, 0, 4), (18428, 2, 4), (19422, 0, 5), (19452, 2, 5), (20189, 1, 4), (20220, 3, 4), (20317, 1, 5), (20348, 3, 5), (20429, 4, 4), (20430, 5, 4), (20437, 4, 5), (20438, 5, 5)],
    [(13243, 0, 0), (15483, 1, 0), (15783, 4, 0), (21879, 0, 2), (23223, 1, 2), (23403, 4, 2), (26355, 4, 3), (26415, 1, 3), (26863, 0, 3)],
    [(13246, 0, 0), (13306, 2, 0), (15485, 1, 0), (15815, 4, 0), (15993, 3, 0), (16263, 5, 0), (21886, 0, 2), (22006, 2, 2), (23229, 1, 2), (23499, 4, 2), (24245, 3, 2), (24395, 5, 2), (26429, 1, 3), (26579, 4, 3), (26878, 0, 3), (27118, 2, 3), (28371, 5, 3), (28461, 3, 3)],
    [(13694, 0, 0), (13814, 2, 0), (14141, 1, 1), (14291, 4, 1), (14590, 0, 1), (14830, 2, 1), (15037, 1, 0), (15307, 4, 0), (16053, 3, 0), (16083, 5, 1), (16173, 3, 1), (16203, 5, 0), (21438, 0, 2), (21498, 2, 2), (22333, 1, 4), (22483, 4, 4), (22782, 0, 4), (23022, 2, 4), (23677, 1, 2), (24007, 4, 2), (24185, 3, 2), (24275, 5, 4), (24365, 3, 4), (24455, 5, 2), (25534, 0, 3), (25594, 2, 3), (25982, 0, 5), (26102, 2, 5), (27325, 1, 5), (27595, 4, 5), (27773, 1, 3), (28103, 4, 3), (28281, 3, 3), (28341, 3, 5), (28491, 5, 5), (28551, 5, 3)],
    [(14171, 0, 0), (14261, 2, 0), (15067, 0, 1), (15277, 2, 1), (15606, 3, 0), (15726, 3, 1), (22393, 2, 2), (22423, 0, 2), (23290, 3, 2), (23470, 3, 4), (23767, 0, 4), (23917, 2, 4), (26490, 3, 3), (26550, 3, 5), (27385, 2, 3), (27535, 0, 3), (27893, 2, 5), (27983, 0, 5)],
    [(14201, 0, 0), (14202, 1, 1), (14231, 2, 0), (14262, 4, 1), (15097, 0, 1), (15098, 1, 0), (15247, 2, 1), (15278, 4, 0), (15575, 3, 0), (15605, 5, 1), (15695, 3, 1), (15725, 5, 0), (22363, 2, 2), (22394, 4, 4), (22453, 0, 2), (22454, 1, 4), (23259, 3, 2), (23289, 5, 4), (23439, 3, 4), (23469, 5, 2), (23797, 0, 4), (23798, 1, 2), (23887, 2, 4), (23918, 4, 2), (26459, 3, 3), (26489, 5, 5), (26519, 3, 5), (26549, 5, 3), (27355, 2, 3), (27386, 4, 5), (27565, 0, 3), (27566, 1, 5), (27863, 2, 5), (27894, 4, 3), (28013, 0, 5), (28014, 1, 3)],
    [(14204, 0, 0), (14294, 2, 0), (15100, 0, 1), (15310, 2, 1), (16085, 3, 0), (16205, 3, 1), (22460, 0, 2), (22490, 2, 2), (23804, 0, 4), (24014, 2, 4), (24281, 3, 2), (24461, 3, 4), (27580, 0, 3), (27610, 2, 3), (28028, 0, 5), (28118, 2, 5), (28505, 3, 3), (28565, 3, 5)],
    [(14235, 0, 0), (14265, 2, 0), (15259, 0, 1), (15289, 2, 1), (15579, 1, 0), (15610, 3, 0), (15707, 1, 1), (15738, 3, 1), (15789, 4, 0), (15790, 5, 0), (15797, 4, 1), (15798, 5, 1), (22359, 0, 2), (22389, 2, 2), (23255, 1, 2), (23286, 3, 2), (23405, 4, 2), (23406, 5, 2), (23417, 4, 4), (23418, 5, 4), (23447, 1, 4), (23478, 3, 4), (23895, 0, 4), (23925, 2, 4), (26357, 4, 3), (26358, 5, 3), (26361, 4, 5), (26362, 5, 5), (26447, 1, 3), (26478, 3, 3), (26511, 1, 5), (26542, 3, 5), (27343, 0, 3), (27373, 2, 3), (27855, 0, 5), (27885, 2, 5)],
    [(14237, 0, 0), (14297, 2, 0), (15261, 0, 1), (15321, 2, 1), (15582, 1, 0), (15710, 1, 1), (15852, 4, 0), (15860, 4, 1), (16090, 3, 0), (16218, 3, 1), (16300, 5, 0), (16308, 5, 1), (22365, 0, 2), (22485, 2, 2), (23262, 1, 2), (23454, 1, 4), (23532, 4, 2), (23544, 4, 4), (23901, 0, 4), (24021, 2, 4), (24278, 3, 2), (24428, 5, 2), (24440, 5, 4), (24470, 3, 4), (26462, 1, 3), (26526, 1, 5), (26612, 4, 3), (26616, 4, 5), (27357, 0, 3), (27597, 2, 3), (27869, 0, 5), (28109, 2, 5), (28404, 5, 3), (28408, 5, 5), (28494, 3, 3), (28558, 3, 5)],
    [(14238, 0, 0), (14328, 2, 0), (15262, 0, 1), (15352, 2, 1), (15581, 1, 0), (15709, 1, 1), (15821, 4, 0), (15829, 4, 1), (16120, 3, 0), (16248, 3, 1), (16270, 5, 0), (16278, 5, 1), (22366, 0, 2), (22516, 2, 2), (23261, 1, 2), (23453, 1, 4), (23501, 4, 2), (23513, 4, 4), (23902, 0, 4), (24052, 2, 4), (24308, 3, 2), (24398, 5, 2), (24410, 5, 4), (24500, 3, 4), (26461, 1, 3), (26525, 1, 5), (26581, 4, 3), (26585, 4, 5), (27358, 0, 3), (27628, 2, 3), (27870, 0, 5), (28140, 2, 5), (28374, 5, 3), (28378, 5, 5), (28524, 3, 3), (28588, 3, 5)],
    [(14266, 0, 0), (15290, 0, 1), (15609, 1, 0), (15737, 1, 1), (15759, 4, 0), (15767, 4, 1), (22390, 0, 2), (23285, 1, 2), (23375, 4, 2), (23387, 4, 4), (23477, 1, 4), (23926, 0, 4), (26327, 4, 3), (26331, 4, 5), (26477, 1, 3), (26541, 1, 5), (27374, 0, 3), (27886, 0, 5)],
    [(14268, 0, 0), (14298, 2, 0), (15292, 0, 1), (15322, 2, 1), (15612, 1, 0), (15740, 1, 1), (15822, 4, 0), (15830, 4, 1), (16089, 3, 0), (16217, 3, 1), (16269, 5, 0), (16277, 5, 1), (22396, 0, 2), (22486, 2, 2), (23292, 1, 2), (23484, 1, 4), (23502, 4, 2), (23514, 4, 4), (23932, 0, 4), (24022, 2, 4), (24277, 3, 2), (24397, 5, 2), (24409, 5, 4), (24469, 3, 4), (26492, 1, 3), (26556, 1, 5), (26582, 4, 3), (26586, 4, 5), (27388, 0, 3), (27598, 2, 3), (27900, 0, 5), (28110, 2, 5), (28373, 5, 3), (28377, 5, 5), (28493, 3, 3), (28557, 3, 5)],
    [(14300, 0, 0), (15324, 0, 1), (16092, 1, 0), (16220, 1, 1), (16332, 4, 0), (16340, 4, 1), (22492, 0, 2), (24028, 0, 4), (24284, 1, 2), (24476, 1, 4), (24524, 4, 2), (24536, 4, 4), (27612, 0, 3), (28124, 0, 5), (28508, 1, 3), (28572, 1, 5), (28628, 4, 3), (28632, 4, 5)],
    [(15773, 0, 0), (15774, 1, 0), (15833, 2, 0), (15864, 4, 0), (16282, 3, 0), (16312, 5, 0), (23389, 0, 2), (23390, 1, 2), (23509, 2, 2), (23540, 4, 2), (24406, 3, 2), (24436, 5, 2), (26333, 0, 3), (26334, 1, 3), (26573, 2, 3), (26604, 4, 3), (28366, 3, 3), (28396, 5, 3)],
    [(15836, 0, 0), (16284, 1, 0), (16344, 4, 0), (23516, 0, 2), (24412, 1, 2), (24532, 4, 2), (26588, 0, 3), (28380, 1, 3), (28620, 4, 3)],
    [(28799, 0, 0), (28863, 0, 2), (28991, 0, 3), (29159, 2, 0), (29163, 2, 2), (29171, 2, 3), (29247, 1, 0), (29667, 4, 0), (29759, 1, 2), (30179, 4, 2), (30783, 1, 3), (31203, 4, 3), (32295, 3, 0), (32299, 3, 2), (32307, 3, 3), (32355, 5, 0), (32419, 5, 2), (32547, 5, 3)],
    [(29434, 0, 0), (29562, 0, 1), (29614, 2, 0), (29622, 2, 1), (29942, 0, 2), (30062, 2, 2), (30074, 2, 4), (30134, 0, 4), (30329, 1, 0), (30389, 1, 2), (30517, 3, 3), (30521, 3, 5), (30539, 4, 2), (30547, 5, 3), (30599, 4, 0), (30611, 5, 5), (30966, 2, 3), (30970, 2, 5), (31086, 0, 3), (31150, 0, 5), (31353, 1, 1), (31405, 3, 2), (31417, 3, 4), (31435, 5, 2), (31443, 4, 3), (31533, 1, 3), (31623, 4, 1), (31627, 5, 4), (31853, 3, 0), (31861, 3, 1), (31925, 1, 4), (31943, 5, 0), (31955, 4, 5), (32045, 1, 5), (32071, 5, 1), (32075, 4, 4)],
    [(30421, 0, 0), (30422, 1, 0), (30425, 0, 2), (30426, 1, 2), (30541, 2, 0), (30550, 3, 1), (30572, 4, 0), (30580, 5, 1), (30605, 2, 2), (30618, 3, 4), (30636, 4, 2), (30648, 5, 4), (31438, 3, 0), (31445, 2, 1), (31468, 5, 0), (31476, 4, 1), (31565, 0, 1), (31566, 1, 1), (31577, 0, 3), (31578, 1, 3), (31637, 2, 3), (31642, 3, 5), (31668, 4, 3), (31672, 5, 5), (31950, 3, 2), (31961, 2, 4), (31980, 5, 2), (31992, 4, 4), (32086, 3, 3), (32089, 2, 5), (32116, 5, 3), (32120, 4, 5), (32141, 0, 4), (32142, 1, 4), (32149, 0, 5), (32150, 1, 5)],
    [(30428, 0, 0), (30668, 2, 0), (31580, 0, 1), (31700, 2, 1), (32156, 0, 4), (32216, 2, 4), (32460, 3, 0), (32596, 3, 1), (32664, 3, 4)],
    [(30553, 0, 0), (30554, 1, 1), (30584, 4, 4), (30613, 0, 2), (30614, 1, 4), (30644, 4, 1), (31449, 0, 1), (31450, 1, 0), (31480, 4, 5), (31629, 0, 3), (31630, 1, 5), (31660, 4, 0), (31957, 0, 4), (31958, 1, 2), (31988, 4, 3), (32077, 0, 5), (32078, 1, 3), (32108, 4, 2)],
    [(30556, 0, 0), (30620, 0, 2), (30676, 2, 0), (30680, 2, 2), (31452, 0, 1), (31644, 0, 3), (31692, 2, 1), (31704, 2, 3), (31964, 0, 4), (32092, 0, 5), (32204, 2, 4), (32212, 2, 5), (32468, 3, 0), (32472, 3, 2), (32588, 3, 1), (32600, 3, 3), (32652, 3, 4), (32660, 3, 5)]]

private theorem orbitTable_spec (k : Fin 22) :
    (orbitTable k).all (fun r => decide (orbitWord k r.2.1 r.2.2 = r.1)) = true := by
  fin_cases k <;> decide +kernel

private def listed (m : BitVec 15) : Bool :=
  (List.finRange 22).any fun k => (orbitTable k).any fun row => decide (row.1 = m)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2400000 in
private theorem check_chunk (hi : Fin 128) :
    (List.finRange 256).all
      (fun lo => !admissible (chunkWord hi lo) || listed (chunkWord hi lo)) = true := by
  fin_cases hi <;> decide +kernel

private theorem find_orbit (m : BitVec 15) (hm : admissible m = true) :
    ∃ (k : Fin 22) (a b : Fin 6), orbitWord k a b = m := by
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

private theorem orbitIso (k : Fin 22) (a b : Fin 6) :
    Nonempty (graphOfWord (orbitWord k a b) ≃g rootedTemplate k) := by
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
  refine ⟨{ toEquiv := p, map_rel_iff' := ?_ }⟩
  intro i j
  change K.Adj i j ↔ (graphOfWord (orbitWord k a b)).Adj i j
  rw [heq]

private def unrootedWord : Fin 12 → BitVec 15 := ![7133, 7134, 13694, 14201, 14235, 14238, 14266, 14268, 15836, 28799, 29434, 30553]

/-- The unrooted isomorphism classes satisfying the four local laws. -/
def contactTemplate (kind : Fin 12) : SimpleGraph (Fin 7) := graphOfWord (unrootedWord kind)

instance (k : Fin 12) : DecidableRel (contactTemplate k).Adj :=
  inferInstanceAs (DecidableRel (graphOfWord (unrootedWord k)).Adj)

private def templateIndex : Fin 22 → Fin 12 := ![0, 1, 0, 1, 2, 2, 3, 3, 4, 4, 5, 6, 7, 6, 6, 8, 9, 10, 4, 0, 11, 5]

private def unrootedWitness : Fin 22 → Fin 7 → Fin 7 :=
  ![![0, 1, 2, 3, 4, 5, 6],
    ![0, 1, 2, 3, 4, 5, 6],
    ![5, 1, 2, 4, 3, 0, 6],
    ![5, 1, 2, 4, 3, 0, 6],
    ![0, 1, 2, 3, 4, 5, 6],
    ![6, 1, 4, 2, 3, 0, 5],
    ![0, 1, 2, 3, 4, 5, 6],
    ![6, 1, 4, 2, 3, 0, 5],
    ![0, 1, 2, 3, 4, 5, 6],
    ![6, 1, 2, 4, 3, 5, 0],
    ![0, 1, 2, 3, 4, 5, 6],
    ![0, 1, 2, 3, 4, 5, 6],
    ![0, 1, 2, 3, 4, 5, 6],
    ![6, 1, 2, 4, 3, 5, 0],
    ![4, 5, 6, 1, 0, 2, 3],
    ![0, 1, 2, 3, 4, 5, 6],
    ![0, 1, 2, 3, 4, 5, 6],
    ![0, 1, 2, 3, 4, 5, 6],
    ![6, 4, 5, 1, 0, 2, 3],
    ![2, 4, 5, 0, 1, 6, 3],
    ![0, 1, 2, 3, 4, 5, 6],
    ![2, 4, 0, 6, 5, 1, 3]]

private theorem unrootedWitness_spec (k : Fin 22) :
    Function.Bijective (unrootedWitness k) ∧
      ∀ i j, (rootedTemplate k).Adj (unrootedWitness k i) (unrootedWitness k j) ↔
        (contactTemplate (templateIndex k)).Adj i j := by
  fin_cases k <;> decide +kernel

private noncomputable def unrootedIso (k : Fin 22) :
    contactTemplate (templateIndex k) ≃g rootedTemplate k where
  toEquiv := Equiv.ofBijective (unrootedWitness k) (unrootedWitness_spec k).1
  map_rel_iff' := fun {i j} => (unrootedWitness_spec k).2 i j

private theorem triangle_of_iso {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {T : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel T.Adj]
    (e : T ≃g G) (h : CubicTriangleFree G) : CubicTriangleFree T := by
  intro a b c hab hbc hca ha hb hc
  exact h (e.map_adj_iff.mpr hab) (e.map_adj_iff.mpr hbc) (e.map_adj_iff.mpr hca)
    ((e.degree_eq a).trans ha) ((e.degree_eq b).trans hb) ((e.degree_eq c).trans hc)

private theorem every_square_of_iso {V : Type u} {W : Type v}
    {G : SimpleGraph V} {T : SimpleGraph W} (e : T ≃g G)
    (h : EveryEdgeSquare G) : EveryEdgeSquare T := by
  intro a b hab
  obtain ⟨c, d, hcb, hda, hac, hcd, hdb⟩ := h (e.map_adj_iff.mpr hab)
  refine ⟨e.symm c, e.symm d, ?_, ?_, e.map_adj_iff.mp ?_, e.map_adj_iff.mp ?_,
    e.map_adj_iff.mp ?_⟩
  · intro hc
    exact hcb (by simpa using congrArg e hc)
  · intro hd
    exact hda (by simpa using congrArg e hd)
  · simpa using hac
  · simpa using hcd
  · simpa using hdb

/-- There are twelve seven-vertex thirteen-edge templates under the contact laws. -/
theorem thirteen_edges_on_seven_vertices {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = 7) (hE : G.edgeFinset.card = 13)
    (hmin : ∀ a, 3 ≤ G.degree a) (hs : SquareCompletion G)
    (ht : SecondCommonNeighbor G) (htri : CubicTriangleFree G)
    (hevery : EveryEdgeSquare G) :
    ∃ kind : Fin 12, Nonempty (contactTemplate kind ≃g G) := by
  classical
  have hroot : ∃ r, G.degree r = 3 := by
    by_contra! h
    have hsum : (∑ a : V, 4) ≤ ∑ a, G.degree a :=
      sum_le_sum fun a _ => by have ha := hmin a; have hne := h a; omega
    rw [G.sum_degrees_eq_twice_card_edges, hE, sum_const, card_univ, hV, nsmul_eq_mul] at hsum
    omega
  obtain ⟨r, hr⟩ := hroot
  obtain ⟨label, _, hroot⟩ := normalize_root G hV r hr
  let K := G.comap label
  let m := encode fun i j => decide (K.Adj i j)
  have hdecoded : graphOfWord m = K := decode K hroot
  let e : graphOfWord m ≃g G :=
    { toEquiv := label
      map_rel_iff' := by
        intro i j
        change K.Adj i j ↔ (graphOfWord m).Adj i j
        rw [hdecoded] }
  have hm : admissible m = true := (admissible_iff m).mpr
    ⟨e.card_edgeFinset_eq.trans hE, fun a => (e.degree_eq a) ▸ hmin (e a),
      square_of_iso e hs, second_of_iso e ht, triangle_of_iso e htri,
      every_square_of_iso e hevery⟩
  obtain ⟨k, a, b, hw⟩ := find_orbit m hm
  have hi := orbitIso k a b
  rw [hw] at hi
  obtain ⟨f⟩ := hi
  exact ⟨templateIndex k, ⟨RelIso.trans (unrootedIso k) (RelIso.trans f.symm e)⟩⟩

#print axioms thirteen_edges_on_seven_vertices

end Q9ThirteenMaskSevenAxisShapes
end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement
