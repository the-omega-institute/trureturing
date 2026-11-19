import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Logic.Equiv.Set
import Mathlib.Tactic.FinCases

/-! Check the finite classifications after labeling the neighbors of vertex zero
as 1, 2, and 3. The masks encode the twelve possible edges from those neighbors
to vertices 4 through 7 and the six possible edges among vertices 4 through 7. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.Q9EightCubicGraphCertificate

private def pairMasks : Fin 6 → ℕ := ![3, 5, 9, 6, 10, 12]
private def tripleMasks : Fin 20 → ℕ :=
  ![7, 11, 19, 35, 13, 21, 37, 25, 41, 49, 14, 22, 38, 26, 42, 50, 28, 44, 52, 56]

def code (a b c : Fin 6) (d : Fin 20) : ℕ :=
  pairMasks a + 16 * pairMasks b + 256 * pairMasks c + 4096 * tripleMasks d

private def edgeSorted (mask i j : ℕ) : Bool :=
  if i = 0 then decide (j ≤ 3)
  else if j ≤ 3 then false
  else if i ≤ 3 then mask.testBit ((i - 1) * 4 + (j - 4))
  else mask.testBit (12 + if i = 4 then j - 5 else if i = 5 then j - 3 else 5)

def adj (mask : ℕ) (i j : Fin 8) : Bool :=
  if i < j then edgeSorted mask i.val j.val
  else if j < i then edgeSorted mask j.val i.val else false

private def vertices := List.finRange 8

def valid (mask : ℕ) : Bool :=
  vertices.all (fun i => (vertices.countP (adj mask i)) == 3) &&
    vertices.all (fun i => vertices.all (fun j => vertices.all (fun k =>
      !(adj mask i j && adj mask j k && adj mask k i))))

private def label (perm : ℕ) (i : Fin 8) : Fin 8 := Fin.ofNat 8 (perm / 8 ^ i.val)

def modelAdj (wagner : Bool) (i j : Fin 8) : Bool :=
  let gap := max i.val j.val - min i.val j.val
  if wagner then gap == 1 || gap == 4 || gap == 7
  else let x := i.val ^^^ j.val; x == 1 || x == 2 || x == 4

private def verifies (mask : ℕ) (wagner : Bool) (perm : ℕ) : Bool :=
  vertices.all (fun i => vertices.all (fun j =>
    (label perm i == label perm j) == (i == j))) &&
    vertices.all (fun i => vertices.all (fun j =>
      adj mask i j == modelAdj wagner (label perm i) (label perm j)))

/- Each entry gives a model and the eight labels, encoded as base-eight digits. -/
private def witnesses : List (ℕ × Bool × ℕ) :=
  [(30380, false, 7829640), (30410, false, 8059016), (31340, false, 11499656),
   (31430, false, 13564040), (31850, false, 12187784), (31910, false, 14022792),
   (54700, true, 11365984), (54730, true, 11366152), (55900, true, 7810656),
   (56005, true, 7810824), (56410, true, 11364808), (56485, true, 7809480),
   (58284, true, 11136776), (58314, true, 11136608), (59964, true, 11135432),
   (60099, true, 8038856), (60474, true, 8040032), (60579, true, 8040200),
   (79516, true, 11480672), (79561, true, 11480840), (80236, true, 7695968),
   (80326, true, 7696136), (81001, true, 11479496), (81046, true, 7694792),
   (90988, true, 5631752), (91078, true, 5631584), (91708, true, 5630408),
   (91843, true, 13543880), (93238, true, 13545056), (93283, true, 13545224),
   (103836, false, 7858312), (103881, false, 8116360), (104796, false, 11528328),
   (104901, false, 13621384), (105561, false, 12302472), (105621, false, 14137480),
   (107420, true, 11222792), (107465, true, 11222624), (108860, true, 11221448),
   (108995, true, 7952840), (109625, true, 7954016), (109715, true, 7954184),
   (115548, true, 5717768), (115653, true, 5717600), (116028, true, 5716424),
   (116163, true, 13457864), (117813, true, 13459040), (117843, true, 13459208),
   (145050, true, 12168800), (145065, true, 12168968), (145770, true, 7007840),
   (145830, true, 7008008), (146025, true, 12167624), (146070, true, 7006664),
   (152938, true, 5173000), (152998, true, 5172832), (153178, true, 5171656),
   (153253, true, 14002632), (154198, true, 14003808), (154213, true, 14003976),
   (169370, true, 12140296), (169385, true, 12140128), (170330, true, 12138952),
   (170405, true, 7035336), (170585, true, 7036512), (170645, true, 7036680),
   (172954, false, 8317064), (172969, false, 8345736), (174394, false, 12445832),
   (174499, false, 14538888), (174649, false, 12531848), (174739, false, 14596232),
   (181082, true, 5945800), (181157, true, 13228488), (181562, true, 5947144),
   (181667, true, 5946976), (182837, true, 13229832), (182867, true, 13229664),
   (202089, true, 5200328), (202134, true, 13973960), (202329, true, 5201672),
   (202389, true, 5201504), (203094, true, 13975304), (203109, true, 13975136),
   (205673, true, 5888456), (205718, true, 13285832), (206393, true, 5889800),
   (206483, true, 5889632), (207158, true, 13287176), (207203, true, 13287008),
   (213846, false, 15657096), (213861, false, 15685768), (214326, false, 16115848),
   (214371, false, 16373896), (214581, false, 16201864), (214611, false, 16431240)]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 16000000 in
-- Check the 4,320 candidates and the explicit permutations of valid graphs.
theorem checked_normalized_codes :
    ∀ (a b c : Fin 6) (d : Fin 20), valid (code a b c d) = true →
      (witnesses.find? (fun w => w.1 == code a b c d)).any
        (fun w => verifies (code a b c d) w.2.1 w.2.2) = true := by
  decide +kernel

#print axioms checked_normalized_codes

/-- A valid encoded graph has a bijective relabeling to the cube or Wagner graph. -/
theorem exists_model_relabeling (a b c : Fin 6) (d : Fin 20)
    (h : valid (code a b c d) = true) :
    ∃ (wagner : Bool) (p : Equiv.Perm (Fin 8)),
      ∀ i j, adj (code a b c d) i j = modelAdj wagner (p i) (p j) := by
  have hm := checked_normalized_codes a b c d h
  cases he : witnesses.find? (fun w => w.1 == code a b c d) with
  | none => simp [he] at hm
  | some w =>
    have hw : verifies (code a b c d) w.2.1 w.2.2 = true := by simpa [he] using hm
    obtain ⟨hinj, hadj⟩ := Bool.and_eq_true_iff.mp hw
    have hmem (i : Fin 8) : i ∈ vertices := List.mem_finRange i
    have hi : Function.Injective (label w.2.2) := by
      intro i j hij
      have hi := List.all_eq_true.mp (List.all_eq_true.mp hinj i (hmem i)) j (hmem j)
      simpa [hij] using hi
    let p := Equiv.ofBijective (label w.2.2) ⟨hi, Finite.injective_iff_surjective.mp hi⟩
    refine ⟨w.2.1, p, fun i j => ?_⟩
    exact beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp hadj i (hmem i)) j (hmem j))

#print axioms exists_model_relabeling

/-- Relabel an actual cubic graph so that vertex zero is fixed and its three
neighbors have labels 1, 2 and 3. -/
theorem normalize_root (G : SimpleGraph (Fin 8)) [DecidableRel G.Adj]
    (hG : G.IsRegularOfDegree 3) :
    ∃ p : Equiv.Perm (Fin 8), p 0 = 0 ∧
      ∀ i, G.Adj 0 (p i) ↔ i ∈ ({1, 2, 3} : Finset (Fin 8)) := by
  classical
  let A : Finset (Fin 8) := {1, 2, 3}
  let B := G.neighborFinset 0
  have hA : A.card = 3 := by decide
  have hB : B.card = 3 := (G.card_neighborFinset_eq_degree 0).trans (hG 0)
  have hC : Aᶜ.card = Bᶜ.card := by
    rw [Finset.card_compl, Finset.card_compl, hA, hB]
  let ea := Finset.equivOfCardEq (hA.trans hB.symm)
  let eb : ((A : Set (Fin 8))ᶜ : Set (Fin 8)) ≃ ((B : Set (Fin 8))ᶜ : Set (Fin 8)) :=
    (Equiv.subtypeEquivRight fun x => Finset.mem_compl.symm).trans
      ((Finset.equivOfCardEq hC).trans (Equiv.subtypeEquivRight fun x => Finset.mem_compl))
  let e := (Equiv.Set.sumCompl (A : Set (Fin 8))).symm.trans
    ((ea.sumCongr eb).trans (Equiv.Set.sumCompl (B : Set (Fin 8))))
  have he (x : Fin 8) : e x ∈ B ↔ x ∈ A := by
    by_cases hx : x ∈ A
    · have h := Equiv.Set.sumCompl_symm_apply_of_mem (show x ∈ (A : Set (Fin 8)) from hx)
      refine iff_of_true ?_ hx
      change (Equiv.Set.sumCompl (B : Set (Fin 8))
        ((ea.sumCongr eb) ((Equiv.Set.sumCompl (A : Set (Fin 8))).symm x))) ∈ B
      rw [h]
      exact (ea ⟨x, hx⟩).property
    · have h := Equiv.Set.sumCompl_symm_apply_of_notMem (show x ∉ (A : Set (Fin 8)) from hx)
      refine iff_of_false ?_ hx
      change (Equiv.Set.sumCompl (B : Set (Fin 8))
        ((ea.sumCongr eb) ((Equiv.Set.sumCompl (A : Set (Fin 8))).symm x))) ∉ B
      rw [h]
      exact (eb ⟨x, hx⟩).property
  have h0 : (0 : Fin 8) ∉ B := by simp [B]
  have he0 : e 0 ∉ B := fun h => (by decide : (0 : Fin 8) ∉ A) ((he 0).mp h)
  let swap := Equiv.swap (e 0) 0
  have hs (x : Fin 8) : swap x ∈ B ↔ x ∈ B := by
    by_cases h1 : x = e 0
    · subst x
      simp [swap, h0, he0]
    by_cases h2 : x = 0
    · subst x
      simp [swap, h0, he0]
    rw [show swap x = x from Equiv.swap_apply_of_ne_of_ne h1 h2]
  refine ⟨e.trans swap, by simp [swap], fun i => ?_⟩
  exact (G.mem_neighborFinset 0 _).symm.trans ((hs (e i)).trans (he i))

#print axioms normalize_root

/-- In the normalized labeling the three neighbors each have two edges to the
last four vertices, and the last four vertices span exactly three edges. -/
theorem normalized_edge_counts (G : SimpleGraph (Fin 8)) [DecidableRel G.Adj]
    (hr : G.IsRegularOfDegree 3)
    (ht : ∀ x y z, G.Adj x y → G.Adj y z → G.Adj z x → False)
    (hroot : ∀ i, G.Adj 0 i ↔ i ∈ ({1, 2, 3} : Finset (Fin 8))) :
    let w := fun (i j : Fin 8) => if G.Adj i j then (1 : ℕ) else 0
    (∀ i ∈ ({1, 2, 3} : Finset (Fin 8)), w i 4 + w i 5 + w i 6 + w i 7 = 2) ∧
      w 4 5 + w 4 6 + w 4 7 + w 5 6 + w 5 7 + w 6 7 = 3 := by
  let w := fun (i j : Fin 8) => if G.Adj i j then (1 : ℕ) else 0
  have hsum (i : Fin 8) : ∑ j : Fin 8, w i j = 3 := by
    have h := hr i
    rw [← SimpleGraph.card_neighborFinset_eq_degree G i,
      SimpleGraph.neighborFinset_eq_filter, Finset.card_filter] at h
    exact h
  have hrow (i : Fin 8) :
      w i 0 + w i 1 + w i 2 + w i 3 + w i 4 + w i 5 + w i 6 + w i 7 = 3 := by
    have h := hsum i
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
    change w i 0 + (w i 1 + (w i 2 + (w i 3 + (w i 4 + (w i 5 +
      (w i 6 + w i 7)))))) = 3 at h
    simpa only [add_assoc] using h
  have hsymm (i j : Fin 8) : w i j = w j i := by simp [w, G.adj_comm]
  have hloop (i : Fin 8) : w i i = 0 := by simp [w]
  have hnear (i : Fin 8) (hi : i ∈ ({1, 2, 3} : Finset (Fin 8))) :
      w i 4 + w i 5 + w i 6 + w i 7 = 2 := by
    have hzero : w i 0 = 1 := ite_eq_left ((hroot i).mpr hi).symm
    have hnone (j : Fin 8) (hj : j ∈ ({1, 2, 3} : Finset (Fin 8))) : w i j = 0 :=
      ite_eq_right (fun h => ht 0 i j ((hroot i).mpr hi) h ((hroot j).mpr hj).symm)
    have h := hrow i
    rw [hzero, hnone 1 (by decide), hnone 2 (by decide), hnone 3 (by decide)] at h
    omega
  refine ⟨hnear, ?_⟩
  have h0 (i : Fin 8) (hi : i ∉ ({1, 2, 3} : Finset (Fin 8))) : w i 0 = 0 :=
    ite_eq_right (fun h => hi ((hroot i).mp h.symm))
  have h4 := hrow 4
  have h5 := hrow 5
  have h6 := hrow 6
  have h7 := hrow 7
  rw [h0 4 (by decide), hloop 4, hsymm 4 1, hsymm 4 2, hsymm 4 3] at h4
  rw [h0 5 (by decide), hloop 5, hsymm 5 1, hsymm 5 2, hsymm 5 3, hsymm 5 4] at h5
  rw [h0 6 (by decide), hloop 6, hsymm 6 1, hsymm 6 2, hsymm 6 3, hsymm 6 4, hsymm 6 5] at h6
  rw [h0 7 (by decide), hloop 7, hsymm 7 1, hsymm 7 2, hsymm 7 3,
    hsymm 7 4, hsymm 7 5, hsymm 7 6] at h7
  have h1 := hnear 1 (by decide)
  have h2 := hnear 2 (by decide)
  have h3 := hnear 3 (by decide)
  change w 4 5 + w 4 6 + w 4 7 + w 5 6 + w 5 7 + w 6 7 = 3
  omega

#print axioms normalized_edge_counts

private theorem pair_digits : ∀ x y z t : Bool,
    x.toNat + y.toNat + z.toNat + t.toNat = 2 →
      ∃ a : Fin 6, (pairMasks a).testBit 0 = x ∧ (pairMasks a).testBit 1 = y ∧
        (pairMasks a).testBit 2 = z ∧ (pairMasks a).testBit 3 = t := by
  decide +kernel

private theorem triple_digits : ∀ x y z u v w : Bool,
    x.toNat + y.toNat + z.toNat + u.toNat + v.toNat + w.toNat = 3 →
      ∃ a : Fin 20, (tripleMasks a).testBit 0 = x ∧ (tripleMasks a).testBit 1 = y ∧
        (tripleMasks a).testBit 2 = z ∧ (tripleMasks a).testBit 3 = u ∧
        (tripleMasks a).testBit 4 = v ∧ (tripleMasks a).testBit 5 = w := by
  intro x y z u v w
  cases x <;> cases y <;> cases z <;> cases u <;> cases v <;> cases w <;> decide +kernel

private def cutDigits (a b c : Fin 6) (i : Fin 3) : ℕ := ![pairMasks a, pairMasks b, pairMasks c] i

set_option maxRecDepth 4096 in
set_option maxHeartbeats 16000000 in
-- Check the bit positions in the bounded code.
private theorem code_digits : ∀ (a b c : Fin 6) (d : Fin 20),
    (∀ (i : Fin 3) (j : Fin 4),
      (code a b c d).testBit (i.val * 4 + j.val) = (cutDigits a b c i).testBit j.val) ∧
    (∀ j : Fin 6, (code a b c d).testBit (12 + j.val) = (tripleMasks d).testBit j.val) := by
  decide +kernel

/-- The edge counts of a normalized graph encode it among the checked codes. -/
theorem exists_code_of_normalized (G : SimpleGraph (Fin 8)) [DecidableRel G.Adj]
    (hr : G.IsRegularOfDegree 3)
    (ht : ∀ x y z, G.Adj x y → G.Adj y z → G.Adj z x → False)
    (hroot : ∀ i, G.Adj 0 i ↔ i ∈ ({1, 2, 3} : Finset (Fin 8))) :
    ∃ (a b c : Fin 6) (d : Fin 20), ∀ i j, adj (code a b c d) i j = decide (G.Adj i j) := by
  let f := fun (i j : Fin 8) => decide (G.Adj i j)
  have hweight (i j : Fin 8) : (f i j).toNat = if G.Adj i j then 1 else 0 := by
    by_cases h : G.Adj i j <;> simp [f, h]
  obtain ⟨hcut, htail⟩ := normalized_edge_counts G hr ht hroot
  have hpair (i : Fin 8) (hi : i ∈ ({1, 2, 3} : Finset (Fin 8))) :
      ∃ a : Fin 6, (pairMasks a).testBit 0 = f i 4 ∧ (pairMasks a).testBit 1 = f i 5 ∧
        (pairMasks a).testBit 2 = f i 6 ∧ (pairMasks a).testBit 3 = f i 7 :=
    pair_digits _ _ _ _ (by simpa only [hweight] using hcut i hi)
  obtain ⟨a, ha0, ha1, ha2, ha3⟩ := hpair 1 (by decide)
  obtain ⟨b, hb0, hb1, hb2, hb3⟩ := hpair 2 (by decide)
  obtain ⟨c, hc0, hc1, hc2, hc3⟩ := hpair 3 (by decide)
  obtain ⟨d, hd0, hd1, hd2, hd3, hd4, hd5⟩ :=
    triple_digits (f 4 5) (f 4 6) (f 4 7) (f 5 6) (f 5 7) (f 6 7)
      (by simpa only [hweight] using htail)
  let mask := code a b c d
  have hc (i : Fin 3) (j : Fin 4) :
      mask.testBit (i.val * 4 + j.val) = (cutDigits a b c i).testBit j.val :=
    (code_digits a b c d).1 i j
  have hd (j : Fin 6) : mask.testBit (12 + j.val) = (tripleMasks d).testBit j.val :=
    (code_digits a b c d).2 j
  have hsymm (i j : Fin 8) : f i j = f j i := by simp [f, G.adj_comm]
  have hnone (i j : Fin 8) (hi : i ∈ ({1, 2, 3} : Finset (Fin 8)))
      (hj : j ∈ ({1, 2, 3} : Finset (Fin 8))) : f i j = false :=
    decide_eq_false (fun h => ht 0 i j ((hroot i).mpr hi) h ((hroot j).mpr hj).symm)
  have hs : ∀ i j, adj mask i j = adj mask j i := by
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · simp [adj, h, not_lt_of_ge h.le]
    · simp [adj]
    · simp [adj, h, not_lt_of_ge h.le]
  have hf : ∀ i j : Fin 8, i ≤ j → adj mask i j = f i j := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> try (exfalso; exact (by decide : ¬ _ ≤ _) hij)
    all_goals try rfl
    all_goals try (simp [adj, edgeSorted, f, hroot] <;> done)
    all_goals try (rw [hnone _ _ (by decide) (by decide)]; rfl)
    all_goals first
      | exact (hc 0 0).trans ha0
      | exact (hc 0 1).trans ha1
      | exact (hc 0 2).trans ha2
      | exact (hc 0 3).trans ha3
      | exact (hc 1 0).trans hb0
      | exact (hc 1 1).trans hb1
      | exact (hc 1 2).trans hb2
      | exact (hc 1 3).trans hb3
      | exact (hc 2 0).trans hc0
      | exact (hc 2 1).trans hc1
      | exact (hc 2 2).trans hc2
      | exact (hc 2 3).trans hc3
      | exact (hd 0).trans hd0
      | exact (hd 1).trans hd1
      | exact (hd 2).trans hd2
      | exact (hd 3).trans hd3
      | exact (hd 4).trans hd4
      | exact (hd 5).trans hd5
  refine ⟨a, b, c, d, fun i j => ?_⟩
  rcases le_total i j with h | h
  · exact hf i j h
  · exact (hs i j).trans ((hf j i h).trans (hsymm j i))

#print axioms exists_code_of_normalized

/-- Every triangle-free cubic graph on eight vertices has the adjacency
of the cube or the Wagner graph after a bijective relabeling. -/
theorem cube_or_wagner (G : SimpleGraph (Fin 8)) [DecidableRel G.Adj]
    (hr : G.IsRegularOfDegree 3)
    (ht : ∀ x y z, G.Adj x y → G.Adj y z → G.Adj z x → False) :
    ∃ (wagner : Bool) (p : Equiv.Perm (Fin 8)),
      ∀ i j, G.Adj i j ↔ modelAdj wagner (p i) (p j) = true := by
  classical
  obtain ⟨q, hq, hroot⟩ := normalize_root G hr
  let H := G.comap q
  have hrH (i : Fin 8) : H.degree i = 3 :=
    ((SimpleGraph.Iso.comap q G).degree_eq i).symm.trans (hr (q i))
  have htH (x y z : Fin 8) (hxy : H.Adj x y) (hyz : H.Adj y z)
      (hzx : H.Adj z x) : False := ht (q x) (q y) (q z) hxy hyz hzx
  have hrootH (i : Fin 8) : H.Adj 0 i ↔ i ∈ ({1, 2, 3} : Finset (Fin 8)) := by
    change G.Adj (q 0) (q i) ↔ _
    rw [hq]
    exact hroot i
  obtain ⟨a, b, c, d, hcode⟩ := exists_code_of_normalized H hrH htH hrootH
  let mask := code a b c d
  have hvalid : valid mask = true := by
    apply Bool.and_eq_true_iff.mpr
    constructor
    · apply List.all_eq_true.mpr
      intro i _
      apply beq_iff_eq.mpr
      have hnodup : vertices.Nodup := List.nodup_finRange 8
      have hall : vertices.toFinset = Finset.univ := by
        ext j
        simp [vertices]
      have hcount := hnodup.card_eq_countP (P := H.Adj i)
      rw [hall, ← SimpleGraph.neighborFinset_eq_filter,
        SimpleGraph.card_neighborFinset_eq_degree, hrH] at hcount
      rw [show adj mask i = (fun j => decide (H.Adj i j)) from funext (hcode i)]
      exact hcount.symm
    · apply List.all_eq_true.mpr
      intro i _
      apply List.all_eq_true.mpr
      intro j _
      apply List.all_eq_true.mpr
      intro k _
      by_cases h1 : H.Adj i j
      · by_cases h2 : H.Adj j k
        · have h3 : ¬ H.Adj k i := htH i j k h1 h2
          simp [mask, hcode, h3]
        · simp [mask, hcode, h2]
      · simp [mask, hcode, h1]
  obtain ⟨wagner, σ, hσ⟩ := exists_model_relabeling a b c d hvalid
  refine ⟨wagner, q.symm.trans σ, fun i j => ?_⟩
  change G.Adj i j ↔ modelAdj wagner (σ (q.symm i)) (σ (q.symm j)) = true
  rw [← hσ, hcode, decide_eq_true_eq]
  change G.Adj i j ↔ G.Adj (q (q.symm i)) (q (q.symm j))
  simp

#print axioms cube_or_wagner

end D5.S3.Combinatorics.Graph.HypercubeCritical.Q9EightCubicGraphCertificate
