import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Bitwise
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Logic.Equiv.Set

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

end D5.S3.Combinatorics.Graph.HypercubeCritical.Q9EightCubicGraphCertificate
