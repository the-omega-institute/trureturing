import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FifteenMaskNineAxisProfile
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9DegreeRows
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9CubicContactHighBlock
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FifteenMaskLargeAxesReplay
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9CubicTriangleExclusion
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ContactGraphTriangles
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9EveryContactEdgeSquare
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.Chain

/-! Fifteen contact edges on nine axes. The high-degree block has at most
three vertices. Read its rows in decreasing bit order, so sorting the cubic
columns also sorts every prefix of the high bits. Then fill in the cubic rows
by their residual degrees. -/

set_option autoImplicit false
set_option maxRecDepth 50000
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FifteenMaskNineAxisClassification

open Finset
open scoped BigOperators
open Q9SharedContactCNF (Axis Word)
open Q9TenMaskGraph (SquareCompletion)
open Q9DegreeRows (degreeEdges)
open private support_degreeEdges from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9DegreeRows

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The cubic square law, the second common neighbor law, cubic triangle
exclusion, and the square law for individual edges. -/
structure LocalLaws (G : SimpleGraph V) [DecidableRel G.Adj] : Prop where
  cubicSquare : SquareCompletion G
  secondNeighbor : ∀ ⦃a b c : V⦄, G.Adj a b → G.degree a = 3 → G.degree b = 3 →
    G.Adj a c → G.Adj b c → ∃ d, d ≠ c ∧ G.Adj a d ∧ G.Adj b d
  noCubicTriangle : ∀ a b c : V, G.Adj a b → G.Adj b c → G.Adj c a →
    G.degree a = 3 → G.degree b = 3 → G.degree c = 3 → False
  edgeSquare : ∀ ⦃a b : V⦄, G.Adj a b →
    ∃ c, G.Adj a c ∧ c ≠ b ∧ ∃ d, d ≠ a ∧ G.Adj b d ∧ G.Adj c d

private theorem laws_of_iso {G : SimpleGraph V} {K : SimpleGraph Axis}
    [DecidableRel G.Adj] [DecidableRel K.Adj]
    (e : K ≃g G) (h : LocalLaws G) : LocalLaws K := by
  have adj (a b : Axis) : G.Adj (e a) (e b) ↔ K.Adj a b := e.map_adj_iff
  have deg (a : Axis) : G.degree (e a) = K.degree a := e.degree_eq a
  have pull (a b c : Axis)
      (h' : ∃ d, d ≠ e a ∧ G.Adj (e b) d ∧ G.Adj (e c) d) :
      ∃ d, d ≠ a ∧ K.Adj b d ∧ K.Adj c d := by
    obtain ⟨d, hd, hb, hc⟩ := h'
    refine ⟨e.symm d, ?_, (adj _ _).mp ?_, (adj _ _).mp ?_⟩
    · intro he
      exact hd (by simpa using congrArg e he)
    · simpa using hb
    · simpa using hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b c hab hac hbc ha hb
    exact pull a b c (h.cubicSquare ((adj _ _).mpr hab) ((adj _ _).mpr hac)
      (e.injective.ne hbc) ((deg a).trans ha) ((deg b).trans hb))
  · intro a b c hab ha hb hac hbc
    exact pull c a b (h.secondNeighbor ((adj _ _).mpr hab)
      ((deg a).trans ha) ((deg b).trans hb) ((adj _ _).mpr hac) ((adj _ _).mpr hbc))
  · intro a b c hab hbc hca ha hb hc
    exact h.noCubicTriangle _ _ _ ((adj _ _).mpr hab) ((adj _ _).mpr hbc)
      ((adj _ _).mpr hca) ((deg a).trans ha) ((deg b).trans hb) ((deg c).trans hc)
  · intro a b hab
    obtain ⟨c, hac, hcb, hd⟩ := h.edgeSquare ((adj _ _).mpr hab)
    refine ⟨e.symm c, (adj _ _).mp (by simpa using hac), ?_, pull a b (e.symm c) ?_⟩
    · intro he
      exact hcb (by simpa using congrArg e he)
    · simpa using hd

private abbrev Row := Axis × List Axis
private abbrev Rows := List Row

private abbrev high (k : Fin 3) : ℕ := k.val + 1
private def degrees (k : Fin 3) : Axis → ℕ :=
  ![![6,3,3,3,3,3,3,3,3], ![4,5,3,3,3,3,3,3,3], ![4,4,4,3,3,3,3,3,3]] k
private def order (k : Fin 3) : List Axis :=
  ![[0,1,2,3,4,5,6,7,8], [1,0,2,3,4,5,6,7,8], [2,1,0,3,4,5,6,7,8]] k
private def low (k : Fin 3) : List Axis := (order k).drop (high k)

private theorem order_ok (k : Fin 3) :
    (order k).Nodup ∧ ∀ i : Axis, i ∈ order k := by
  fin_cases k <;> decide +kernel

private theorem cubic_iff (k : Fin 3) (a : Axis) :
    degrees k a = 3 ↔ high k ≤ a.val := by
  revert a
  fin_cases k <;> decide +kernel

private def encode (G : SimpleGraph Axis) [DecidableRel G.Adj] : List Axis → Rows
  | [] => []
  | v :: vs => (v, vs.filter fun u => decide (G.Adj v u)) :: encode G vs

private def forward (rows : Rows) (a b : Axis) : Bool :=
  rows.any fun r => r.1 == a && r.2.contains b

private theorem forward_cut (G : SimpleGraph Axis) [DecidableRel G.Adj]
    (pre rest : List Axis) {a b : Axis} (hb : b ∈ rest) :
    forward ((encode G (pre ++ rest)).take pre.length) a b = true ↔
      a ∈ pre ∧ G.Adj a b := by
  induction pre with
  | nil => simp [forward]
  | cons v pre ih =>
    have hm : b ∈ pre ++ rest := List.mem_append_right _ hb
    simp only [List.cons_append, List.length_cons, encode, List.take_succ_cons,
      forward, List.any_cons, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
      List.contains_iff_mem, List.mem_filter, decide_eq_true_eq, List.mem_cons]
    change (v = a ∧ (b ∈ pre ++ rest ∧ G.Adj v b)) ∨
      forward ((encode G (pre ++ rest)).take pre.length) a b = true ↔ _
    rw [ih]
    simp only [hm, true_and]
    constructor
    · rintro (⟨rfl, hadj⟩ | ⟨ha, hadj⟩)
      · exact ⟨Or.inl rfl, hadj⟩
      · exact ⟨Or.inr ha, hadj⟩
    · rintro ⟨rfl | ha, hadj⟩
      · exact Or.inl ⟨rfl, hadj⟩
      · exact Or.inr ⟨ha, hadj⟩

private def score (bits : Axis → Bool) : ℕ :=
  (if bits 0 then 1 else 0) + (if bits 1 then 2 else 0) + (if bits 2 then 4 else 0)

private theorem score_cut (n : Fin 4) (bits : Axis → Bool) :
    score (fun i => decide (n.val ≤ i.val) && bits i) = (score bits / 2 ^ n.val) * 2 ^ n.val := by
  have h : ∀ (m : Fin 4) (a b c : Bool),
      (if decide (m.val ≤ 0) && a then 1 else 0) +
      (if decide (m.val ≤ 1) && b then 2 else 0) +
      (if decide (m.val ≤ 2) && c then 4 else 0) =
      (((if a then 1 else 0) + (if b then 2 else 0) + (if c then 4 else 0)) /
        (2 : ℕ) ^ m.val) * 2 ^ m.val := by decide +kernel
  exact h n (bits 0) (bits 1) (bits 2)

private def keepPrefix (k : Fin 3) (rows : Rows) : Bool :=
  if rows.length ≤ high k then
    decide ((low k).IsChain fun a b => score (fun i => forward rows i a) ≤
      score (fun i => forward rows i b))
  else true

private theorem order_cuts (k : Fin 3) (n : Fin 4) (hn : n.val ≤ high k) :
    ((low k).IsChain (· ≤ ·)) ∧
    (∀ j ∈ low k, high k ≤ (j : Axis).val ∧ j ∈ (order k).drop n.val) ∧
    (∀ i : Axis, i ∈ (order k).take n.val ↔ high k - n.val ≤ i.val ∧ i.val < high k) := by
  revert n
  fin_cases k <;> decide +kernel

private def sig (k : Fin 3) (G : SimpleGraph Axis) [DecidableRel G.Adj] (a : Axis) : ℕ :=
  score (fun i => decide (i.val < high k) && decide (G.Adj i a))

private theorem encode_length (G : SimpleGraph Axis) [DecidableRel G.Adj] (vs : List Axis) :
    (encode G vs).length = vs.length := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [encode, ih]

private theorem keep_of_sorted (k : Fin 3) (G : SimpleGraph Axis) [DecidableRel G.Adj]
    (hs : ∀ a b : Axis, high k ≤ a.val → a ≤ b → sig k G a ≤ sig k G b)
    {pre rest : Rows} (he : pre ++ rest = encode G (order k)) :
    keepPrefix k pre = true := by
  unfold keepPrefix
  split
  next hn =>
    let n : Fin 4 := ⟨pre.length, by have := k.isLt; unfold high at hn; omega⟩
    obtain ⟨hchain, hlow, hhigh⟩ := order_cuts k n hn
    have hp : pre = (encode G (order k)).take n.val := by
      rw [← he]
      simp [n]
    have hlen : ((order k).take n.val).length = n.val := by
      apply List.length_take_of_le
      have hl := congrArg List.length he
      rw [List.length_append, encode_length] at hl
      change pre.length ≤ (order k).length
      omega
    have hscore (a : Axis) (ha : a ∈ low k) :
        score (fun i => forward pre i a) = (sig k G a / 2 ^ (high k - n.val)) * 2 ^ (high k - n.val) := by
      let cut : Fin 4 := ⟨high k - n.val, by have := k.isLt; unfold high; omega⟩
      have hagree (i : Axis) :
          forward pre i a = (decide (cut.val ≤ i.val) &&
            (decide (i.val < high k) && decide (G.Adj i a))) := by
        apply Bool.eq_iff_iff.mpr
        have hf := forward_cut G ((order k).take n.val) ((order k).drop n.val)
          (a := i) (hlow a ha).2
        rw [List.take_append_drop, hlen] at hf
        rw [hp, hf, hhigh]
        simp only [Bool.and_eq_true, decide_eq_true_eq, cut, and_assoc]
      rw [funext hagree, score_cut cut] <;> rfl
    apply decide_eq_true
    exact hchain.imp_of_mem_imp fun a b ha hb hab => by
      rw [hscore a ha, hscore b hb]
      exact Nat.mul_le_mul_right _ (Nat.div_le_div_right (hs a b (hlow a ha).1 hab))
  next => rfl

/-- List implementation of the degree-prescribed row search. Prefix tests
use the high bits already fixed by the selected rows. -/
private def scan (keep : Rows → Bool) : List Axis → (Axis → ℕ) → Rows → List Rows
  | [], _, pre => [pre]
  | v :: vs, d, pre =>
    ((vs.filter fun u => decide (0 < d u)).sublistsLen (d v)).flatMap fun N =>
      let next := pre ++ [(v,N)]
      if keep next then scan keep vs (fun u => d u - if N.contains u then 1 else 0) next
      else []

private theorem scan_complete (keep : Rows → Bool)
    (G : SimpleGraph Axis) [DecidableRel G.Adj]
    (vs : List Axis) (hvs : vs.Nodup) (d : Axis → ℕ) (pre : Rows)
    {E : Finset (Axis × Axis)} (hE : E ∈ degreeEdges vs d)
    (hcover : ∀ a ∈ vs.toFinset, ∀ b ∈ vs.toFinset,
      G.Adj a b ↔ (a,b) ∈ E ∨ (b,a) ∈ E)
    (hkeep : ∀ p q : Rows, p ++ q = encode G vs → keep (pre ++ p) = true) :
    pre ++ encode G vs ∈ scan keep vs d pre := by
  induction vs generalizing d pre E with
  | nil => simp [scan, encode]
  | cons v vs ih =>
    have hv : v ∉ vs.toFinset := by simpa using (List.nodup_cons.mp hvs).1
    simp only [degreeEdges] at hE
    obtain ⟨N, hN, hmem⟩ := mem_biUnion.mp hE
    obtain ⟨F, hF, rfl⟩ := mem_image.mp hmem
    letI : ∀ N : Finset Axis, Decidable (∀ u ∈ N, 0 < d u) := fun _ => decidableDforallFinset
    obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp (mem_filter.mp hN).1
    have hpos := (mem_filter.mp hN).2
    have hnL (u : Axis) : (v,u) ∉ F :=
      fun h => hv (support_degreeEdges vs _ hF _ h).1
    have hnR (u : Axis) : (u,v) ∉ F :=
      fun h => hv (support_degreeEdges vs _ hF _ h).2
    have hrow (u : Axis) (hu : u ∈ vs.toFinset) : G.Adj v u ↔ u ∈ N := by
      have huv : u ≠ v := fun he => hv (he ▸ hu)
      have hu' : u ∈ (v :: vs).toFinset := by
        simp only [List.toFinset_cons, mem_insert]
        exact Or.inr hu
      simpa [hnL, hnR, Finset.mem_image, huv, Ne.symm huv] using
        hcover v (by simp) u hu'
    let row := vs.filter fun u => decide (G.Adj v u)
    have hrowN : row.toFinset = N := by
      ext u
      simp only [row, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
      exact ⟨fun ⟨hu, ha⟩ => (hrow u (List.mem_toFinset.mpr hu)).mp ha,
        fun hu => ⟨List.mem_toFinset.mp (hsub hu), (hrow u (hsub hu)).mpr hu⟩⟩
    have hrowPos : ∀ u ∈ row, decide (0 < d u) = true := by
      intro u hu
      exact decide_eq_true (hpos u (hrowN ▸ List.mem_toFinset.mpr hu))
    have hchoose : row ∈ (vs.filter fun u => decide (0 < d u)).sublistsLen (d v) := by
      apply List.mem_sublistsLen.mpr
      refine ⟨List.sublist_filter_iff.mpr ⟨row, List.filter_sublist, ?_⟩, ?_⟩
      · exact (List.filter_eq_self.mpr hrowPos).symm
      · rw [← List.toFinset_card_of_nodup ((List.nodup_cons.mp hvs).2.filter _), hrowN, hcard]
    have hq (u : Axis) : (d u - if u ∈ N then 1 else 0) =
        (d u - if row.contains u then 1 else 0) := by
      simp [← hrowN, List.contains_iff_mem]
    have hcover' (a : Axis) (ha : a ∈ vs.toFinset) (b : Axis) (hb : b ∈ vs.toFinset) :
        G.Adj a b ↔ (a,b) ∈ F ∨ (b,a) ∈ F := by
      have hav : a ≠ v := fun he => hv (he ▸ ha)
      have hbv : b ≠ v := fun he => hv (he ▸ hb)
      have lift_mem (u : Axis) (hu : u ∈ vs.toFinset) : u ∈ (v :: vs).toFinset := by
        simp only [List.toFinset_cons, mem_insert]
        exact Or.inr hu
      simpa [Finset.mem_image, hav, hbv, Ne.symm hav, Ne.symm hbv] using
        hcover a (lift_mem a ha) b (lift_mem b hb)
    have hk : keep (pre ++ [(v,row)]) = true := hkeep [(v,row)] (encode G vs) rfl
    have ht := ih (List.nodup_cons.mp hvs).2 _ (pre ++ [(v,row)]) hF hcover' (by
      intro p q hp
      rw [List.append_assoc]
      apply hkeep ([(v,row)] ++ p) q
      simp [hp, encode]
      rfl)
    rw [show (fun u => d u - if u ∈ N then 1 else 0) =
      (fun u => d u - if row.contains u then 1 else 0) from funext hq] at ht
    simp only [scan, List.mem_flatMap]
    refine ⟨row, hchoose, ?_⟩
    rw [if_pos hk]
    simpa only [encode, List.append_assoc, List.singleton_append] using ht

private def neighbors (rows : Rows) (a : Axis) : List Axis :=
  rows.flatMap fun r =>
    (if r.1 = a then r.2 else []) ++ (if r.2.contains a then [r.1] else [])

private theorem mem_neighbors_encode (G : SimpleGraph Axis) [DecidableRel G.Adj]
    (vs : List Axis) (a b : Axis) :
    b ∈ neighbors (encode G vs) a ↔ a ∈ vs ∧ b ∈ vs ∧ G.Adj a b := by
  induction vs with
  | nil => simp [encode, neighbors]
  | cons v vs ih =>
    change b ∈ ((if v = a then vs.filter (fun u => decide (G.Adj v u)) else []) ++
      (if (vs.filter (fun u => decide (G.Adj v u))).contains a then [v] else [])) ++
        neighbors (encode G vs) a ↔ _
    rw [List.mem_append, List.mem_append, ih]
    by_cases ha : v = a <;> by_cases hb : v = b
    · subst a
      subst b
      simp [G.irrefl, List.contains_iff_mem]
    · subst a
      by_cases h : (vs.filter (fun u => decide (G.Adj v u))).contains v = true
      all_goals simp [hb, Ne.symm hb, h] <;> tauto
    · subst b
      by_cases h : (vs.filter (fun u => decide (G.Adj v u))).contains a = true
      · have hh := List.contains_iff_mem.mp h
        simp only [List.mem_filter, decide_eq_true_eq] at hh
        simp [ha, Ne.symm ha, h, hh.1, hh.2, hh.2.symm]
      · have hh : ¬ (a ∈ vs ∧ G.Adj a v) := by
          rintro ⟨hm, hadj⟩
          exact h (List.contains_iff_mem.mpr (List.mem_filter.mpr ⟨hm, decide_eq_true hadj.symm⟩))
        have hn : ¬ (a ∈ vs ∧ G.Adj v a) := fun he => hh ⟨he.1, he.2.symm⟩
        simp [ha, Ne.symm ha, h, hh, hn]
        tauto
    · by_cases h : (vs.filter (fun u => decide (G.Adj v u))).contains a = true
      all_goals simp [ha, Ne.symm ha, hb, Ne.symm hb, h]

private def other (N : Axis → List Axis) (a b c : Axis) : Bool :=
  (N b).any fun d => d != a && (N c).contains d

private def passes (k : Fin 3) (rows : Rows) : Bool :=
  let N := neighbors rows
  (List.finRange 9).all fun a => (N a).all fun b =>
    ((N a).any fun c => c != b && other N a b c) &&
    (if high k ≤ a.val ∧ high k ≤ b.val then
      (N a).all fun c =>
        (if c = b then true else other N a b c) &&
        (if (N b).contains c then decide (c.val < high k) && other N c a b else true)
    else true)

private theorem passes_of_laws (k : Fin 3) (G : SimpleGraph Axis) [DecidableRel G.Adj]
    (hd : ∀ a, G.degree a = degrees k a) (hl : LocalLaws G) :
    passes k (encode G (order k)) = true := by
  let N := neighbors (encode G (order k))
  have adj (a b : Axis) : b ∈ N a ↔ G.Adj a b := by
    simpa only [N, (order_ok k).2 a, (order_ok k).2 b, true_and] using
      mem_neighbors_encode G (order k) a b
  have other_of (a b c : Axis) (h : ∃ d, d ≠ a ∧ G.Adj b d ∧ G.Adj c d) :
      other N a b c = true := by
    obtain ⟨d, hda, hbd, hcd⟩ := h
    apply List.any_eq_true.mpr
    refine ⟨d, (adj _ _).mpr hbd, ?_⟩
    simp [hda, List.contains_iff_mem, (adj _ _).mpr hcd]
  have cubic (a : Axis) : G.degree a = 3 ↔ high k ≤ a.val := by
    rw [hd a, cubic_iff]
  unfold passes
  apply List.all_eq_true.mpr
  intro a _
  apply List.all_eq_true.mpr
  intro b hb
  have hab := (adj a b).mp hb
  simp only [Bool.and_eq_true]
  constructor
  · obtain ⟨c, hac, hcb, he⟩ := hl.edgeSquare hab
    exact List.any_eq_true.mpr ⟨c, (adj _ _).mpr hac, by
      change (c != b && other N a b c) = true
      simp [hcb, Ne.symm hcb, other_of a b c he]⟩
  · split
    next h =>
      have ha := (cubic a).mpr h.1
      have hb' := (cubic b).mpr h.2
      apply List.all_eq_true.mpr
      intro c hc
      have hac := (adj a c).mp hc
      simp only [Bool.and_eq_true]
      constructor
      · by_cases he : c = b
        · simp [he]
        · simpa [he] using other_of a b c (hl.cubicSquare hab hac (Ne.symm he) ha hb')
      · split
        next hbc =>
          have hbc' := (adj b c).mp (List.contains_iff_mem.mp hbc)
          have hlt : c.val < high k := by
            by_contra! hge
            exact hl.noCubicTriangle a b c hab hbc' hac.symm ha hb' ((cubic c).mpr hge)
          rw [Bool.and_eq_true]
          exact ⟨decide_eq_true hlt, other_of c a b (hl.secondNeighbor hab ha hb' hac hbc')⟩
        next => rfl
    next => rfl

/-- Witness words in audit order for 483F4265747077, 483F6F70766245,
and 483F717642605B. The common root mask 3 is inserted by `recipe`. -/
def maskWords (kind : Fin 3) : List Word :=
  ![[6,10,65,68,80,96,129,136,144,160,260,264,272,288],
    [6,40,48,66,72,80,129,132,136,144,257,260,288,320],
    [6,33,40,48,65,68,72,132,136,144,258,260,272,288]] kind

def recipeFamily (kind : Fin 3) : Finset (Finset Axis) :=
  (Q9FifteenMaskLargeAxesReplay.recipe (maskWords kind)).family

/-- The recipe graph uses the actual coordinate labels of the mask words. -/
def recipeGraph (kind : Fin 3) : SimpleGraph Axis :=
  SimpleGraph.fromRel fun a b => ({a,b} : Finset Axis) ∈ recipeFamily kind

instance (kind : Fin 3) : DecidableRel (recipeGraph kind).Adj := by
  unfold recipeGraph
  infer_instance

theorem recipeGraph_adj (kind : Fin 3) (a b : Axis) :
    (recipeGraph kind).Adj a b ↔ a ≠ b ∧ ({a,b} : Finset Axis) ∈ recipeFamily kind := by
  simp [recipeGraph, Finset.pair_comm b a]

private def witness : Fin 16 → Rows × (Fin 3 × (Axis → Axis)) :=
  ![([(2,[5,6,7,8]),(1,[4,6,7,8]),(0,[4,5,7,8]),(3,[4,5,6]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[])], (0, ![6,7,8,1,0,2,3,4,5])),
    ([(2,[1,6,7,8]),(1,[3,4,5]),(0,[4,5,7,8]),(3,[7,8]),(4,[6]),(5,[6]),(6,[]),(7,[]),(8,[])], (1, ![7,8,6,5,0,2,1,3,4])),
    ([(2,[0,6,7,8]),(1,[4,5,7,8]),(0,[3,4,5]),(3,[7,8]),(4,[6]),(5,[6]),(6,[]),(7,[]),(8,[])], (1, ![8,7,6,5,0,2,1,3,4])),
    ([(2,[1,0,7,8]),(1,[5,6,8]),(0,[3,4,7]),(3,[5,6]),(4,[5,8]),(5,[]),(6,[7]),(7,[]),(8,[])], (2, ![5,2,8,3,0,6,7,4,1])),
    ([(2,[1,0,7,8]),(1,[5,6,8]),(0,[3,4,7]),(3,[5,6]),(4,[6,8]),(5,[7]),(6,[]),(7,[]),(8,[])], (2, ![5,2,8,3,0,7,6,4,1])),
    ([(2,[1,0,7,8]),(1,[5,6,8]),(0,[3,4,7]),(3,[5,8]),(4,[5,6]),(5,[]),(6,[7]),(7,[]),(8,[])], (2, ![5,2,8,0,3,6,7,4,1])),
    ([(2,[1,0,7,8]),(1,[5,6,8]),(0,[3,4,7]),(3,[6,8]),(4,[5,6]),(5,[7]),(6,[]),(7,[]),(8,[])], (2, ![5,2,8,0,3,7,6,4,1])),
    ([(2,[5,6,7,8]),(1,[0,4,7,8]),(0,[3,5,6]),(3,[7,8]),(4,[5,6]),(5,[]),(6,[]),(7,[]),(8,[])], (1, ![8,6,7,5,1,0,2,3,4])),
    ([(2,[1,6,7,8]),(1,[0,5,8]),(0,[3,4,5]),(3,[6,7]),(4,[6,8]),(5,[7]),(6,[]),(7,[]),(8,[])], (2, ![5,8,2,3,0,4,6,7,1])),
    ([(2,[1,6,7,8]),(1,[0,5,8]),(0,[3,4,5]),(3,[6,7]),(4,[7,8]),(5,[6]),(6,[]),(7,[]),(8,[])], (2, ![5,8,2,3,0,4,7,6,1])),
    ([(2,[1,6,7,8]),(1,[0,5,8]),(0,[3,4,5]),(3,[6,8]),(4,[6,7]),(5,[7]),(6,[]),(7,[]),(8,[])], (2, ![5,8,2,0,3,4,6,7,1])),
    ([(2,[1,6,7,8]),(1,[0,5,8]),(0,[3,4,5]),(3,[7,8]),(4,[6,7]),(5,[6]),(6,[]),(7,[]),(8,[])], (2, ![5,8,2,0,3,4,7,6,1])),
    ([(2,[0,6,7,8]),(1,[0,3,4,5]),(0,[5,8]),(3,[6,7]),(4,[6,8]),(5,[7]),(6,[]),(7,[]),(8,[])], (2, ![8,5,2,3,0,4,6,7,1])),
    ([(2,[0,6,7,8]),(1,[0,3,4,5]),(0,[5,8]),(3,[6,7]),(4,[7,8]),(5,[6]),(6,[]),(7,[]),(8,[])], (2, ![8,5,2,3,0,4,7,6,1])),
    ([(2,[0,6,7,8]),(1,[0,3,4,5]),(0,[5,8]),(3,[6,8]),(4,[6,7]),(5,[7]),(6,[]),(7,[]),(8,[])], (2, ![8,5,2,0,3,4,6,7,1])),
    ([(2,[0,6,7,8]),(1,[0,3,4,5]),(0,[5,8]),(3,[7,8]),(4,[6,7]),(5,[6]),(6,[]),(7,[]),(8,[])], (2, ![8,5,2,0,3,4,7,6,1]))]

private theorem witness_ok (i : Fin 16) :
    Function.Bijective (witness i).2.2 ∧
    ∀ a b : Axis, b ∈ neighbors (witness i).1 a ↔
      (recipeGraph (witness i).2.1).Adj ((witness i).2.2 a) ((witness i).2.2 b) := by
  fin_cases i <;> decide +kernel

private def survivors (k : Fin 3) : List Rows :=
  (scan (keepPrefix k) (order k) (degrees k) []).filter (passes k)

set_option maxHeartbeats 0 in
private theorem finite_cover (k : Fin 3) (hk : k ≠ 0) :
    (survivors k).length = (![0,0,16] : Fin 3 → ℕ) k ∧
    (survivors k).all (fun rows => (List.finRange 16).any
      (fun i => decide ((witness i).1 = rows))) = true := by
  fin_cases k
  · exact (hk rfl).elim
  · decide +kernel
  · decide +kernel

private theorem classify_sorted (k : Fin 3) (hk : k ≠ 0) (G : SimpleGraph Axis) [DecidableRel G.Adj]
    (hd : ∀ a, G.degree a = degrees k a)
    (hs : ∀ a b : Axis, high k ≤ a.val → a ≤ b → sig k G a ≤ sig k G b)
    (hl : LocalLaws G) : ∃ kind, Nonempty (G ≃g recipeGraph kind) := by
  have hset : (order k).toFinset = univ := by
    ext a
    simp [(order_ok k).2 a]
  have hdeg (a : Axis) (ha : a ∈ (order k).toFinset) :
      degrees k a = ((order k).toFinset.filter (G.Adj a)).card := by
    rw [← hd a, hset, ← SimpleGraph.neighborFinset_eq_filter, G.card_neighborFinset_eq_degree]
  obtain ⟨E, hE, hcover⟩ := Q9DegreeRows.complete G (order k) (order_ok k).1 (degrees k) hdeg
  let rows := encode G (order k)
  have hm : rows ∈ survivors k := by
    apply List.mem_filter.mpr
    refine ⟨?_, passes_of_laws k G hd hl⟩
    have hh := scan_complete (keepPrefix k) G (order k) (order_ok k).1
      (degrees k) [] hE hcover (fun p q he => by
        simpa only [List.nil_append] using keep_of_sorted k G hs he)
    simpa only [List.nil_append, rows] using hh
  obtain ⟨i, _, hi⟩ := List.any_eq_true.mp (List.all_eq_true.mp (finite_cover k hk).2 rows hm)
  have he : (witness i).1 = rows := of_decide_eq_true hi
  obtain ⟨hbij, hadj⟩ := witness_ok i
  refine ⟨(witness i).2.1, ⟨{ toEquiv := Equiv.ofBijective _ hbij, map_rel_iff' := ?_ }⟩⟩
  intro a b
  specialize hadj a b
  rw [he] at hadj
  have hrow : b ∈ neighbors rows a ↔ G.Adj a b := by
    simpa only [(order_ok k).2 a, (order_ok k).2 b, true_and] using
      mem_neighbors_encode G (order k) a b
  exact hadj.symm.trans hrow

private def blocks (k : Fin 3) : Fin (high k) ⊕ Fin (9 - high k) ≃ Axis :=
  finSumFinEquiv.trans (finCongr (by
    have hk := k.isLt
    unfold high
    omega))

private theorem high_degrees (k : Fin 3) (d : Fin (high k) → ℕ)
    (hp : ∀ i, 3 < d i) (hs : ∑ i, (d i - 3) = 3) (hm : Monotone d) :
    ∀ i, d i = degrees k (blocks k (Sum.inl i)) := by
  revert d
  fin_cases k
  · intro d hp hs _ i
    have h0 : d 0 = 6 := by
      have hx : d 0 - 3 = 3 := by
        change (∑ i : Fin 1, (d i - 3)) = 3 at hs
        simpa only [Fin.sum_univ_one] using hs
      have h0 := hp 0
      omega
    fin_cases i
    exact h0
  · intro d hp hs hm i
    have hx : (d 0 - 3) + (d 1 - 3) = 3 := by
      change (∑ i : Fin 2, (d i - 3)) = 3 at hs
      simpa only [Fin.sum_univ_two] using hs
    have h0 := hp 0
    have h1 := hp 1
    have h01 := hm (by decide : (0 : Fin 2) ≤ 1)
    have he0 : d 0 = 4 := by omega
    have he1 : d 1 = 5 := by omega
    fin_cases i
    · exact he0
    · exact he1
  · intro d hp hs _ i
    have hx : (d 0 - 3) + (d 1 - 3) + (d 2 - 3) = 3 := by
      change (∑ i : Fin 3, (d i - 3)) = 3 at hs
      simpa only [Fin.sum_univ_three] using hs
    have h0 := hp 0
    have h1 := hp 1
    have h2 := hp 2
    have he0 : d 0 = 4 := by omega
    have he1 : d 1 = 4 := by omega
    have he2 : d 2 = 4 := by omega
    fin_cases i
    · exact he0
    · exact he1
    · exact he2

private theorem sig_sum (k : Fin 3) (hk : k ≠ 0) (G : SimpleGraph Axis) [DecidableRel G.Adj] (a : Axis) :
    sig k G a = ∑ i : Fin (high k),
      if G.Adj (blocks k (Sum.inl i)) a then 2 ^ i.val else 0 := by
  fin_cases k
  · exact (hk rfl).elim
  · simp [sig, score, high, blocks, finSumFinEquiv, Fin.castAdd,
      Fin.sum_univ_two, Fin.sum_univ_three]
  · simp [sig, score, high, blocks, finSumFinEquiv, Fin.castAdd,
      Fin.sum_univ_two, Fin.sum_univ_three]

private theorem classify_blocks (k : Fin 3) (hk : k ≠ 0) (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Fin (high k) ⊕ Fin (9 - high k) ≃ V)
    (hsum : ∑ v : V, (G.degree v - 3) = 3)
    (hH : ∀ i, 3 < G.degree (e (Sum.inl i))) (hL : ∀ j, G.degree (e (Sum.inr j)) = 3)
    (hord : Monotone (fun i => G.degree (e (Sum.inl i))))
    (hsig : Monotone (fun j => ∑ i : Fin (high k),
      if G.Adj (e (Sum.inl i)) (e (Sum.inr j)) then 2 ^ i.val else 0))
    (hl : LocalLaws G) : ∃ kind, Nonempty (recipeGraph kind ≃g G) := by
  let labels := (blocks k).symm.trans e
  let K := G.comap labels
  let iso : K ≃g G := SimpleGraph.Iso.comap labels G
  have hd (s : Fin (high k) ⊕ Fin (9 - high k)) :
      K.degree (blocks k s) = G.degree (e s) := by
    have heq : iso (blocks k s) = e s := by
      change labels (blocks k s) = e s
      simp [labels]
    rw [← heq]
    exact (iso.degree_eq (blocks k s)).symm
  have hex : (∑ i : Fin (high k), (G.degree (e (Sum.inl i)) - 3)) = 3 := by
    have he := e.sum_comp (fun v => G.degree v - 3)
    rw [Fintype.sum_sum_type, hsum] at he
    have hz : (∑ j : Fin (9 - high k), (G.degree (e (Sum.inr j)) - 3)) = 0 := by
      simp [hL]
    simpa only [hz, add_zero] using he
  have hdeg (a : Axis) : K.degree a = degrees k a := by
    obtain ⟨s, rfl⟩ := (blocks k).surjective a
    rw [hd s]
    cases s with
    | inl i => exact high_degrees k _ hH hex hord i
    | inr j =>
      rw [hL j]
      exact ((cubic_iff k _).mpr (by change high k ≤ high k + j.val; omega)).symm
  have right (a : Axis) (ha : high k ≤ a.val) :
      ∃ j, blocks k (Sum.inr j) = a := by
    obtain ⟨s, rfl⟩ := (blocks k).surjective a
    cases s with
    | inl i =>
      change high k ≤ i.val at ha
      exact (Nat.not_le_of_lt i.isLt ha).elim
    | inr j => exact ⟨j, rfl⟩
  have hsort (a b : Axis) (ha : high k ≤ a.val) (hab : a ≤ b) :
      sig k K a ≤ sig k K b := by
    have hb : high k ≤ b.val := ha.trans (show a.val ≤ b.val from hab)
    obtain ⟨i, rfl⟩ := right a ha
    obtain ⟨j, rfl⟩ := right b hb
    have hij : i ≤ j := by
      change high k + i.val ≤ high k + j.val at hab
      exact Nat.le_of_add_le_add_left hab
    have hsig_eq (a : Fin (9 - high k)) : sig k K (blocks k (Sum.inr a)) =
        ∑ i : Fin (high k), if G.Adj (e (Sum.inl i)) (e (Sum.inr a)) then 2 ^ i.val else 0 := by
      rw [sig_sum k hk]
      apply sum_congr rfl
      intro i _
      have ha : K.Adj (blocks k (Sum.inl i)) (blocks k (Sum.inr a)) ↔
          G.Adj (e (Sum.inl i)) (e (Sum.inr a)) := by
        change G.Adj (labels (blocks k (Sum.inl i))) (labels (blocks k (Sum.inr a))) ↔ _
        simp [labels]
      simp only [ha]
    rw [hsig_eq, hsig_eq]
    exact hsig hij
  obtain ⟨kind, ⟨p⟩⟩ := classify_sorted k hk K hdeg hsort (laws_of_iso iso hl)
  exact ⟨kind, ⟨RelIso.trans p.symm iso⟩⟩

/-- The four local laws force a fifteen-edge graph on nine vertices of
minimum degree three to be isomorphic to one of the three recipe graphs. -/
theorem fifteen_edges_on_nine_vertices (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = 9) (hE : G.edgeFinset.card = 15)
    (hmin : ∀ v, 3 ≤ G.degree v) (hl : LocalLaws G) :
    ∃ kind : Fin 3, Nonempty (recipeGraph kind ≃g G) := by
  obtain ⟨h, l, e, hp, hm, hhl, hH, hL, hord, hsig⟩ :=
    Q9FifteenMaskNineAxisProfile.sorted_degree_blocks G hV hE hmin
  have hs := Q9FifteenMaskNineAxisProfile.excess_sum G hV hE hmin
  have hc : (h = 1 ∧ l = 8) ∨ (h = 2 ∧ l = 7) ∨ (h = 3 ∧ l = 6) := by omega
  rcases hc with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · -- The unique high vertex has degree six. Its independent cubic
    -- neighborhood has too few vertices outside it to use all remaining edges.
    have hx : G.degree (e (Sum.inl 0)) - 3 = 3 := by
      have he := e.sum_comp (fun v => G.degree v - 3)
      rw [Fintype.sum_sum_type, hs] at he
      simpa [Fin.sum_univ_one, hL] using he
    have hdeg : G.degree (e (Sum.inl 0)) = 6 := by
      have := hH 0
      omega
    have hcubic (x : V) (hne : x ≠ e (Sum.inl 0)) : G.degree x = 3 := by
      obtain ⟨s,rfl⟩ := e.surjective x
      cases s with
      | inl i => fin_cases i; exact (hne rfl).elim
      | inr j => exact hL j
    have hbound := Q9CubicContactHighBlock.unique_high_degree_bound
      (G := G) (hH 0) hcubic hl.secondNeighbor hl.noCubicTriangle
    rw [hdeg, hV] at hbound
    omega
  · exact classify_blocks 1 (by decide) G e hs hH hL hord hsig hl
  · exact classify_blocks 2 (by decide) G e hs hH hL hord hsig hl

/-- The representatives are distinguished by the presence of an edge and
of a two-edge path among their degree-four vertices. -/
theorem recipeGraph_distinct (i j : Fin 3) (hne : i ≠ j) :
    ¬ Nonempty (recipeGraph i ≃g recipeGraph j) := by
  let edge (G : SimpleGraph Axis) [DecidableRel G.Adj] : Prop :=
    ∃ a b, G.degree a = 4 ∧ G.degree b = 4 ∧ G.Adj a b
  let wedge (G : SimpleGraph Axis) [DecidableRel G.Adj] : Prop :=
    ∃ a b c, a ≠ c ∧ G.degree a = 4 ∧ G.degree b = 4 ∧ G.degree c = 4 ∧
      G.Adj a b ∧ G.Adj b c
  have edge_map {a b : Fin 3} (p : recipeGraph a ≃g recipeGraph b)
      (h : edge (recipeGraph a)) : edge (recipeGraph b) := by
    obtain ⟨x,y,hx,hy,hxy⟩ := h
    exact ⟨p x, p y, (p.degree_eq x).trans hx, (p.degree_eq y).trans hy, p.map_adj_iff.mpr hxy⟩
  have wedge_map {a b : Fin 3} (p : recipeGraph a ≃g recipeGraph b)
      (h : wedge (recipeGraph a)) : wedge (recipeGraph b) := by
    obtain ⟨x,y,z,hxz,hx,hy,hz,hxy,hyz⟩ := h
    exact ⟨p x, p y, p z, p.injective.ne hxz, (p.degree_eq x).trans hx, (p.degree_eq y).trans hy,
      (p.degree_eq z).trans hz, p.map_adj_iff.mpr hxy, p.map_adj_iff.mpr hyz⟩
  have hprofile : ∀ a b : Fin 3,
      (edge (recipeGraph a) ↔ edge (recipeGraph b)) →
      (wedge (recipeGraph a) ↔ wedge (recipeGraph b)) → a = b := by
    dsimp [edge, wedge]
    decide +kernel
  rintro ⟨p⟩
  exact hne (hprofile i j ⟨edge_map p, edge_map p.symm⟩ ⟨wedge_map p, wedge_map p.symm⟩)

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open Q9MinimumDistanceOperator (minimumDisplacements)
open Q9SquareMaskGraph (activeAxes maskGraph card_edges distance_two_mask_graph_constraints)
open Q9SharedContactNormalized (LocalRules)
open Q9WeightedSaturation (defect signedBiadjacency)
open private mem_minimumDisplacements from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator
open private mem_axes from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.MinimumContactDisplacementCount

open Classical in
/-- The generic classification applies to the actual contact graph via the
four previously established local geometric laws. -/
theorem classify_contact_graph {C D : Finset (Q 9)} {b : Bool}
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcC : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hdetC : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w C false)).det = 0)
    (hdetD : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w D false)).det = 0)
    (hlC : LocalRules C) (hlD : LocalRules D)
    (haxes : (activeAxes (minimumDisplacements C D b 2)).card = 9)
    (hcard : (minimumDisplacements C D b 2).card = 15) :
    ∃ kind : Fin 3, Nonempty (recipeGraph kind ≃g maskGraph (minimumDisplacements C D b 2)) := by
  let F := minimumDisplacements C D b 2
  let G := maskGraph F
  have hsize (T : Finset Axis) (hT : T ∈ F) : T.card = 2 := by
    obtain ⟨_, _, _, _, _, ht, rfl⟩ := mem_minimumDisplacements.mp hT
    exact ht
  have hV : Fintype.card (activeAxes F) = 9 := (Fintype.card_coe _).trans haxes
  have hE : G.edgeFinset.card = 15 := (card_edges F hsize).trans hcard
  obtain ⟨hmin, hsq⟩ := distance_two_mask_graph_constraints (b := b)
    hsep hrC hrD hcC hcD hbC hbD hdetC hdetD
  apply fifteen_edges_on_nine_vertices G hV hE hmin
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a v c
    exact hsq
  · intro a v c hav ha hv hac hvc
    exact Q9ContactGraphTriangles.cubic_edge_common_neighbor_has_companion (b := b)
      hsep hrC hrD hcC hcD hbC hbD hdetC hdetD hav ha hv hac hvc
  · exact Q9CubicTriangleExclusion.no_cubic_contact_triangle (b := b)
      hsep hrC hrD hcC hcD hbC hbD hdetC hdetD
  · intro a c hac
    obtain ⟨p,q,hpa,hqc,hpc,hqa,hpq,hp,hq,hpq'⟩ :=
      Q9EveryContactEdgeSquare.every_realized_mask_on_four_cycle hlC hlD hsep hac.2
    let x : activeAxes F := ⟨p, mem_axes.mpr ⟨_, hp, by simp⟩⟩
    let y : activeAxes F := ⟨q, mem_axes.mpr ⟨_, hq, by simp⟩⟩
    refine ⟨y, ?_, ?_, x, ?_, ?_, ?_⟩
    · exact ⟨fun he => hqa (congrArg Subtype.val he).symm, hq⟩
    · exact fun he => hqc (congrArg Subtype.val he)
    · exact fun he => hpa (congrArg Subtype.val he)
    · refine ⟨fun he => hpc (congrArg Subtype.val he).symm, ?_⟩
      change ({c.val,p} : Finset Axis) ∈ F
      rw [Finset.pair_comm]
      exact hp
    · refine ⟨fun he => hpq (congrArg Subtype.val he).symm, ?_⟩
      change ({q,p} : Finset Axis) ∈ F
      rw [Finset.pair_comm]
      exact hpq' 

#print axioms fifteen_edges_on_nine_vertices
#print axioms recipeGraph_distinct
#print axioms classify_contact_graph

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FifteenMaskNineAxisClassification
