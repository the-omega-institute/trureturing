/- GID: D5/S3/Combinatorics/Graph/Triameter/CliqueChains
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Triameter/CliqueChains
   mirror-E: none(waiver:universal-finite-graph-theorem)
   anchors: []
   utility: none
   digest: Equality in the triameter-independence bound characterizes three chains of split cliques at a common central clique. -/

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Triameter and chains of split cliques

A perimeter triple projects to the feet of three legs attached to a point or a triangle.
The packing bound forces a triangular centre and even leg lengths at equality for independence.
The preimages of the central triangle and successive pairs of positive depths are cliques.
-/

namespace D5.S3.Combinatorics.Graph.Triameter

namespace EvenLegTriangle

/-- A vertex on leg `i` has depth between zero and `2 * q i`, inclusive. -/
abbrev Vertex (q : Fin 3 → ℕ) := Σ i : Fin 3, Fin (2 * q i + 1)

/-- Consecutive depths on each leg are joined, and the three roots form a triangle. -/
private def H (q : Fin 3 → ℕ) : SimpleGraph (Vertex q) where
  Adj x y :=
    (x.1 = y.1 ∧ (x.2.val + 1 = y.2.val ∨ y.2.val + 1 = x.2.val)) ∨
      (x.1 ≠ y.1 ∧ x.2.val = 0 ∧ y.2.val = 0)
  symm := by
    constructor
    intro x y h
    rcases h with ⟨hleg, hstep⟩ | ⟨hleg, hx, hy⟩
    · exact Or.inl ⟨hleg.symm, hstep.symm⟩
    · exact Or.inr ⟨Ne.symm hleg, hy, hx⟩
  loopless := by
    constructor
    intro x h
    rcases h with ⟨_, h | h⟩ | ⟨h, _, _⟩
    · omega
    · omega
    · exact h rfl

local instance (q : Fin 3 → ℕ) : DecidableRel (H q).Adj := fun x y => by
  change Decidable
    ((x.1 = y.1 ∧ (x.2.val + 1 = y.2.val ∨ y.2.val + 1 = x.2.val)) ∨
      (x.1 ≠ y.1 ∧ x.2.val = 0 ∧ y.2.val = 0))
  infer_instance

/-- The two vertices of block `t` on leg `i`. -/
private def peripheralBlock (q : Fin 3 → ℕ) (i : Fin 3) (t : ℕ) (ht : t ≤ q i) :
    Finset (Vertex q) :=
  {⟨i, ⟨2 * t - 1, by omega⟩⟩, ⟨i, ⟨2 * t, by omega⟩⟩}

private abbrev BlockIndex (q : Fin 3 → ℕ) := Σ i : Fin 3, Fin (q i)

private theorem sigma_fin_ext {n : Fin 3 → ℕ} {x y : Σ i : Fin 3, Fin (n i)}
    (hleg : x.1 = y.1) (hval : x.2.val = y.2.val) : x = y := by
  obtain ⟨i, a⟩ := x
  obtain ⟨j, b⟩ := y
  change i = j at hleg
  subst j
  exact congrArg (Sigma.mk i) (Fin.ext hval)

private theorem apart_of_depth_gap {q : Fin 3 → ℕ} {x y : Vertex q}
    (hgap : x.2.val + 2 ≤ y.2.val) : x ≠ y ∧ ¬ (H q).Adj x y := by
  constructor
  · rintro rfl
    omega
  · rintro (⟨_, h | h⟩ | ⟨_, _, h⟩) <;> omega

private theorem apart_of_different_legs {q : Fin 3 → ℕ} {x y : Vertex q}
    (hleg : x.1 ≠ y.1) (hpos : 0 < x.2.val ∨ 0 < y.2.val) :
    x ≠ y ∧ ¬ (H q).Adj x y := by
  constructor
  · rintro rfl
    exact hleg rfl
  · rintro (⟨h, _⟩ | ⟨_, hx, hy⟩)
    · exact hleg h
    · omega

/-- Every marked peripheral block has one companion per peripheral block overall. -/
private theorem peripheral_companions (q : Fin 3 → ℕ) (i : Fin 3) (t : ℕ)
    (ht₀ : 1 ≤ t) (ht : t ≤ q i) :
    ∃ A : Finset (Vertex q),
      A.card = q 0 + q 1 + q 2 ∧
      (H q).IsIndepSet (↑A : Set (Vertex q)) ∧
      ∀ x ∈ A, ∀ y ∈ peripheralBlock q i t ht, x ≠ y ∧ ¬ (H q).Adj x y := by
  obtain ⟨j, hji⟩ := exists_ne i
  let mark : BlockIndex q := ⟨i, ⟨t - 1, by omega⟩⟩
  let root : Vertex q := ⟨j, ⟨0, by omega⟩⟩
  -- Use odd depths before the mark and even depths after it or on other legs.
  let depth (b : BlockIndex q) : ℕ :=
    if b.1 = i ∧ b.2.val + 1 < t then 2 * b.2.val + 1 else 2 * b.2.val + 2
  let regular (b : BlockIndex q) : Vertex q :=
    ⟨b.1, ⟨depth b, by
      have hb := b.2.isLt
      dsimp only [depth]
      split <;> omega⟩⟩
  have depth_pos (b : BlockIndex q) : 0 < depth b := by
    dsimp only [depth]
    split <;> omega
  have depth_gap {a b : BlockIndex q} (hleg : a.1 = b.1)
      (hlt : a.2.val < b.2.val) : depth a + 2 ≤ depth b := by
    dsimp only [depth]
    by_cases ha : a.1 = i ∧ a.2.val + 1 < t
    · rw [ite_eq_left ha]
      split <;> omega
    · have hb : ¬ (b.1 = i ∧ b.2.val + 1 < t) := by
        rintro ⟨hbi, hbt⟩
        exact ha ⟨hleg.trans hbi, by omega⟩
      rw [ite_eq_right ha, ite_eq_right hb]
      omega
  have regular_apart {a b : BlockIndex q} (hab : a ≠ b) :
      regular a ≠ regular b ∧ ¬ (H q).Adj (regular a) (regular b) := by
    by_cases hleg : a.1 = b.1
    · have hval : a.2.val ≠ b.2.val := fun h => hab (sigma_fin_ext hleg h)
      rcases lt_or_gt_of_ne hval with hlt | hgt
      · exact apart_of_depth_gap (depth_gap hleg hlt)
      · obtain ⟨hne, hna⟩ :=
          apart_of_depth_gap (q := q) (x := regular b) (y := regular a)
            (depth_gap hleg.symm hgt)
        exact ⟨Ne.symm hne, fun h => hna h.symm⟩
    · exact apart_of_different_legs hleg (Or.inl (depth_pos a))
  have root_apart (b : BlockIndex q) :
      root ≠ regular b ∧ ¬ (H q).Adj root (regular b) := by
    by_cases hleg : j = b.1
    · have hbi : b.1 ≠ i := hleg ▸ hji
      apply apart_of_depth_gap
      change 0 + 2 ≤ depth b
      simp [depth, hbi]
    · exact apart_of_different_legs hleg (Or.inr (depth_pos b))
  -- The marked block's index instead supplies the root on the other leg.
  let select (b : BlockIndex q) : Vertex q :=
    if b = mark then root else regular b
  have select_apart {a b : BlockIndex q} (hab : a ≠ b) :
      select a ≠ select b ∧ ¬ (H q).Adj (select a) (select b) := by
    by_cases ha : a = mark
    · have hb : b ≠ mark := fun hb => hab (ha.trans hb.symm)
      simpa [select, ha, hb] using root_apart b
    · by_cases hb : b = mark
      · obtain ⟨hne, hna⟩ := root_apart a
        simpa [select, ha, hb] using
          show regular a ≠ root ∧ ¬ (H q).Adj (regular a) root from
            ⟨Ne.symm hne, fun h => hna h.symm⟩
      · simpa [select, ha, hb] using regular_apart hab
  have select_remote (b : BlockIndex q) (y : Vertex q)
      (hy : y ∈ peripheralBlock q i t ht) :
      select b ≠ y ∧ ¬ (H q).Adj (select b) y := by
    have hy_coords : y.1 = i ∧ (y.2.val = 2 * t - 1 ∨ y.2.val = 2 * t) := by
      simp only [peripheralBlock, Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact ⟨rfl, Or.inl rfl⟩
      · exact ⟨rfl, Or.inr rfl⟩
    obtain ⟨hy_leg, hy_depth⟩ := hy_coords
    by_cases hb : b = mark
    · simp only [select, ite_eq_left hb]
      exact apart_of_different_legs (fun h => hji (h.trans hy_leg))
        (Or.inr (by omega))
    · simp only [select, ite_eq_right hb]
      by_cases hbi : b.1 = i
      · have hindex : b.2.val + 1 ≠ t := by
          intro h
          apply hb
          exact sigma_fin_ext hbi (show b.2.val = t - 1 by omega)
        by_cases hbefore : b.2.val + 1 < t
        · apply apart_of_depth_gap
          change depth b + 2 ≤ y.2.val
          have hcond : b.1 = i ∧ b.2.val + 1 < t := ⟨hbi, hbefore⟩
          simp only [depth, ite_eq_left hcond]
          omega
        · have hcond : ¬ (b.1 = i ∧ b.2.val + 1 < t) := fun h => hbefore h.2
          have hgap : y.2.val + 2 ≤ (regular b).2.val := by
            change y.2.val + 2 ≤ depth b
            simp only [depth, ite_eq_right hcond]
            omega
          obtain ⟨hne, hna⟩ := apart_of_depth_gap hgap
          exact ⟨Ne.symm hne, fun h => hna h.symm⟩
      · exact apart_of_different_legs (fun h => hbi (h.trans hy_leg))
          (Or.inl (depth_pos b))
  let embedding : BlockIndex q ↪ Vertex q :=
    ⟨select, fun _ _ h => by
      by_contra hne
      exact (select_apart hne).1 h⟩
  refine ⟨Finset.univ.map embedding, ?_, ?_, ?_⟩
  · rw [Finset.card_map]
    change (Finset.univ.sigma fun i : Fin 3 => (Finset.univ : Finset (Fin (q i)))).card =
      q 0 + q 1 + q 2
    simp [Fin.sum_univ_three]
  · rw [SimpleGraph.isIndepSet_iff]
    intro x hx y hy hxy
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hx)
    obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hy)
    exact (select_apart (fun h => hxy (congrArg embedding h))).2
  · intro x hx y hy
    obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp hx
    exact select_remote b y hy

end EvenLegTriangle

open SimpleGraph

open SimpleGraph

private noncomputable def packingConflict {V : Type*} (G : SimpleGraph V) (k : ℕ) :
    SimpleGraph V where
  Adj x y := x ≠ y ∧ G.dist x y ≤ k
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, dist_comm ▸ h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- On a connected graph, this is the maximum size of a set with all distances greater than k. -/
private noncomputable def packingNum {V : Type*} (G : SimpleGraph V) (k : ℕ) : ℕ :=
  (packingConflict G k).indepNum

private theorem packingNum_one {V : Type*} {G : SimpleGraph V} (hc : G.Connected) :
    packingNum G 1 = G.indepNum := by
  suffices packingConflict G 1 = G by rw [packingNum, this]
  ext x y
  change x ≠ y ∧ G.dist x y ≤ 1 ↔ G.Adj x y
  constructor
  · intro ⟨hne, h⟩
    have hp := hc.pos_dist_of_ne hne
    exact dist_eq_one_iff_adj.mp (by omega)
  · intro h
    exact ⟨h.ne, (dist_eq_one_iff_adj.mpr h).le⟩

private theorem packing_card_le {V I : Type*} [Finite V] [Fintype I]
    (G : SimpleGraph V) (k : ℕ) (f : I → V)
    (h : ∀ i j, i ≠ j → k < G.dist (f i) (f j)) :
    Fintype.card I ≤ packingNum G k := by
  classical
  let emb : I ↪ V := ⟨f, fun i j he => by
    by_contra hn
    have hh := h i j hn
    simp [he] at hh⟩
  let s := Finset.univ.map emb
  have hs : (packingConflict G k).IsIndepSet (s : Set V) := by
    rw [isIndepSet_iff]
    intro x hx y hy hxy hadj
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hx)
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hy)
    have hij : i ≠ j := fun he => hxy (congrArg emb he)
    exact (Nat.not_le_of_lt (h i j hij)) hadj.2
  simpa only [s, Finset.card_map, Finset.card_univ, packingNum] using hs.card_le_indepNum

private theorem packingNum_le_of_surjective_nonexpanding {V W : Type*} [Finite V]
    {G : SimpleGraph V} {H : SimpleGraph W} (k : ℕ) {f : V → W}
    (hs : Function.Surjective f) (hn : ∀ x y, H.dist (f x) (f y) ≤ G.dist x y) :
    packingNum H k ≤ packingNum G k := by
  classical
  obtain ⟨s, hs'⟩ := (packingConflict H k).exists_isNIndepSet_indepNum
  let g : ↥s → V := fun v => (hs v.val).choose
  have hg (v : ↥s) : f (g v) = v.val := (hs v.val).choose_spec
  have hp (x y : ↥s) (hxy : x ≠ y) : k < G.dist (g x) (g y) := by
    have hne : x.val ≠ y.val := fun he => hxy (Subtype.ext he)
    have hi := hs'.isIndepSet
    rw [isIndepSet_iff] at hi
    have hbad := hi (Finset.mem_coe.mpr x.property) (Finset.mem_coe.mpr y.property) hne
    have hlt : k < H.dist x.val y.val := by
      by_contra! hle
      exact hbad ⟨hne, hle⟩
    have hle := hn (g x) (g y)
    rw [hg, hg] at hle
    exact hlt.trans_le hle
  have hcard := packing_card_le G k g hp
  rw [Fintype.card_coe, hs'.card_eq] at hcard
  exact hcard

private abbrev OuterIndex (k : ℕ) (L : Fin 3 → ℕ) :=
  Σ i : Fin 3, Fin (L i / (k + 1))

private def outerDepth {k : ℕ} {L : Fin 3 → ℕ} (x : OuterIndex k L) : ℕ :=
  L x.1 % (k + 1) + (k + 1) * (x.2.val + 1)

private theorem outerDepth_le {k : ℕ} {L : Fin 3 → ℕ} (x : OuterIndex k L) :
    outerDepth x ≤ L x.1 := by
  unfold outerDepth
  have h := Nat.mul_le_mul_left (k + 1) (Nat.succ_le_of_lt x.2.isLt)
  change (k + 1) * (x.2.val + 1) ≤ (k + 1) * (L x.1 / (k + 1)) at h
  have hdiv := Nat.mod_add_div (L x.1) (k + 1)
  omega

private def outer {e k : ℕ} {L : Fin 3 → ℕ} (x : OuterIndex k L) : SpiderVertex e L :=
  point x.1 (outerDepth x) (outerDepth_le x)

private def inner (e k : ℕ) (L : Fin 3 → ℕ) (i : Fin 3) : SpiderVertex e L :=
  point i (L i % (k + 1)) (Nat.mod_le ..)

private theorem outer_separated {e k : ℕ} {L : Fin 3 → ℕ} {x y : OuterIndex k L} (hxy : x ≠ y) :
    k < spiderDist (outer (e := e) x) (outer y) := by
  unfold outer
  rw [spiderDist_point]
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left (show i = i from rfl)]
    have hne : x.val ≠ y.val := fun h => hxy (congrArg (Sigma.mk i) (Fin.ext h))
    rcases lt_or_gt_of_ne hne with h | h
    · have hgap := Nat.mul_le_mul_left (k + 1) (Nat.succ_le_of_lt (Nat.succ_lt_succ h))
      simp only [← Nat.add_one, Nat.mul_add, Nat.mul_one] at hgap
      simp only [outerDepth]
      simp only [Nat.mul_add, Nat.mul_one]
      omega
    · have hgap := Nat.mul_le_mul_left (k + 1) (Nat.succ_le_of_lt (Nat.succ_lt_succ h))
      simp only [← Nat.add_one, Nat.mul_add, Nat.mul_one] at hgap
      simp only [outerDepth]
      simp only [Nat.mul_add, Nat.mul_one]
      omega
  · rw [ite_eq_right hij]
    dsimp [outerDepth]
    rw [Nat.mul_succ]
    omega

private theorem outer_inner_separated {e k : ℕ} {L : Fin 3 → ℕ} (x : OuterIndex k L) (j : Fin 3) :
    k < spiderDist (outer (e := e) x) (inner e k L j) := by
  unfold outer inner
  rw [spiderDist_point]
  rcases x with ⟨i, x⟩
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left (show i = i from rfl)]
    dsimp [outerDepth]
    rw [Nat.mul_succ]
    omega
  · rw [ite_eq_right hij]
    dsimp [outerDepth]
    rw [Nat.mul_succ]
    omega

private theorem spider_packing_lower {e : ℕ} (he : e ≤ 1) (k : ℕ) (L : Fin 3 → ℕ)
    (C : Finset (Fin 3))
    (hC : ∀ i ∈ C, ∀ j ∈ C, i ≠ j → k < L i % (k + 1) + L j % (k + 1) + e) :
    L 0 / (k + 1) + L 1 / (k + 1) + L 2 / (k + 1) + C.card ≤
      packingNum (spider e L) k := by
  let select : OuterIndex k L ⊕ ↥C → SpiderVertex e L :=
    Sum.elim outer (fun i => inner e k L i.val)
  have hsep (x y : OuterIndex k L ⊕ ↥C) (hxy : x ≠ y) :
      k < (spider e L).dist (select x) (select y) := by
    rw [spider_dist_eq he]
    rcases x with x | x <;> rcases y with y | y
    · exact outer_separated (fun h => hxy (congrArg Sum.inl h))
    · exact outer_inner_separated x y.val
    · change k < spiderDist (inner e k L x.val) (outer y)
      rw [spiderDist_comm]
      exact outer_inner_separated y x.val
    · have hne : x.val ≠ y.val := fun h => hxy (congrArg Sum.inr (Subtype.ext h))
      change k < spiderDist (inner e k L x.val) (inner e k L y.val)
      rw [inner, inner, spiderDist_point, ite_eq_right hne]
      exact hC x.val x.property y.val y.property hne
  have h := packing_card_le (spider e L) k select hsep
  simpa [OuterIndex, Fintype.card_sigma, Fin.sum_univ_three] using h

private theorem spider_packing_bound {e : ℕ} (he : e ≤ 1) (k : ℕ) (L : Fin 3 → ℕ)
    (m : ℕ) (hm : packingNum (spider e L) k ≤ m) :
    let p := 2 * (L 0 + L 1 + L 2) + 3 * e
    let Q := L 0 / (k + 1) + L 1 / (k + 1) + L 2 / (k + 1)
    p + 2 ≤ 2 * (k + 1) * m + k ∧
      (p + 2 = 2 * (k + 1) * m + k →
        m = Q + 1 ∧
        (∀ i j : Fin 3, i ≠ j → L i % (k + 1) + L j % (k + 1) + e = k)) := by
  classical
  let s (i : Fin 3) := L i % (k + 1)
  let Q := L 0 / (k + 1) + L 1 / (k + 1) + L 2 / (k + 1)
  let p := 2 * (L 0 + L 1 + L 2) + 3 * e
  let p₀ := 2 * (s 0 + s 1 + s 2) + 3 * e
  let D := 2 * (k + 1)
  have hsum : L 0 + L 1 + L 2 = s 0 + s 1 + s 2 + (k + 1) * Q := by
    have h0 := Nat.mod_add_div (L 0) (k + 1)
    have h1 := Nat.mod_add_div (L 1) (k + 1)
    have h2 := Nat.mod_add_div (L 2) (k + 1)
    dsimp [s, Q]
    simp only [Nat.mul_add]
    omega
  have hdecomp : p = D * Q + p₀ := by
    change 2 * (L 0 + L 1 + L 2) + 3 * e = 2 * (k + 1) * Q + (2 * (s 0 + s 1 + s 2) + 3 * e)
    rw [hsum]
    ring
  have hs (i : Fin 3) : s i ≤ k :=
    Nat.le_of_lt_succ (Nat.mod_lt (L i) (Nat.succ_pos k))
  have pack (C : Finset (Fin 3))
      (hC : ∀ i ∈ C, ∀ j ∈ C, i ≠ j → k < s i + s j + e) : Q + C.card ≤ m :=
    (spider_packing_lower he k L C hC).trans hm
  have one : Q + 1 ≤ m := by
    have h := pack {0} (by simp)
    simpa using h
  have two (i j : Fin 3) (hij : i ≠ j) (h : k < s i + s j + e) : Q + 2 ≤ m := by
    have hC : ∀ x ∈ ({i, j} : Finset (Fin 3)), ∀ y ∈ ({i, j} : Finset (Fin 3)),
        x ≠ y → k < s x + s y + e := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro x (rfl | rfl) y (rfl | rfl) hxy
      · exact (hxy rfl).elim
      · exact h
      · omega
      · exact (hxy rfl).elim
    simpa [hij] using pack {i, j} hC
  have mul_lower (b : ℕ) (hb : Q + b ≤ m) : D * Q + D * b ≤ D * m := by
    rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left D hb
  have strict (b : ℕ) (hb : Q + b ≤ m) (hp : p₀ + 2 < D * b + k) :
      p + 2 < D * m + k := by
    have hl := mul_lower b hb
    omega
  change p + 2 ≤ D * m + k ∧ (p + 2 = D * m + k → m = Q + 1 ∧ _)
  by_cases hall : ∀ i j : Fin 3, i ≠ j → k < s i + s j + e
  · have three : Q + 3 ≤ m := by
      simpa using pack Finset.univ (fun i _ j _ h => hall i j h)
    have hstrict := strict 3 three (by
      have h0 := hs 0
      have h1 := hs 1
      have h2 := hs 2
      dsimp [p₀, D]
      omega)
    exact ⟨hstrict.le, fun heq => (Nat.ne_of_lt hstrict heq).elim⟩
  · by_cases hany : ∃ i j : Fin 3, i ≠ j ∧ k < s i + s j + e
    · obtain ⟨i, j, hij, hj⟩ := hany
      push Not at hall
      obtain ⟨u, v, huv, hclose⟩ := hall
      have hclose' : s 0 + s 1 + e ≤ k ∨ s 0 + s 2 + e ≤ k ∨ s 1 + s 2 + e ≤ k := by
        have swap (i j : Fin 3) (h : s j + s i + e ≤ k) : s i + s j + e ≤ k := by omega
        fin_cases u <;> fin_cases v <;> first
          | exact (huv rfl).elim
          | exact Or.inl hclose
          | exact Or.inr (Or.inl hclose)
          | exact Or.inr (Or.inr hclose)
          | exact Or.inl (swap 0 1 hclose)
          | exact Or.inr (Or.inl (swap 0 2 hclose))
          | exact Or.inr (Or.inr (swap 1 2 hclose))
      have hsmall : p₀ ≤ 4 * k + 1 := by
        have h0 := hs 0
        have h1 := hs 1
        have h2 := hs 2
        dsimp [p₀]
        rcases hclose' with h | h | h <;> omega
      have hstrict := strict 2 (two i j hij hj) (by dsimp [D]; omega)
      exact ⟨hstrict.le, fun heq => (Nat.ne_of_lt hstrict heq).elim⟩
    · have hclose (i j : Fin 3) (hij : i ≠ j) : s i + s j + e ≤ k := by
        by_contra! hlt
        exact hany ⟨i, j, hij, hlt⟩
      have h01 := hclose 0 1 (by decide)
      have h02 := hclose 0 2 (by decide)
      have h12 := hclose 1 2 (by decide)
      have hp₀ : p₀ ≤ 3 * k := by dsimp [p₀]; omega
      have hl := mul_lower 1 one
      simp only [Nat.mul_one] at hl
      have hD : D = 2 * k + 2 := by dsimp [D]; omega
      refine ⟨by omega, ?_⟩
      intro heq
      have hp₀' : p₀ = 3 * k := by omega
      have hm' : m = Q + 1 := by
        by_contra h
        have h₂ : Q + 2 ≤ m := by omega
        have hl₂ := mul_lower 2 h₂
        rw [show D * 2 = D + D by omega] at hl₂
        omega
      refine ⟨hm', ?_⟩
      have e01 : s 0 + s 1 + e = k := by dsimp [p₀] at hp₀'; omega
      have e02 : s 0 + s 2 + e = k := by dsimp [p₀] at hp₀'; omega
      have e12 : s 1 + s 2 + e = k := by dsimp [p₀] at hp₀'; omega
      intro i j hij
      fin_cases i <;> fin_cases j <;> first
        | exact (hij rfl).elim
        | exact e01
        | exact e02
        | exact e12
        | exact (Nat.add_comm (s 1) (s 0) ▸ e01)
        | exact (Nat.add_comm (s 2) (s 0) ▸ e02)
        | exact (Nat.add_comm (s 2) (s 1) ▸ e12)

private theorem graph_packing_bound {V : Type*} [Finite V] {G : SimpleGraph V}
    (hc : G.Connected) (k : ℕ) (a : Fin 3 → V) :
    let L := legLength G a
    let e := perimeter G a % 2
    perimeter G a + 2 ≤ 2 * (k + 1) * packingNum G k + k ∧
      (perimeter G a + 2 = 2 * (k + 1) * packingNum G k + k →
        packingNum G k = L 0 / (k + 1) + L 1 / (k + 1) + L 2 / (k + 1) + 1 ∧
          (∀ i j : Fin 3, i ≠ j → L i % (k + 1) + L j % (k + 1) + e = k)) := by
  dsimp only
  have he : perimeter G a % 2 ≤ 1 := by omega
  obtain ⟨hs, hn, _⟩ := canonical_projection hc a
  have hm := packingNum_le_of_surjective_nonexpanding k hs hn
  have hb := spider_packing_bound he k (legLength G a) (packingNum G k) hm
  have h := perimeter_of_fits (legLength_fits hc a)
  dsimp only at hb
  rw [← h] at hb
  exact hb

noncomputable def triameter {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  Finset.univ.sup (perimeter G)

private theorem perimeter_le_triameter {V : Type*} [Fintype V] (G : SimpleGraph V) (a : Fin 3 → V) :
    perimeter G a ≤ triameter G :=
  Finset.le_sup (Finset.mem_univ a)

private theorem exists_perimeter_eq_triameter {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hc : G.Connected) : ∃ a : Fin 3 → V, perimeter G a = triameter G := by
  let : Nonempty V := hc.nonempty
  obtain ⟨a, _, ha⟩ :=
    Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin 3 → V)) Finset.univ_nonempty (perimeter G)
  exact ⟨a, ha.symm⟩

private theorem triameter_le_packing {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hc : G.Connected) (k : ℕ) :
    triameter G + 2 ≤ 2 * (k + 1) * packingNum G k + k := by
  obtain ⟨a, ha⟩ := exists_perimeter_eq_triameter hc
  exact ha ▸ (graph_packing_bound hc k a).1

private theorem triameter_le_indepNum {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hc : G.Connected) :
    triameter G + 1 ≤ 4 * G.indepNum := by
  have h := triameter_le_packing hc 1
  rw [packingNum_one hc] at h
  omega

private theorem k1_equality_lengths {V : Type*} [Finite V] {G : SimpleGraph V}
    (hc : G.Connected) (a : Fin 3 → V)
    (h : perimeter G a + 1 = 4 * G.indepNum) :
    let L := legLength G a
    let q : Fin 3 → ℕ := fun i => L i / 2
    perimeter G a % 2 = 1 ∧ L = (fun i => 2 * q i) ∧ G.indepNum = q 0 + q 1 + q 2 + 1 := by
  let L := legLength G a
  let e := perimeter G a % 2
  have he : e ≤ 1 := by dsimp [e]; omega
  have hb := (graph_packing_bound hc 1 a).2
  rw [packingNum_one hc] at hb
  obtain ⟨ha, hp⟩ := hb (by omega)
  have h01 : L 0 % 2 + L 1 % 2 + e = 1 := hp 0 1 (by decide)
  have h02 : L 0 % 2 + L 2 % 2 + e = 1 := hp 0 2 (by decide)
  have h12 : L 1 % 2 + L 2 % 2 + e = 1 := hp 1 2 (by decide)
  have hl0 : L 0 = 2 * (L 0 / 2) := by omega
  have hl1 : L 1 = 2 * (L 1 / 2) := by omega
  have hl2 : L 2 = 2 * (L 2 / 2) := by omega
  refine ⟨show e = 1 by omega, ?_, ha⟩
  funext i
  fin_cases i
  · exact hl0
  · exact hl1
  · exact hl2

/-- The equality case of the packing bound admits a projection onto an even-leg triangle. -/
private theorem k1_equality_projection {V : Type*} [Finite V] {G : SimpleGraph V}
    (hc : G.Connected) (a : Fin 3 → V)
    (h : perimeter G a + 1 = 4 * G.indepNum) :
    ∃ (q : Fin 3 → ℕ) (f : V → EvenLegTriangle.Vertex q),
      G.indepNum = q 0 + q 1 + q 2 + 1 ∧
      Function.Surjective f ∧
      (∀ x y, G.Adj x y → f x = f y ∨ (EvenLegTriangle.H q).Adj (f x) (f y)) ∧
      (∀ u v, (EvenLegTriangle.H q).Adj u v → ∃ x y, G.Adj x y ∧ f x = u ∧ f y = v) := by
  let L := legLength G a
  let q : Fin 3 → ℕ := fun i => L i / 2
  obtain ⟨he, hL, hα⟩ := k1_equality_lengths hc a h
  have hfit : Fits G a (fun i => 2 * q i) 1 := by
    have h' := legLength_fits hc a
    rwa [he, hL] at h'
  let proj := project G a (fun i => 2 * q i) 1
  let iso := evenLegIso q
  let f := iso ∘ proj
  refine ⟨q, f, hα, iso.surjective.comp (project_surjective hc le_rfl hfit), ?_, ?_⟩
  · intro x y hxy
    rcases project_edges hc le_rfl hfit hxy with hh | hh
    · exact Or.inl (congrArg iso hh)
    · exact Or.inr (iso.map_rel_iff.mpr hh)
  · intro u v huv
    have h' := iso.symm.map_rel_iff.mpr huv
    obtain ⟨x, y, hxy, hx, hy⟩ := project_edge_surjective hc le_rfl hfit h'
    exact ⟨x, y, hxy, by simp [f, proj, hx], by simp [f, proj, hy]⟩

open SimpleGraph
open EvenLegTriangle (H Vertex peripheralBlock)

abbrev BlockIndex (q : Fin 3 → ℕ) := Option (Σ i : Fin 3, Fin (q i))

/-- The root layers share one block. Each successive pair of positive depths is one block. -/
def block {q : Fin 3 → ℕ} (x : Vertex q) : BlockIndex q :=
  if h : x.2.val = 0 then none else
    some ⟨x.1, ⟨(x.2.val - 1) / 2, by have := x.2.isLt; omega⟩⟩

/-- Consecutive layers across two successive cliques on the same chain. -/
def Interface {q : Fin 3 → ℕ} (x y : Vertex q) : Prop :=
  x.1 = y.1 ∧
    ((x.2.val % 2 = 0 ∧ x.2.val + 1 = y.2.val) ∨
      (y.2.val % 2 = 0 ∧ y.2.val + 1 = x.2.val))

private theorem coords_eq {L : Fin 3 → ℕ} {x y : Σ i : Fin 3, Fin (L i)}
    (hi : x.1 = y.1) (hd : x.2.val = y.2.val) : x = y := by
  obtain ⟨i, x⟩ := x
  obtain ⟨j, y⟩ := y
  change i = j at hi
  subst j
  exact congrArg (Sigma.mk i) (Fin.ext hd)

private theorem block_eq_iff {q : Fin 3 → ℕ} (x y : Vertex q) :
    block x = block y ↔
      (x.2.val = 0 ∧ y.2.val = 0) ∨
      (x.2.val ≠ 0 ∧ y.2.val ≠ 0 ∧ x.1 = y.1 ∧ (x.2.val - 1) / 2 = (y.2.val - 1) / 2) := by
  by_cases hx : x.2.val = 0 <;> by_cases hy : y.2.val = 0
  · simp [block, hx, hy]
  · simp [block, hx, hy]
  · simp [block, hx, hy]
  · unfold block
    rw [dite_eq_right hx, dite_eq_right hy, Option.some.injEq]
    constructor
    · intro h
      exact Or.inr ⟨hx, hy, congrArg (fun b : Σ i : Fin 3, Fin (q i) => b.1) h,
        congrArg (fun b : Σ i : Fin 3, Fin (q i) => b.2.val) h⟩
    · rintro (⟨h, _⟩ | ⟨_, _, hi, hd⟩)
      · exact (hx h).elim
      · exact coords_eq hi hd

private theorem model_adj_iff {q : Fin 3 → ℕ} {x y : Vertex q} :
    (H q).Adj x y ↔ x ≠ y ∧ (block x = block y ∨ Interface x y) := by
  constructor
  · intro h
    refine ⟨h.ne, ?_⟩
    change (x.1 = y.1 ∧ (x.2.val + 1 = y.2.val ∨ y.2.val + 1 = x.2.val)) ∨
      (x.1 ≠ y.1 ∧ x.2.val = 0 ∧ y.2.val = 0) at h
    rcases h with ⟨hi, hs | hs⟩ | ⟨_, hx, hy⟩
    · by_cases he : x.2.val % 2 = 0
      · exact Or.inr ⟨hi, Or.inl ⟨he, hs⟩⟩
      · exact Or.inl ((block_eq_iff x y).mpr (Or.inr ⟨by omega, by omega, hi, by omega⟩))
    · by_cases he : y.2.val % 2 = 0
      · exact Or.inr ⟨hi, Or.inr ⟨he, hs⟩⟩
      · exact Or.inl ((block_eq_iff x y).mpr (Or.inr ⟨by omega, by omega, hi, by omega⟩))
    · exact Or.inl ((block_eq_iff x y).mpr (Or.inl ⟨hx, hy⟩))
  · rintro ⟨hne, h | h⟩
    · rcases (block_eq_iff x y).mp h with ⟨hx, hy⟩ | ⟨hx, hy, hi, hd⟩
      · exact Or.inr ⟨fun hi => hne (coords_eq hi (hx.trans hy.symm)), hx, hy⟩
      · have hdepth : x.2.val ≠ y.2.val := fun h => hne (coords_eq hi h)
        exact Or.inl ⟨hi, by omega⟩
    · rcases h with ⟨hi, ⟨_, hs⟩ | ⟨_, hs⟩⟩
      · exact Or.inl ⟨hi, Or.inl hs⟩
      · exact Or.inl ⟨hi, Or.inr hs⟩

private theorem interface_ne {q : Fin 3 → ℕ} {x y : Vertex q} (h : Interface x y) : x ≠ y := by
  rintro rfl
  rcases h.2 with ⟨_, hs⟩ | ⟨_, hs⟩ <;> omega

private theorem peripheral_mem {q : Fin 3 → ℕ} {x : Vertex q} (i : Fin 3) (t : ℕ)
    (ht : t ≤ q i) (hi : x.1 = i)
    (hd : x.2.val = 2 * t - 1 ∨ x.2.val = 2 * t) :
    x ∈ peripheralBlock q i t ht := by
  simp only [peripheralBlock, Finset.mem_insert, Finset.mem_singleton]
  rcases hd with h | h
  · exact Or.inl (coords_eq hi h)
  · exact Or.inr (coords_eq hi h)

private theorem roots_companions (q : Fin 3 → ℕ) :
    ∃ A : Finset (Vertex q), A.card = q 0 + q 1 + q 2 ∧ (H q).IsIndepSet (A : Set (Vertex q)) ∧
      ∀ x ∈ A, ∀ y : Vertex q, y.2.val = 0 → x ≠ y ∧ ¬(H q).Adj x y := by
  let positiveEven : (Σ i : Fin 3, Fin (q i)) → Vertex q := fun x =>
    ⟨x.1, ⟨2 * (x.2.val + 1), by have := x.2.isLt; omega⟩⟩
  have evenCoords (x : Σ i : Fin 3, Fin (q i)) : (positiveEven x).2.val = 2 * (x.2.val + 1) :=
    rfl
  let emb : (Σ i : Fin 3, Fin (q i)) ↪ Vertex q :=
    ⟨positiveEven, fun x y h => by
      have hleg : x.1 = y.1 := congrArg (fun z : Vertex q => z.1) h
      apply coords_eq hleg
      have hd := congrArg (fun z : Vertex q => z.2.val) h
      change (positiveEven x).2.val = (positiveEven y).2.val at hd
      rw [evenCoords, evenCoords] at hd
      omega⟩
  refine ⟨Finset.univ.map emb, by simp [Fintype.card_sigma, Fin.sum_univ_three], ?_, ?_⟩
  · rw [isIndepSet_iff]
    intro x hx y hy _ hadj
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hx)
    obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hy)
    have ha := evenCoords a
    have hb := evenCoords b
    rcases hadj with ⟨_, hs | hs⟩ | ⟨_, hz, _⟩
    · change (positiveEven a).2.val + 1 = (positiveEven b).2.val at hs
      omega
    · change (positiveEven b).2.val + 1 = (positiveEven a).2.val at hs
      omega
    · change (positiveEven a).2.val = 0 at hz
      omega
  · intro x hx y hy
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
    have ha := evenCoords a
    refine ⟨?_, ?_⟩
    · intro h
      have hd : (positiveEven a).2.val = y.2.val := congrArg (fun z : Vertex q => z.2.val) h
      omega
    · rintro (⟨_, hs | hs⟩ | ⟨_, hz, _⟩)
      · change (positiveEven a).2.val + 1 = y.2.val at hs
        omega
      · change y.2.val + 1 = (positiveEven a).2.val at hs
        omega
      · change (positiveEven a).2.val = 0 at hz
        omega

private theorem block_companions {q : Fin 3 → ℕ} {u v : Vertex q} (h : block u = block v) :
    ∃ A : Finset (Vertex q), A.card = q 0 + q 1 + q 2 ∧ (H q).IsIndepSet (A : Set (Vertex q)) ∧
      ∀ z ∈ A, (z ≠ u ∧ ¬(H q).Adj z u) ∧ (z ≠ v ∧ ¬(H q).Adj z v) := by
  rcases (block_eq_iff u v).mp h with ⟨hu, hv⟩ | ⟨hu, hv, hleg, hdepth⟩
  · obtain ⟨A, hA, hi, hr⟩ := roots_companions q
    exact ⟨A, hA, hi, fun z hz => ⟨hr z hz u hu, hr z hz v hv⟩⟩
  · let t := (u.2.val - 1) / 2 + 1
    have ht₀ : 1 ≤ t := by dsimp [t]; omega
    have ht : t ≤ q u.1 := by
      have hd := u.2.isLt
      dsimp [t]
      omega
    have hum : u ∈ peripheralBlock q u.1 t ht := by
      apply peripheral_mem _ _ _ rfl
      dsimp [t]
      omega
    have hvm : v ∈ peripheralBlock q u.1 t ht := by
      apply peripheral_mem _ _ _ hleg.symm
      dsimp [t]
      omega
    obtain ⟨A, hA, hi, hr⟩ := EvenLegTriangle.peripheral_companions q u.1 t ht₀ ht
    exact ⟨A, hA, hi, fun z hz => ⟨hr z hz u hum, hr z hz v hvm⟩⟩

private theorem indep_insert {V : Type*} [DecidableEq V] {G : SimpleGraph V} {B : Finset V}
    (hB : G.IsIndepSet (B : Set V)) {x : V} (hx : ∀ b ∈ B, ¬ G.Adj b x) :
    G.IsIndepSet (↑(insert x B) : Set V) := by
  rw [isIndepSet_iff] at hB ⊢
  simp only [Finset.coe_insert]
  rintro u (rfl | hu) v (rfl | hv) huv h
  · exact huv rfl
  · exact hx v hv h.symm
  · exact hx u hu h
  · exact hB (Finset.mem_coe.mpr hu) (Finset.mem_coe.mpr hv) huv h

private theorem clique_of_equal_block {V : Type*} [Finite V] {G : SimpleGraph V}
    {q : Fin 3 → ℕ} {f : V → Vertex q} (hs : Function.Surjective f)
    (hedge : ∀ x y, G.Adj x y → f x = f y ∨ (H q).Adj (f x) (f y))
    (hα : G.indepNum = q 0 + q 1 + q 2 + 1)
    {x y : V} (hne : x ≠ y) (hb : block (f x) = block (f y)) : G.Adj x y := by
  classical
  by_contra hxy
  obtain ⟨A, hA, hAi, hAr⟩ := block_companions hb
  let g : Vertex q → V := fun z => (hs z).choose
  have hg (z : Vertex q) : f (g z) = z := (hs z).choose_spec
  let emb : Vertex q ↪ V := ⟨g, fun a b h => (hg a).symm.trans ((congrArg f h).trans (hg b))⟩
  let B := A.map emb
  have hB : G.IsIndepSet (B : Set V) := by
    rw [isIndepSet_iff] at hAi ⊢
    intro a ha b hb hab h
    obtain ⟨i, hii, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp ha)
    obtain ⟨j, hjj, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hb)
    have hh := hedge (g i) (g j) h
    rw [hg, hg] at hh
    exact hh.elim (fun he => hab (congrArg g he))
      (hAi (Finset.mem_coe.mpr hii) (Finset.mem_coe.mpr hjj) (fun he => hab (congrArg g he)))
  have hr (b : V) (hb : b ∈ B) :
      (b ≠ x ∧ ¬ G.Adj b x) ∧ (b ≠ y ∧ ¬ G.Adj b y) := by
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hb
    obtain ⟨hx, hy⟩ := hAr z hz
    have lift (w : V) (h : z ≠ f w ∧ ¬(H q).Adj z (f w)) :
        g z ≠ w ∧ ¬ G.Adj (g z) w := by
      constructor
      · intro he
        exact h.1 ((hg z).symm.trans (congrArg f he))
      · intro ha
        have hh := hedge _ _ ha
        rw [hg] at hh
        exact hh.elim h.1 h.2
    exact ⟨lift x hx, lift y hy⟩
  have hxB : x ∉ B := fun h => (hr x h).1.1 rfl
  have hyB : y ∉ B := fun h => (hr y h).2.1 rfl
  have hyI := indep_insert hB (fun b hb => (hr b hb).2.2)
  have hxyI := indep_insert hyI (x := x) (by
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact fun hh => hxy hh.symm
    · exact (hr b hb).1.2)
  have hcard := hxyI.card_le_indepNum
  have hcardB : B.card = A.card := Finset.card_map _
  rw [Finset.card_insert_of_notMem (by simp [hne, hxB]), Finset.card_insert_of_notMem hyB,
    hcardB, hA, hα] at hcard
  omega

/-- Fibers are the layers. Block zero is the central clique, and positive blocks split into two layers. -/
structure CliqueChains {V : Type*} (G : SimpleGraph V) (q : Fin 3 → ℕ) (f : V → Vertex q) : Prop where
  layers_nonempty : Function.Surjective f
  within_cliques : ∀ x y, x ≠ y → block (f x) = block (f y) → G.Adj x y
  allowed_edges : ∀ x y, G.Adj x y → block (f x) = block (f y) ∨ Interface (f x) (f y)
  interfaces_nonempty : ∀ u v, Interface u v → ∃ x y, G.Adj x y ∧ f x = u ∧ f y = v

private theorem equality_clique_chains {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hc : G.Connected) (h : triameter G = 4 * G.indepNum - 1) :
    ∃ (q : Fin 3 → ℕ) (f : V → Vertex q), CliqueChains G q f := by
  obtain ⟨a, ha⟩ := exists_perimeter_eq_triameter hc
  have hbound := triameter_le_indepNum hc
  obtain ⟨q, f, hα, hs, hmap, hlift⟩ := k1_equality_projection hc a (by omega)
  refine ⟨q, f, ⟨hs, fun x y hn hb => clique_of_equal_block hs hmap hα hn hb, ?_, ?_⟩⟩
  · intro x y hxy
    exact (hmap x y hxy).elim (fun hh => Or.inl (congrArg block hh))
      (fun hh => (model_adj_iff.mp hh).2)
  · intro u v huv
    exact hlift u v (model_adj_iff.mpr ⟨interface_ne huv, Or.inr huv⟩)

private theorem clique_chains_indepNum_le {V : Type*} {G : SimpleGraph V}
    {q : Fin 3 → ℕ} {f : V → Vertex q} (h : CliqueChains G q f) :
    G.indepNum ≤ q 0 + q 1 + q 2 + 1 := by
  classical
  obtain ⟨A, hA⟩ := G.exists_isNIndepSet_indepNum
  have hi := hA.isIndepSet
  rw [isIndepSet_iff] at hi
  have injective : Set.InjOn (block ∘ f) (A : Set V) := by
    intro x hx y hy hb
    by_contra hne
    exact hi hx hy hne (h.within_cliques x y hne hb)
  have hcard := Finset.card_le_card_of_injOn (block ∘ f)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _) injective
  rw [hA.card_eq] at hcard
  simpa [BlockIndex, Fintype.card_sigma, Fin.sum_univ_three] using hcard

/-- Edge maps into the even-leg model contract distances, even when edges collapse. -/
private theorem evenLeg_coord_le_dist {V : Type*} {G : SimpleGraph V} (hc : G.Connected)
    {q : Fin 3 → ℕ} {f : V → Vertex q}
    (h : ∀ x y, G.Adj x y → f x = f y ∨ (H q).Adj (f x) (f y)) (x y : V) :
    spiderDist ((evenLegIso q).symm (f x)) ((evenLegIso q).symm (f y)) ≤ G.dist x y := by
  let g := (evenLegIso q).symm ∘ f
  have hwalk {u v : V} (p : G.Walk u v) : spiderDist (g u) (g v) ≤ p.length := by
    induction p with
    | nil => simp [spiderDist]
    | @cons a b c hab p ih =>
      have hedge : spiderDist (g a) (g b) ≤ 1 := by
        rcases h a b hab with he | ha
        · have hg : g a = g b := congrArg (evenLegIso q).symm he
          simp [hg, spiderDist]
        · have hh : (spider 1 (fun i => 2 * q i)).Adj (g a) (g b) :=
            (evenLegIso q).symm.map_rel_iff.mpr ha
          change spiderDist (g a) (g b) = 1 at hh
          exact hh.le
      have ht := spiderDist_triangle (g a) (g b) (g c)
      change spiderDist (g a) (g c) ≤ p.length + 1
      omega
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist x y
  exact hp ▸ hwalk p

private theorem clique_chains_triameter_ge {V : Type*} [Fintype V] {G : SimpleGraph V} (hc : G.Connected)
    {q : Fin 3 → ℕ} {f : V → Vertex q} (h : CliqueChains G q f) :
    4 * (q 0 + q 1 + q 2) + 3 ≤ triameter G := by
  let L : Fin 3 → ℕ := fun i => 2 * q i
  let iso := evenLegIso q
  let footLift (i : Fin 3) := (h.layers_nonempty (iso (foot 1 L i))).choose
  have hfoot (i : Fin 3) : iso.symm (f (footLift i)) = foot 1 L i := by
    have hh := (h.layers_nonempty (iso (foot 1 L i))).choose_spec
    change f (footLift i) = iso (foot 1 L i) at hh
    simp [hh]
  have hmap (x y : V) (hxy : G.Adj x y) : f x = f y ∨ (H q).Adj (f x) (f y) := by
    by_cases he : f x = f y
    · exact Or.inl he
    · exact Or.inr (model_adj_iff.mpr ⟨he, h.allowed_edges x y hxy⟩)
  have hpair (i j : Fin 3) (hij : i ≠ j) :
      2 * q i + 2 * q j + 1 ≤ G.dist (footLift i) (footLift j) := by
    have hh := evenLeg_coord_le_dist hc hmap (footLift i) (footLift j)
    change spiderDist (iso.symm (f (footLift i))) (iso.symm (f (footLift j))) ≤ _ at hh
    rw [hfoot, hfoot, ← spider_dist_eq (by decide), spider_foot_dist (by decide) hij] at hh
    exact hh
  have h01 := hpair 0 1 (by decide)
  have h02 := hpair 0 2 (by decide)
  have h12 := hpair 1 2 (by decide)
  have ht := perimeter_le_triameter G footLift
  unfold perimeter at ht
  omega

private theorem clique_chains_equality {V : Type*} [Fintype V] {G : SimpleGraph V} (hc : G.Connected)
    {q : Fin 3 → ℕ} {f : V → Vertex q} (h : CliqueChains G q f) :
    triameter G = 4 * G.indepNum - 1 ∧ G.indepNum = q 0 + q 1 + q 2 + 1 := by
  have hα := clique_chains_indepNum_le h
  have hlo := clique_chains_triameter_ge hc h
  have hhi := triameter_le_indepNum hc
  exact ⟨by omega, by omega⟩

/-- Hak–Kozerenko's Question 1. The equivalence also holds on connected graphs of order 1 and 2. -/
theorem question1 {V : Type*} [Fintype V] {G : SimpleGraph V} (hc : G.Connected) :
    triameter G = 4 * G.indepNum - 1 ↔
      ∃ (q : Fin 3 → ℕ) (f : V → Vertex q), CliqueChains G q f := by
  refine ⟨equality_clique_chains hc, ?_⟩
  rintro ⟨q, f, h⟩
  exact (clique_chains_equality hc h).1

end D5.S3.Combinatorics.Graph.Triameter
