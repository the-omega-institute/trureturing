/- GID: D5/S3/Combinatorics/Graph/Triameter/CliqueChains
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Triameter/CliqueChains
   mirror-E: none(waiver:universal-finite-graph-theorem)
   anchors: []
   utility: none
   digest: Equality in the triameter bound by independence classifies chains of split cliques. -/

/-
proof_shape: question1: content
escape_witness: The marked-block companions force every block fiber to be a clique
  when the independence number attains the packing bound.
admission_basis: open-problem-resolution (Hak–Kozerenko Question 1 at k = 1, #32242)
Direct frozen dependencies: none. The proof uses pinned Mathlib.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Triameter and chains of split cliques

A perimeter triple projects to the feet of three legs attached to a point or a triangle.
The packing bound forces a triangular centre and even leg lengths at equality for independence.
The preimages of the central triangle and successive pairs of positive depths are cliques.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

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

/-- With offset zero, only leg zero represents the shared root. Offset one keeps all roots. -/
private abbrev SpiderVertex (e : ℕ) (L : Fin 3 → ℕ) :=
  { x : Σ i : Fin 3, Fin (L i + 1) // e ≠ 0 ∨ x.1 = 0 ∨ 0 < x.2.val }

private def leg {e : ℕ} {L : Fin 3 → ℕ} (x : SpiderVertex e L) : Fin 3 := x.val.1
private def depth {e : ℕ} {L : Fin 3 → ℕ} (x : SpiderVertex e L) : ℕ := x.val.2.val

private theorem vertex_ext {e : ℕ} {L : Fin 3 → ℕ} {x y : SpiderVertex e L}
    (hi : leg x = leg y) (hd : depth x = depth y) : x = y := by
  apply Subtype.ext
  rcases x with ⟨⟨i, x⟩, _⟩
  rcases y with ⟨⟨j, y⟩, _⟩
  change i = j at hi
  subst j
  exact congrArg (Sigma.mk i) (Fin.ext hd)

private def rootZero (e : ℕ) (L : Fin 3 → ℕ) : SpiderVertex e L :=
  ⟨⟨0, ⟨0, Nat.zero_lt_succ _⟩⟩, Or.inr (Or.inl rfl)⟩

private def point {e : ℕ} {L : Fin 3 → ℕ} (i : Fin 3) (d : ℕ) (hd : d ≤ L i) :
    SpiderVertex e L :=
  if h : e = 0 ∧ d = 0 then rootZero e L
  else ⟨⟨i, ⟨d, Nat.lt_succ_of_le hd⟩⟩, by
    by_cases he : e = 0
    · exact Or.inr (Or.inr (Nat.pos_of_ne_zero fun hz => h ⟨he, hz⟩))
    · exact Or.inl he⟩

private theorem point_congr {e : ℕ} {L : Fin 3 → ℕ} {i j : Fin 3} {d f : ℕ}
    {hd : d ≤ L i} {hf : f ≤ L j} (hi : i = j) (hdf : d = f) :
    point (e := e) i d hd = point j f hf := by
  subst j
  subst f
  rfl

@[simp] private theorem depth_point {e : ℕ} {L : Fin 3 → ℕ} (i : Fin 3) (d : ℕ) (hd : d ≤ L i) :
    depth (point (e := e) i d hd) = d := by
  unfold point
  split
  · next h => exact h.2.symm
  · rfl

private theorem leg_point {e : ℕ} {L : Fin 3 → ℕ} (i : Fin 3) (d : ℕ) (hd : d ≤ L i)
    (h : e ≠ 0 ∨ 0 < d) : leg (point (e := e) i d hd) = i := by
  unfold point
  split
  · rename_i hzero
    rcases h with he | hd
    · exact False.elim (he hzero.1)
    · omega
  · rfl

private theorem point_coords {e : ℕ} {L : Fin 3 → ℕ} (x : SpiderVertex e L) :
    point (leg x) (depth x) (Nat.le_of_lt_succ x.val.2.isLt) = x := by
  apply vertex_ext _ (depth_point _ _ _)
  rcases x.property with he | hi | hd
  · exact leg_point _ _ _ (Or.inl he)
  · change leg x = 0 at hi
    unfold point
    split
    · exact hi.symm
    · rfl
  · exact leg_point _ _ _ (Or.inr hd)

private def spiderDist {e : ℕ} {L : Fin 3 → ℕ} (x y : SpiderVertex e L) : ℕ :=
  if leg x = leg y then (depth x - depth y) + (depth y - depth x)
  else depth x + depth y + e

private theorem spiderDist_comm {e : ℕ} {L : Fin 3 → ℕ} (x y : SpiderVertex e L) :
    spiderDist x y = spiderDist y x := by
  unfold spiderDist
  by_cases h : leg x = leg y
  · simp only [ite_eq_left h, ite_eq_left h.symm]
    omega
  · simp only [ite_eq_right h, ite_eq_right (Ne.symm h)]
    omega

private theorem spiderDist_zero_iff {e : ℕ} {L : Fin 3 → ℕ} (x y : SpiderVertex e L) :
    spiderDist x y = 0 ↔ x = y := by
  constructor
  · unfold spiderDist
    split
    · next h => exact fun hz => vertex_ext h (by omega)
    · next h =>
      intro hz
      have he : e = 0 := by omega
      have hx : depth x = 0 := by omega
      have hy : depth y = 0 := by omega
      have root_leg (z : SpiderVertex e L) (hd : depth z = 0) : leg z = 0 := by
        rcases z.property with he' | hi | hp
        · exact False.elim (he' he)
        · exact hi
        · change 0 < depth z at hp
          omega
      exact False.elim (h ((root_leg x hx).trans (root_leg y hy).symm))
  · rintro rfl
    simp [spiderDist]

private theorem spiderDist_triangle {e : ℕ} {L : Fin 3 → ℕ} (x y z : SpiderVertex e L) :
    spiderDist x z ≤ spiderDist x y + spiderDist y z := by
  unfold spiderDist
  split <;> split <;> split <;> omega

private def spider (e : ℕ) (L : Fin 3 → ℕ) : SimpleGraph (SpiderVertex e L) where
  Adj x y := spiderDist x y = 1
  symm := ⟨fun x y h => (spiderDist_comm y x).trans h⟩
  loopless := ⟨fun x h => by simp [spiderDist] at h⟩

private theorem spiderDist_point {e : ℕ} {L : Fin 3 → ℕ}
    (i j : Fin 3) (d f : ℕ) (hd : d ≤ L i) (hf : f ≤ L j) :
    spiderDist (point (e := e) i d hd) (point j f hf) =
      if i = j then (d - f) + (f - d) else d + f + e := by
  unfold spiderDist
  simp only [depth_point]
  by_cases hx : e = 0 ∧ d = 0 <;> by_cases hy : e = 0 ∧ f = 0
  · simp [hx.1, hx.2, hy.2]
  · simp only [hx.1, hx.2]
    split <;> split <;> simp
  · simp only [hy.1, hy.2]
    split <;> split <;> simp
  · rw [leg_point i d hd (by omega), leg_point j f hf (by omega)]

private theorem spider_adj_iff {L : Fin 3 → ℕ} {x y : SpiderVertex 1 L} :
    (spider 1 L).Adj x y ↔
      (leg x = leg y ∧ (depth x + 1 = depth y ∨ depth y + 1 = depth x)) ∨
      (leg x ≠ leg y ∧ depth x = 0 ∧ depth y = 0) := by
  change spiderDist x y = 1 ↔ _
  by_cases h : leg x = leg y
  · simp [spiderDist, h]
    omega
  · simp [spiderDist, h]

private def evenLegIso (q : Fin 3 → ℕ) :
    spider 1 (fun i => 2 * q i) ≃g EvenLegTriangle.H q where
  toEquiv :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x, Or.inl (by decide)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  map_rel_iff' := by
    intro x y
    exact spider_adj_iff.symm

section Projection
variable {V : Type*} {G : SimpleGraph V} {a : Fin 3 → V} {L : Fin 3 → ℕ} {e : ℕ}

/-- The open tree balls and the closed triangle balls have this common threshold. -/
private def Active (G : SimpleGraph V) (a : Fin 3 → V) (L : Fin 3 → ℕ) (e : ℕ)
    (x : V) (i : Fin 3) : Prop :=
  G.dist (a i) x + (1 - e) ≤ L i

private def Fits (G : SimpleGraph V) (a : Fin 3 → V) (L : Fin 3 → ℕ) (e : ℕ) : Prop :=
  ∀ i j, i ≠ j → G.dist (a i) (a j) = L i + L j + e

private theorem active_unique (hc : G.Connected) (he : e ≤ 1) (hfit : Fits G a L e)
    {x : V} {i j : Fin 3} (hi : Active G a L e x i) (hj : Active G a L e x j) : i = j := by
  by_contra h
  have ht := hc.dist_triangle (u := a i) (v := x) (w := a j)
  rw [hfit i j h, dist_comm (u := x) (v := a j)] at ht
  unfold Active at hi hj
  omega

private noncomputable def project (G : SimpleGraph V) (a : Fin 3 → V) (L : Fin 3 → ℕ) (e : ℕ)
    (x : V) : SpiderVertex e L := by
  classical
  exact if h : ∃ i, Active G a L e x i then
    point h.choose (L h.choose - G.dist (a h.choose) x) (Nat.sub_le ..)
  else rootZero e L

private theorem project_active (hc : G.Connected) (he : e ≤ 1) (hfit : Fits G a L e)
    {x : V} {i : Fin 3} (hi : Active G a L e x i) :
    project G a L e x = point i (L i - G.dist (a i) x) (Nat.sub_le ..) := by
  classical
  have h : ∃ j, Active G a L e x j := ⟨i, hi⟩
  unfold project
  rw [dite_eq_left h]
  exact congrArg (fun j => point j (L j - G.dist (a j) x) (Nat.sub_le ..))
    (active_unique hc he hfit h.choose_spec hi)

private theorem project_inactive {x : V} (h : ¬ ∃ i, Active G a L e x i) :
    project G a L e x = rootZero e L := by
  classical
  simp [project, h]

private theorem project_nonexpanding (hc : G.Connected) (he : e ≤ 1) (hfit : Fits G a L e)
    (x y : V) : spiderDist (project G a L e x) (project G a L e y) ≤ G.dist x y := by
  have reverse_dist (i : Fin 3) : G.dist (a i) x ≤ G.dist (a i) y + G.dist x y := by
    rw [dist_comm (u := x) (v := y)]
    exact hc.dist_triangle
  have forward_dist (i : Fin 3) : G.dist (a i) y ≤ G.dist (a i) x + G.dist x y :=
    hc.dist_triangle
  have cross_dist (i j : Fin 3) (hij : i ≠ j) :
      L i + L j + e ≤ G.dist (a i) x + G.dist x y + G.dist (a j) y := by
    have h₁ := hc.dist_triangle (u := a i) (v := y) (w := a j)
    have h₂ := hc.dist_triangle (u := a i) (v := x) (w := y)
    rw [hfit i j hij, dist_comm (u := y) (v := a j)] at h₁
    omega
  have hroot : rootZero e L = point 0 0 (Nat.zero_le _) := by
    by_cases hh : e = 0 <;> simp [point, hh, rootZero]
  by_cases hx : ∃ i, Active G a L e x i
  · obtain ⟨i, hi⟩ := hx
    rw [project_active hc he hfit hi]
    by_cases hy : ∃ j, Active G a L e y j
    · obtain ⟨j, hj⟩ := hy
      rw [project_active hc he hfit hj, spiderDist_point]
      by_cases hij : i = j
      · subst j
        rw [ite_eq_left (show i = i from rfl)]
        have := reverse_dist i
        have := forward_dist i
        omega
      · have := cross_dist i j hij
        simp only [ite_eq_right hij]
        unfold Active at hi hj
        omega
    · rw [project_inactive hy, hroot, spiderDist_point]
      have hin : ¬ Active G a L e y i := fun h => hy ⟨i, h⟩
      unfold Active at hi hin
      have := forward_dist i
      split <;> omega
  · rw [project_inactive hx]
    by_cases hy : ∃ j, Active G a L e y j
    · obtain ⟨j, hj⟩ := hy
      rw [project_active hc he hfit hj, hroot, spiderDist_point]
      have hin : ¬ Active G a L e x j := fun h => hx ⟨j, h⟩
      unfold Active at hj hin
      have := reverse_dist j
      split <;> omega
    · rw [project_inactive hy]
      simp [spiderDist]

private theorem project_edges (hc : G.Connected) (he : e ≤ 1) (hfit : Fits G a L e)
    {x y : V} (hxy : G.Adj x y) :
    project G a L e x = project G a L e y ∨
      (spider e L).Adj (project G a L e x) (project G a L e y) := by
  have h := project_nonexpanding hc he hfit x y
  rw [dist_eq_one_iff_adj.mpr hxy] at h
  by_cases hz : spiderDist (project G a L e x) (project G a L e y) = 0
  · exact Or.inl ((spiderDist_zero_iff ..).mp hz)
  · exact Or.inr (show spiderDist (project G a L e x) (project G a L e y) = 1 by omega)

private theorem project_of_dist_le (hc : G.Connected) (he : e ≤ 1) (hfit : Fits G a L e)
    {x : V} {i : Fin 3} (hi : G.dist (a i) x ≤ L i) :
    project G a L e x = point i (L i - G.dist (a i) x) (Nat.sub_le ..) := by
  by_cases h : Active G a L e x i
  · exact project_active hc he hfit h
  · unfold Active at h
    have he₀ : e = 0 := by omega
    have hi' : G.dist (a i) x = L i := by omega
    have hn : ¬ ∃ j, Active G a L e x j := by
      rintro ⟨j, hj⟩
      by_cases hij : i = j
      · exact h (hij ▸ hj)
      · have ht := hc.dist_triangle (u := a i) (v := x) (w := a j)
        rw [hfit i j hij, dist_comm (u := x) (v := a j), hi'] at ht
        unfold Active at hj
        omega
    rw [project_inactive hn]
    simp [point, he₀, hi']

private def foot (e : ℕ) (L : Fin 3 → ℕ) (i : Fin 3) : SpiderVertex e L :=
  point i (L i) le_rfl

private theorem geodesic_coordinates (hc : G.Connected) {x y : V} (p : G.Walk x y)
    (hp : p.length = G.dist x y) {n : ℕ} (hn : n ≤ p.length) :
    G.dist x (p.getVert n) = n ∧ G.dist y (p.getVert n) = p.length - n := by
  have hl := dist_le (p.take n)
  have hr := dist_le (p.drop n)
  simp only [Walk.take_length, inf_eq_left.mpr hn] at hl
  simp only [Walk.drop_length] at hr
  have ht := hc.dist_triangle (u := x) (v := p.getVert n) (w := y)
  rw [← hp] at ht
  rw [dist_comm (u := y) (v := p.getVert n)]
  omega

private theorem project_surjective (hc : G.Connected) (he : e ≤ 1) (hfit : Fits G a L e) :
    Function.Surjective (project G a L e) := by
  intro x
  let i := leg x
  let d := depth x
  have hd : d ≤ L i := Nat.le_of_lt_succ x.val.2.isLt
  obtain ⟨j, hji⟩ := exists_ne i
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist (a i) (a j)
  have hlen : p.length = L i + L j + e := hp.trans (hfit i j (Ne.symm hji))
  let n := L i - d
  have hcoord := (geodesic_coordinates hc p hp (n := n) (by dsimp [n]; omega)).1
  refine ⟨p.getVert n, ?_⟩
  rw [project_of_dist_le hc he hfit (i := i) (x := p.getVert n)
    (by rw [hcoord]; exact Nat.sub_le ..)]
  have hdepth : L i - G.dist (a i) (p.getVert n) = d := by
    rw [hcoord]
    dsimp [n]
    omega
  exact (point_congr rfl hdepth).trans (point_coords x)

private theorem geodesic_project_left (hc : G.Connected) (he : e ≤ 1)
    (hfit : Fits G a L e) {i j : Fin 3} (p : G.Walk (a i) (a j))
    (hp : p.length = G.dist (a i) (a j)) {n : ℕ} (hn : n ≤ p.length)
    (hi : n ≤ L i) :
    project G a L e (p.getVert n) = point i (L i - n) (Nat.sub_le ..) := by
  have hdist := (geodesic_coordinates hc p hp hn).1
  have hpj := project_of_dist_le hc he hfit (x := p.getVert n) (i := i) (hdist.symm ▸ hi)
  exact hpj.trans (congrArg (fun m => point i (L i - m) (Nat.sub_le ..)) hdist)

private theorem lift_leg_edge (hc : G.Connected) (he : e ≤ 1) (hfit : Fits G a L e)
    (i : Fin 3) (d : ℕ) (hd : d + 1 ≤ L i) :
    ∃ x y, G.Adj x y ∧
      project G a L e x = point i (d + 1) hd ∧
      project G a L e y = point i d (by omega) := by
  obtain ⟨j, hji⟩ := exists_ne i
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist (a i) (a j)
  have hlen : p.length = L i + L j + e := hp.trans (hfit i j (Ne.symm hji))
  let n := L i - (d + 1)
  have hn : n < p.length := by dsimp [n]; omega
  have hd₁ : L i - n = d + 1 := by dsimp [n]; omega
  have hd₂ : L i - (n + 1) = d := by dsimp [n]; omega
  refine ⟨p.getVert n, p.getVert (n + 1), p.adj_getVert_succ hn, ?_, ?_⟩
  · exact (geodesic_project_left hc he hfit p hp (by omega) (Nat.sub_le ..)).trans
      (point_congr rfl hd₁)
  · exact (geodesic_project_left hc he hfit p hp (by omega) (by dsimp [n]; omega)).trans
      (point_congr rfl hd₂)

private theorem lift_triangle_edge (hc : G.Connected) (hfit : Fits G a L 1)
    {i j : Fin 3} (hij : i ≠ j) :
    ∃ x y, G.Adj x y ∧
      project G a L 1 x = point i 0 (Nat.zero_le _) ∧
      project G a L 1 y = point j 0 (Nat.zero_le _) := by
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist (a i) (a j)
  have hlen := hp.trans (hfit i j hij)
  have hn : L i < p.length := by omega
  have hj := (geodesic_coordinates hc p hp (n := L i + 1) (by omega)).2
  have hj' : G.dist (a j) (p.getVert (L i + 1)) = L j := by omega
  refine ⟨p.getVert (L i), p.getVert (L i + 1), p.adj_getVert_succ hn, ?_, ?_⟩
  · simpa only [Nat.sub_self] using geodesic_project_left hc le_rfl hfit p hp (by omega) le_rfl
  · have h := project_of_dist_le hc le_rfl hfit (x := p.getVert (L i + 1)) (i := j) hj'.le
    exact h.trans (by simp only [hj', Nat.sub_self])

private theorem project_edge_surjective (hc : G.Connected) (he : e ≤ 1) (hfit : Fits G a L e)
    {u v : SpiderVertex e L} (huv : (spider e L).Adj u v) :
    ∃ x y, G.Adj x y ∧ project G a L e x = u ∧ project G a L e y = v := by
  let i := leg u
  let j := leg v
  let d := depth u
  let f := depth v
  have hd : d ≤ L i := Nat.le_of_lt_succ u.val.2.isLt
  have hf : f ≤ L j := Nat.le_of_lt_succ v.val.2.isLt
  have hu : point (e := e) i d hd = u := point_coords u
  have hv : point (e := e) j f hf = v := point_coords v
  change (if i = j then (d - f) + (f - d) else d + f + e) = 1 at huv
  have same_leg (hij : i = j) (hstep : d + 1 = f ∨ f + 1 = d) :
      ∃ x y, G.Adj x y ∧ project G a L e x = u ∧ project G a L e y = v := by
    rcases hstep with h | h
    · have hh : d + 1 ≤ L i := by simpa only [hij, h] using hf
      obtain ⟨x, y, hxy, hx, hy⟩ := lift_leg_edge hc he hfit i d hh
      refine ⟨y, x, hxy.symm, hy.trans hu, hx.trans ?_⟩
      calc
        point i (d + 1) hh = point j f hf := point_congr hij h
        _ = v := hv
    · have hh : f + 1 ≤ L j := by simpa only [← hij, h] using hd
      obtain ⟨x, y, hxy, hx, hy⟩ := lift_leg_edge hc he hfit j f hh
      refine ⟨x, y, hxy, hx.trans ?_, hy.trans hv⟩
      calc
        point j (f + 1) hh = point i d hd := point_congr hij.symm h
        _ = u := hu
  by_cases hij : i = j
  · rw [ite_eq_left hij] at huv
    exact same_leg hij (by omega)
  · rw [ite_eq_right hij] at huv
    rcases (show e = 1 ∨ (e = 0 ∧ d = 0 ∧ f = 1) ∨ (e = 0 ∧ d = 1 ∧ f = 0) by omega)
      with h | ⟨h, hz, hs⟩ | ⟨h, hs, hz⟩
    · subst e
      have hd' : d = 0 := by omega
      have hf' : f = 0 := by omega
      obtain ⟨x, y, hxy, hx, hy⟩ := lift_triangle_edge hc hfit hij
      exact ⟨x, y, hxy, hx.trans (by simpa only [hd'] using hu),
        hy.trans (by simpa only [hf'] using hv)⟩
    · subst e
      obtain ⟨x, y, hxy, hx, hy⟩ := lift_leg_edge hc (by decide) hfit j 0 (by omega)
      have hu' : rootZero 0 L = u := by simpa [hz, point] using hu
      refine ⟨y, x, hxy.symm, ?_, hx.trans ?_⟩
      · exact hy.trans (by simpa [point] using hu')
      · simpa only [hs] using hv
    · subst e
      obtain ⟨x, y, hxy, hx, hy⟩ := lift_leg_edge hc (by decide) hfit i 0 (by omega)
      have hv' : rootZero 0 L = v := by simpa [hz, point] using hv
      refine ⟨x, y, hxy, hx.trans ?_, ?_⟩
      · simpa only [hs] using hu
      · exact hy.trans (by simpa [point] using hv')

end Projection

noncomputable def perimeter {V : Type*} (G : SimpleGraph V) (a : Fin 3 → V) : ℕ :=
  G.dist (a 0) (a 1) + G.dist (a 0) (a 2) + G.dist (a 1) (a 2)

private noncomputable def legLength {V : Type*} (G : SimpleGraph V) (a : Fin 3 → V)
    (i : Fin 3) : ℕ :=
  let x := G.dist (a 0) (a 1)
  let y := G.dist (a 0) (a 2)
  let z := G.dist (a 1) (a 2)
  if i = 0 then (x + y - z) / 2 else if i = 1 then (x + z - y) / 2 else (y + z - x) / 2

private theorem legLength_fits {V : Type*} {G : SimpleGraph V} (hc : G.Connected) (a : Fin 3 → V) :
    Fits G a (legLength G a) (perimeter G a % 2) := by
  have h₀ := hc.dist_triangle (u := a 1) (v := a 0) (w := a 2)
  have h₁ := hc.dist_triangle (u := a 0) (v := a 1) (w := a 2)
  have h₂ := hc.dist_triangle (u := a 0) (v := a 2) (w := a 1)
  rw [dist_comm (u := a 1) (v := a 0)] at h₀
  rw [dist_comm (u := a 2) (v := a 1)] at h₂
  let L := legLength G a
  let e := perimeter G a % 2
  have h01 : G.dist (a 0) (a 1) = L 0 + L 1 + e := by
    simp [L, e, legLength, perimeter]
    omega
  have h02 : G.dist (a 0) (a 2) = L 0 + L 2 + e := by
    simp [L, e, legLength, perimeter]
    omega
  have h12 : G.dist (a 1) (a 2) = L 1 + L 2 + e := by
    simp [L, e, legLength, perimeter]
    omega
  have h10 : G.dist (a 1) (a 0) = L 1 + L 0 + e := by
    rw [dist_comm, h01, Nat.add_comm (L 0)]
  have h20 : G.dist (a 2) (a 0) = L 2 + L 0 + e := by
    rw [dist_comm, h02, Nat.add_comm (L 0)]
  have h21 : G.dist (a 2) (a 1) = L 2 + L 1 + e := by
    rw [dist_comm, h12, Nat.add_comm (L 1)]
  intro i j hij
  fin_cases i <;> fin_cases j <;> first
    | exact False.elim (hij rfl)
    | exact h01
    | exact h02
    | exact h12
    | exact h10
    | exact h20
    | exact h21

private theorem perimeter_of_fits {V : Type*} {G : SimpleGraph V} {a : Fin 3 → V}
    {L : Fin 3 → ℕ} {e : ℕ} (h : Fits G a L e) :
    perimeter G a = 2 * (L 0 + L 1 + L 2) + 3 * e := by
  unfold perimeter
  rw [h 0 1 (by decide), h 0 2 (by decide), h 1 2 (by decide)]
  omega

section ModelMetric
variable {e : ℕ} {L : Fin 3 → ℕ}

private theorem leg_walk (i : Fin 3) (d f : ℕ) (hd : d ≤ f) (hf : f ≤ L i) :
    ∃ p : (spider e L).Walk (point i d (hd.trans hf)) (point i f hf), p.length = f - d := by
  induction f, hd using Nat.le_induction with
  | base => exact ⟨.nil, by simp⟩
  | succ n hdn ih =>
    have hn : n ≤ L i := by omega
    obtain ⟨p, hp⟩ := ih hn
    have hedge : (spider e L).Adj (point i n hn) (point i (n + 1) hf) := by
      change spiderDist _ _ = 1
      rw [spiderDist_point, ite_eq_left (show i = i from rfl)]
      omega
    refine ⟨p.append hedge.toWalk, ?_⟩
    rw [Walk.length_append, hp]
    change n - d + 1 = n + 1 - d
    omega

private theorem root_walk (he : e ≤ 1) {i j : Fin 3} (hij : i ≠ j) :
    ∃ p : (spider e L).Walk (point i 0 (Nat.zero_le _)) (point j 0 (Nat.zero_le _)),
      p.length = e := by
  by_cases h : e = 0
  · subst e
    exact ⟨.nil, rfl⟩
  · have h' : e = 1 := by omega
    have hedge : (spider e L).Adj (point i 0 (Nat.zero_le _)) (point j 0 (Nat.zero_le _)) := by
      change spiderDist _ _ = 1
      rw [spiderDist_point, ite_eq_right hij]
      omega
    exact ⟨hedge.toWalk, h'.symm⟩

private theorem walk_between_points (he : e ≤ 1) (i j : Fin 3) (d f : ℕ)
    (hd : d ≤ L i) (hf : f ≤ L j) :
    ∃ p : (spider e L).Walk (point i d hd) (point j f hf),
      p.length = spiderDist (point (e := e) i d hd) (point j f hf) := by
  rw [spiderDist_point]
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left (show i = i from rfl)]
    rcases le_total d f with h | h
    · obtain ⟨p, hp⟩ := leg_walk (e := e) i d f h hf
      exact ⟨p, by omega⟩
    · obtain ⟨p, hp⟩ := leg_walk (e := e) i f d h hd
      refine ⟨p.reverse, ?_⟩
      rw [Walk.length_reverse]
      omega
  · rw [ite_eq_right hij]
    obtain ⟨p, hp⟩ := leg_walk (e := e) i 0 d (Nat.zero_le _) hd
    obtain ⟨q, hq⟩ := root_walk he hij
    obtain ⟨r, hr⟩ := leg_walk (e := e) j 0 f (Nat.zero_le _) hf
    refine ⟨(p.reverse.append q).append r, ?_⟩
    simp only [Walk.length_append, Walk.length_reverse, hp, hq, hr]
    omega

private theorem spider_walk (he : e ≤ 1) (x y : SpiderVertex e L) :
    ∃ p : (spider e L).Walk x y, p.length = spiderDist x y := by
  rw [← point_coords x, ← point_coords y]
  exact walk_between_points he (leg x) (leg y) (depth x) (depth y) _ _

private theorem spider_dist_eq (he : e ≤ 1) (x y : SpiderVertex e L) :
    (spider e L).dist x y = spiderDist x y := by
  have lower {u v : SpiderVertex e L} (p : (spider e L).Walk u v) :
      spiderDist u v ≤ p.length := by
    induction p with
    | nil => simp [spiderDist]
    | @cons u v w h p ih =>
      have ht := spiderDist_triangle u v w
      change spiderDist u v = 1 at h
      change spiderDist u w ≤ p.length + 1
      omega
  obtain ⟨p, hp⟩ := spider_walk he x y
  obtain ⟨q, hq⟩ := (show (spider e L).Reachable x y from ⟨p⟩).exists_walk_length_eq_dist
  exact le_antisymm (hp ▸ dist_le p) (hq ▸ lower q)

private theorem spider_foot_dist (he : e ≤ 1) {i j : Fin 3} (hij : i ≠ j) :
    (spider e L).dist (foot e L i) (foot e L j) = L i + L j + e := by
  rw [spider_dist_eq he, foot, foot, spiderDist_point, ite_eq_right hij]

end ModelMetric

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
  have hfit := legLength_fits hc a
  let f := project G a (legLength G a) (perimeter G a % 2)
  have hn (x y : V) :
      (spider (perimeter G a % 2) (legLength G a)).dist (f x) (f y) ≤ G.dist x y := by
    rw [spider_dist_eq he]
    exact project_nonexpanding hc he hfit x y
  have hm := packingNum_le_of_surjective_nonexpanding k
    (project_surjective hc he hfit) hn
  have hb := spider_packing_bound he k (legLength G a) (packingNum G k) hm
  have h := perimeter_of_fits hfit
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

/-- Fibers are layers. The central clique has three layers, and every other clique has two. -/
structure CliqueChains {V : Type*} (G : SimpleGraph V) (q : Fin 3 → ℕ)
    (f : V → Vertex q) : Prop where
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

private theorem clique_chains_triameter_ge {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hc : G.Connected)
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

private theorem clique_chains_equality {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hc : G.Connected)
    {q : Fin 3 → ℕ} {f : V → Vertex q} (h : CliqueChains G q f) :
    triameter G = 4 * G.indepNum - 1 ∧ G.indepNum = q 0 + q 1 + q 2 + 1 := by
  have hα := clique_chains_indepNum_le h
  have hlo := clique_chains_triameter_ge hc h
  have hhi := triameter_le_indepNum hc
  exact ⟨by omega, by omega⟩

/-- Hak–Kozerenko Question 1 at k = 1, including connected graphs of order one or two. -/
theorem question1 {V : Type*} [Fintype V] {G : SimpleGraph V} (hc : G.Connected) :
    triameter G = 4 * G.indepNum - 1 ↔
      ∃ (q : Fin 3 → ℕ) (f : V → Vertex q), CliqueChains G q f := by
  refine ⟨equality_clique_chains hc, ?_⟩
  rintro ⟨q, f, h⟩
  exact (clique_chains_equality hc h).1

end D5.S3.Combinatorics.Graph.Triameter
