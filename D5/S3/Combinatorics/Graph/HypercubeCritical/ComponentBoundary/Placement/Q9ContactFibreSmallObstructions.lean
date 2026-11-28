import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9NormalizedContactTranslations
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9EightMaskClauses

/-! Shared exterior rows and the translation action of cubic contact axes give
short obstructions inside a single seven-coordinate fibre. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ContactFibreSmallObstructions

open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip flip_adj)
open BalancedCubeComponentBoundary (directions mem_directions)
open Q9SharedContactCNF (Word Axis)
open Q9SharedContactNormalized (LocalRules)
open Q9FiveAxisMissingContact (Geometry rightRoot)
open D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization (origin)
open Q9MinimumDistanceOperator (minimumDisplacements RidgeContact)
open Q9IsotropicHuang (parity)
open D5.S3.Combinatorics.Graph.HypercubeCritical (cubeBitVec)
open private adjacentWord adjacentWord_spec from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactCNF
open private axesOf xor_mask rootWord rootWord_cube from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9EightMaskClauses
open private row_contact minimumDisplacements_swap_two from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoCenter
open private mem_minimumDisplacements parity_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator

private abbrev vertex (w : Word) : Q 9 := cubeBitVec 9 w

structure Inputs (F : Finset (Finset Axis)) (C D : Finset (Q 9)) : Prop where
  geometry : Geometry C D
  allowed : minimumDisplacements C D false 2 ⊆ F
  translated : ∀ ⦃i j p q : Axis⦄ ⦃x : Q 9⦄, p ≠ q →
    (∀ k, ({i,k} : Finset Axis) ∈ minimumDisplacements C D false 2 → k = j ∨ k = p ∨ k = q) →
    RidgeContact C D false [i] j x → RidgeContact C D false [i] j (flip (flip x p) q)

private theorem leftRoot {F : Finset (Finset Axis)} {C D : Finset (Q 9)} (h : Inputs F C D) :
    vertex 0 ∈ C := by
  have he : vertex 0 = origin := by simpa only [rootWord, Bool.false_eq_true, ite_false] using rootWord_cube false
  exact he.symm ▸ h.geometry.left_root

private theorem rightRoot {F : Finset (Finset Axis)} {C D : Finset (Q 9)} (h : Inputs F C D) :
    vertex 3 ∈ D := by
  have he : vertex 3 = Q9FiveAxisMissingContact.rightRoot := by simpa only [rootWord, ite_true] using rootWord_cube true
  exact he.symm ▸ h.geometry.right_root

private theorem close {F : Finset (Finset Axis)} {C D : Finset (Q 9)} (h : Inputs F C D)
    (x y : Word) (hd : hammingDist (vertex x) (vertex y) ≤ 1) :
    vertex x ∈ C → vertex y ∈ D → False := by
  intro hx hy
  have hs := h.geometry.separated _ hx _ hy
  omega

private theorem absent {F : Finset (Finset Axis)} {C D : Finset (Q 9)} (h : Inputs F C D)
    (x y : Word) (hp : parity (vertex x) = false) (hd : hammingDist (vertex x) (vertex y) = 2)
    (hm : axesOf (x ^^^ y) ∉ F) : vertex x ∈ C → vertex y ∈ D → False := by
  intro hx hy
  apply hm
  rw [← xor_mask]
  exact h.allowed (mem_minimumDisplacements.mpr ⟨_, hx, _, hy, hp, hd, rfl⟩)

private theorem translateWord {F : Finset (Finset Axis)} {C D : Finset (Q 9)} (h : Inputs F C D)
    (x : Word) (i j p q : Axis) (hp : parity (vertex x) = false) (hij : i ≠ j) (hpq : p ≠ q)
    (hcap : ∀ k, ({i,k} : Finset Axis) ∈ F → k = j ∨ k = p ∨ k = q)
    (hx : vertex x ∈ C) (hy : vertex (adjacentWord (adjacentWord x i) j) ∈ D) :
    vertex (adjacentWord (adjacentWord x p) q) ∈ C ∧
      vertex (adjacentWord (adjacentWord (adjacentWord (adjacentWord x p) q) i) j) ∈ D := by
  have hcontact : RidgeContact C D false [i] j (vertex x) := by
    refine ⟨by simpa using hij.symm, hx, hp, ?_⟩
    simpa only [List.foldl_cons, List.foldl_nil, adjacentWord_spec] using hy
  have hnew := h.translated hpq (fun k hk => hcap k (h.allowed hk)) hcontact
  exact ⟨by simpa only [adjacentWord_spec] using hnew.2.1,
    by simpa only [List.foldl_cons, List.foldl_nil, adjacentWord_spec] using hnew.2.2.2⟩

open Classical in
/-- A shared exterior row must have another neighbor in the first support,
and the coordinate of that neighbor is a partner of the opposing direction. -/
theorem shared_row_second {F : Finset (Finset Axis)} {C D : Finset (Q 9)} {b : Bool}
    (hl : LocalRules C) (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y)
    (hallowed : minimumDisplacements C D b 2 ⊆ F)
    {z : Q 9} {i j : Axis} (hp : parity z = !b) (hi : flip z i ∈ C) (hj : flip z j ∈ D) :
    ∃ k, k ≠ i ∧ ({k,j} : Finset Axis) ∈ F ∧ flip z k ∈ C := by
  have hz : z ∉ C := by
    intro hz
    have hs := hsep z hz (flip z j) hj
    have hd : hammingDist z (flip z j) = 1 := flip_adj z j
    omega
  have him : i ∈ directions C z := (mem_directions _ _ _).mpr hi
  have hpos := card_pos.mpr ⟨i, him⟩
  obtain ⟨n, hn⟩ := hl.exterior_degree z hz
  have htwo : 1 < (directions C z).card := by omega
  obtain ⟨k, hk, hki⟩ := exists_mem_ne htwo i
  have hC := (mem_directions _ _ _).mp hk
  have hkj : k ≠ j := by
    intro he
    subst k
    have hs := hsep (flip z j) hC (flip z j) hj
    simp at hs
  have hpar : parity (flip z k) = b := by rw [parity_flip, hp]; cases b <;> rfl
  exact ⟨k, hki, hallowed (row_contact hC hj hkj hpar), hC⟩

private theorem secondLeft {F : Finset (Finset Axis)} {C D : Finset (Q 9)} (h : Inputs F C D)
    (z : Word) (i j : Axis) (hp : parity (vertex z) = true)
    (hi : vertex (adjacentWord z i) ∈ C) (hj : vertex (adjacentWord z j) ∈ D) :
    ∃ k, k ≠ i ∧ ({k,j} : Finset Axis) ∈ F ∧ vertex (adjacentWord z k) ∈ C := by
  simpa only [adjacentWord_spec] using shared_row_second (b := false) h.geometry.left_rules h.geometry.separated h.allowed hp
    (show flip (vertex z) i ∈ C by simpa only [adjacentWord_spec] using hi)
    (show flip (vertex z) j ∈ D by simpa only [adjacentWord_spec] using hj)

private theorem secondRight {F : Finset (Finset Axis)} {C D : Finset (Q 9)} (h : Inputs F C D)
    (z : Word) (i j : Axis) (hp : parity (vertex z) = true)
    (hi : vertex (adjacentWord z i) ∈ C) (hj : vertex (adjacentWord z j) ∈ D) :
    ∃ k, k ≠ j ∧ ({k,i} : Finset Axis) ∈ F ∧ vertex (adjacentWord z k) ∈ D := by
  have hs (x : Q 9) (hx : x ∈ D) (y : Q 9) (hy : y ∈ C) : 2 ≤ hammingDist x y := by
    rw [hammingDist_comm]
    exact h.geometry.separated y hy x hx
  have ha : minimumDisplacements D C false 2 ⊆ F := by
    rw [minimumDisplacements_swap_two D C false]
    exact h.allowed
  simpa only [adjacentWord_spec] using shared_row_second (b := false) h.geometry.right_rules hs ha hp
    (show flip (vertex z) j ∈ D by simpa only [adjacentWord_spec] using hj)
    (show flip (vertex z) i ∈ C by simpa only [adjacentWord_spec] using hi)

/-- Rooted seven-axis contact family FLUmW. -/
def family1 : Finset (Finset Axis) :=
  {axesOf (3 : Word), axesOf (10 : Word), axesOf (12 : Word), axesOf (18 : Word), axesOf (20 : Word), axesOf (33 : Word), axesOf (40 : Word), axesOf (48 : Word), axesOf (65 : Word), axesOf (68 : Word), axesOf (80 : Word), axesOf (96 : Word)}

private theorem logic1 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 : Prop)
    (h1 : p0)
    (h2 : p1)
    (h3 : p0 → p1 → p2)
    (h4 : p0 → p1 → p3)
    (h5 : p0 → p1 → p4)
    (h6 : p0 → p1 → p5)
    (h7 : p0 → p6 → False)
    (h8 : p0 → p7 → p8)
    (h9 : p8 → p1 → False)
    (h10 : p9 → p10 → p11)
    (h11 : p11 → p5 → p12)
    (h12 : p13 → p5 → p14)
    (h13 : p4 → p15 → p16)
    (h14 : p12 → p3 → False)
    (h15 : p2 → p16 → False)
    (h16 : p0 → p1 → p9 ∨ p13)
    (h17 : p9 → p1 → p6 ∨ p10)
    (h18 : p0 → p14 → p15 ∨ p7)
    : False := by
  have step19 : p2 := by
    clear h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
    tauto
  have step20 : p3 := by
    clear h3 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 step19
    tauto
  have step21 : p4 := by
    clear h3 h4 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 step19 step20
    tauto
  have step22 : p5 := by
    clear h3 h4 h5 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 step19 step20 step21
    tauto
  have step23 : ¬p6 := by
    clear h2 h3 h4 h5 h6 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 step19 step20 step21 step22
    tauto
  have step24 : ¬p7 ∨ p8 := by
    clear h2 h3 h4 h5 h6 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 step19 step20 step21 step22 step23
    tauto
  have step25 : ¬p8 := by
    clear h1 h3 h4 h5 h6 h7 h8 h10 h11 h12 h13 h14 h15 h16 h17 h18 step19 step20 step21 step22 step23 step24
    tauto
  have step26 : ¬p7 := by
    clear h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 step19 step20 step21 step22 step23
    tauto
  have step27 : ¬p11 ∨ p12 := by
    clear h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h12 h13 h14 h15 h16 h17 h18 step19 step20 step21 step23 step24 step25 step26
    tauto
  have step28 : ¬p13 ∨ p14 := by
    clear h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h13 h14 h15 h16 h17 h18 step19 step20 step21 step23 step24 step25 step26 step27
    tauto
  have step29 : ¬p15 ∨ p16 := by
    clear h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h14 h15 h16 h17 h18 step19 step20 step22 step23 step24 step25 step26 step27 step28
    tauto
  have step30 : ¬p12 := by
    clear h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h15 h16 h17 h18 step19 step21 step22 step23 step24 step25 step26 step27 step28 step29
    tauto
  have step31 : ¬p11 := by
    clear h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 step19 step20 step21 step22 step23 step24 step25 step26 step28 step29
    tauto
  have step32 : ¬p16 := by
    clear h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h16 h17 h18 step20 step21 step22 step23 step24 step25 step26 step27 step28 step29 step30 step31
    tauto
  have step33 : ¬p15 := by
    clear h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 step19 step20 step21 step22 step23 step24 step25 step26 step27 step28 step30 step31
    tauto
  have step34 : p9 ∨ p13 := by
    clear h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h17 h18 step19 step20 step21 step22 step23 step24 step25 step26 step27 step28 step29 step30 step31 step32 step33
    tauto
  have step35 : ¬p9 ∨ p10 := by
    clear h1 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h18 step19 step20 step21 step22 step24 step25 step26 step27 step28 step29 step30 step31 step32 step33 step34
    tauto
  have step36 : ¬p14 := by
    clear h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 step19 step20 step21 step22 step23 step24 step25 step27 step28 step29 step30 step31 step32 step34 step35
    tauto
  have step37 : ¬p13 := by
    clear h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 step19 step20 step21 step22 step23 step24 step25 step26 step27 step29 step30 step31 step32 step33 step34 step35
    tauto
  have step38 : p9 := by
    clear h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 step19 step20 step21 step22 step23 step24 step25 step26 step27 step28 step29 step30 step31 step32 step33 step35 step36
    tauto
  have step39 : ¬p10 := by
    clear h1 h2 h3 h4 h5 h6 h7 h8 h9 h11 h12 h13 h14 h15 h16 h17 h18 step19 step20 step21 step22 step23 step24 step25 step26 step27 step28 step29 step30 step32 step33 step34 step35 step36 step37
    tauto
  have step40 : False := by
    clear h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 step19 step20 step21 step22 step23 step24 step25 step26 step27 step28 step29 step30 step31 step32 step33 step34 step36 step37
    tauto
  exact step40

/-- The contact at mask three in FLUmW is incompatible with its local orbit. -/
theorem no_family1 {C D : Finset (Q 9)} (h : Inputs family1 C D) : False := by
  have h1 : vertex 0 ∈ C := leftRoot h
  have h2 : vertex 3 ∈ D := rightRoot h
  have h3 : vertex 0 ∈ C → vertex 3 ∈ D → vertex 96 ∈ C := by
    intro hx hy
    exact (translateWord h 0 0 1 5 6 (by decide +kernel) (by decide) (by decide) (by decide +kernel) hx hy).1
  have h4 : vertex 0 ∈ C → vertex 3 ∈ D → vertex 99 ∈ D := by
    intro hx hy
    exact (translateWord h 0 0 1 5 6 (by decide +kernel) (by decide) (by decide) (by decide +kernel) hx hy).2
  have h5 : vertex 0 ∈ C → vertex 3 ∈ D → vertex 24 ∈ C := by
    intro hx hy
    exact (translateWord h 0 1 0 3 4 (by decide +kernel) (by decide) (by decide) (by decide +kernel) hx hy).1
  have h6 : vertex 0 ∈ C → vertex 3 ∈ D → vertex 27 ∈ D := by
    intro hx hy
    exact (translateWord h 0 1 0 3 4 (by decide +kernel) (by decide) (by decide) (by decide +kernel) hx hy).2
  have h7 : vertex 0 ∈ C → vertex 5 ∈ D → False :=
    absent h 0 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h8 : vertex 0 ∈ C → vertex 40 ∈ D → vertex 6 ∈ C := by
    intro hx hy
    exact (translateWord h 0 3 5 1 2 (by decide +kernel) (by decide) (by decide) (by decide +kernel) hx hy).1
  have h9 : vertex 6 ∈ C → vertex 3 ∈ D → False :=
    absent h 6 3 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h10 : vertex 9 ∈ C → vertex 33 ∈ D → vertex 15 ∈ C := by
    intro hx hy
    exact (translateWord h 9 3 5 1 2 (by decide +kernel) (by decide) (by decide) (by decide +kernel) hx hy).1
  have h11 : vertex 15 ∈ C → vertex 27 ∈ D → vertex 71 ∈ C := by
    intro hx hy
    exact (translateWord h 15 2 4 3 6 (by decide +kernel) (by decide) (by decide) (by decide +kernel) hx hy).1
  have h12 : vertex 17 ∈ C → vertex 27 ∈ D → vertex 10 ∈ D := by
    intro hx hy
    exact (translateWord h 17 1 3 0 4 (by decide +kernel) (by decide) (by decide) (by decide +kernel) hx hy).2
  have h13 : vertex 24 ∈ C → vertex 12 ∈ D → vertex 68 ∈ D := by
    intro hx hy
    exact (translateWord h 24 2 4 3 6 (by decide +kernel) (by decide) (by decide) (by decide +kernel) hx hy).2
  have h14 : vertex 71 ∈ C → vertex 99 ∈ D → False :=
    absent h 71 99 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h15 : vertex 96 ∈ C → vertex 68 ∈ D → False :=
    absent h 96 68 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h16 : vertex 0 ∈ C → vertex 3 ∈ D → vertex 9 ∈ C ∨ vertex 17 ∈ C := by
    intro hx hy
    obtain ⟨k, hne, hk, hv⟩ := secondLeft h 1 0 1 (by decide +kernel) hx hy
    have hc : ∀ u : Axis, u ≠ 0 → ({u,1} : Finset Axis) ∈ family1 → u = 3 ∨ u = 4 := by decide +kernel
    rcases hc k hne hk with rfl | rfl
    · exact Or.inl hv
    · exact Or.inr (hv)
  have h17 : vertex 9 ∈ C → vertex 3 ∈ D → vertex 5 ∈ D ∨ vertex 33 ∈ D := by
    intro hx hy
    obtain ⟨k, hne, hk, hv⟩ := secondRight h 1 3 1 (by decide +kernel) hx hy
    have hc : ∀ u : Axis, u ≠ 1 → ({u,3} : Finset Axis) ∈ family1 → u = 2 ∨ u = 5 := by decide +kernel
    rcases hc k hne hk with rfl | rfl
    · exact Or.inl hv
    · exact Or.inr (hv)
  have h18 : vertex 0 ∈ C → vertex 10 ∈ D → vertex 12 ∈ D ∨ vertex 40 ∈ D := by
    intro hx hy
    obtain ⟨k, hne, hk, hv⟩ := secondRight h 8 3 1 (by decide +kernel) hx hy
    have hc : ∀ u : Axis, u ≠ 1 → ({u,3} : Finset Axis) ∈ family1 → u = 2 ∨ u = 5 := by decide +kernel
    rcases hc k hne hk with rfl | rfl
    · exact Or.inl hv
    · exact Or.inr (hv)
  exact logic1
    (vertex 0 ∈ C) (vertex 3 ∈ D) (vertex 96 ∈ C) (vertex 99 ∈ D) (vertex 24 ∈ C) (vertex 27 ∈ D) (vertex 5 ∈ D) (vertex 40 ∈ D) (vertex 6 ∈ C) (vertex 9 ∈ C) (vertex 33 ∈ D) (vertex 15 ∈ C) (vertex 71 ∈ C) (vertex 17 ∈ C) (vertex 10 ∈ D) (vertex 12 ∈ D) (vertex 68 ∈ D)
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18

/-- Rooted seven-axis contact family FBfnO. -/
def family2 : Finset (Finset Axis) :=
  {axesOf (3 : Word), axesOf (18 : Word), axesOf (20 : Word), axesOf (24 : Word), axesOf (33 : Word), axesOf (34 : Word), axesOf (36 : Word), axesOf (40 : Word), axesOf (65 : Word), axesOf (66 : Word), axesOf (68 : Word), axesOf (72 : Word)}

private theorem logic2 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 : Prop)
    (h1 : p0)
    (h2 : p1)
    (h3 : p2 → p1 → False)
    (h4 : p3 → p1 → False)
    (h5 : p4 → p1 → False)
    (h6 : p5 → p6 → False)
    (h7 : p7 → p6 → False)
    (h8 : p8 → p6 → False)
    (h9 : p0 → p1 → p5 ∨ p7 ∨ p8)
    (h10 : p0 → p1 → p9 ∨ p6)
    (h11 : p0 → p9 → p2 ∨ p3 ∨ p4)
    : False := by
  have step12 : ¬p2 := by
    clear h1 h4 h5 h6 h7 h8 h9 h10 h11
    tauto
  have step13 : ¬p3 := by
    clear h1 h3 h5 h6 h7 h8 h9 h10 h11 step12
    tauto
  have step14 : ¬p4 := by
    clear h1 h3 h4 h6 h7 h8 h9 h10 h11 step12 step13
    tauto
  have step15 : p5 ∨ p7 ∨ p8 := by
    clear h3 h4 h5 h6 h7 h8 h10 h11 step12 step13 step14
    tauto
  have step16 : p9 ∨ p6 := by
    clear h3 h4 h5 h6 h7 h8 h9 h11 step12 step13 step14 step15
    tauto
  have step17 : ¬p9 := by
    clear h2 h3 h4 h5 h6 h7 h8 h9 h10 step15 step16
    tauto
  have step18 : p6 := by
    clear h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 step12 step13 step14 step15
    tauto
  have step19 : ¬p5 := by
    clear h1 h2 h3 h4 h5 h7 h8 h9 h10 h11 step12 step13 step14 step15 step16 step17
    tauto
  have step20 : ¬p7 := by
    clear h1 h2 h3 h4 h5 h6 h8 h9 h10 h11 step12 step13 step14 step15 step16 step17 step19
    tauto
  have step21 : ¬p8 := by
    clear h1 h2 h3 h4 h5 h6 h7 h9 h10 h11 step12 step13 step14 step15 step16 step17 step19 step20
    tauto
  have step22 : False := by
    clear h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 step12 step13 step14 step16 step17 step18
    tauto
  exact step22

/-- The contact at mask three in FBfnO is incompatible with its local orbit. -/
theorem no_family2 {C D : Finset (Q 9)} (h : Inputs family2 C D) : False := by
  have h1 : vertex 0 ∈ C := leftRoot h
  have h2 : vertex 3 ∈ D := rightRoot h
  have h3 : vertex 3 ∈ C → vertex 3 ∈ D → False :=
    close h 3 3 (by decide +kernel)
  have h4 : vertex 5 ∈ C → vertex 3 ∈ D → False :=
    absent h 5 3 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h5 : vertex 9 ∈ C → vertex 3 ∈ D → False :=
    absent h 9 3 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h6 : vertex 17 ∈ C → vertex 65 ∈ D → False :=
    absent h 17 65 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h7 : vertex 33 ∈ C → vertex 65 ∈ D → False :=
    absent h 33 65 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h8 : vertex 65 ∈ C → vertex 65 ∈ D → False :=
    close h 65 65 (by decide +kernel)
  have h9 : vertex 0 ∈ C → vertex 3 ∈ D → vertex 17 ∈ C ∨ vertex 33 ∈ C ∨ vertex 65 ∈ C := by
    intro hx hy
    obtain ⟨k, hne, hk, hv⟩ := secondLeft h 1 0 1 (by decide +kernel) hx hy
    have hc : ∀ u : Axis, u ≠ 0 → ({u,1} : Finset Axis) ∈ family2 → u = 4 ∨ u = 5 ∨ u = 6 := by decide +kernel
    rcases hc k hne hk with rfl | rfl | rfl
    · exact Or.inl hv
    · exact Or.inr (Or.inl hv)
    · exact Or.inr (Or.inr (hv))
  have h10 : vertex 0 ∈ C → vertex 3 ∈ D → vertex 33 ∈ D ∨ vertex 65 ∈ D := by
    intro hx hy
    obtain ⟨k, hne, hk, hv⟩ := secondRight h 1 0 1 (by decide +kernel) hx hy
    have hc : ∀ u : Axis, u ≠ 1 → ({u,0} : Finset Axis) ∈ family2 → u = 5 ∨ u = 6 := by decide +kernel
    rcases hc k hne hk with rfl | rfl
    · exact Or.inl hv
    · exact Or.inr (hv)
  have h11 : vertex 0 ∈ C → vertex 33 ∈ D → vertex 3 ∈ C ∨ vertex 5 ∈ C ∨ vertex 9 ∈ C := by
    intro hx hy
    obtain ⟨k, hne, hk, hv⟩ := secondLeft h 1 0 5 (by decide +kernel) hx hy
    have hc : ∀ u : Axis, u ≠ 0 → ({u,5} : Finset Axis) ∈ family2 → u = 1 ∨ u = 2 ∨ u = 3 := by decide +kernel
    rcases hc k hne hk with rfl | rfl | rfl
    · exact Or.inl hv
    · exact Or.inr (Or.inl hv)
    · exact Or.inr (Or.inr (hv))
  exact logic2
    (vertex 0 ∈ C) (vertex 3 ∈ D) (vertex 3 ∈ C) (vertex 5 ∈ C) (vertex 9 ∈ C) (vertex 17 ∈ C) (vertex 65 ∈ D) (vertex 33 ∈ C) (vertex 65 ∈ C) (vertex 33 ∈ D)
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11

/-- Rooted seven-axis contact family FEl~?. -/
def family3 : Finset (Finset Axis) :=
  {axesOf (3 : Word), axesOf (6 : Word), axesOf (17 : Word), axesOf (18 : Word), axesOf (24 : Word), axesOf (34 : Word), axesOf (36 : Word), axesOf (40 : Word), axesOf (48 : Word), axesOf (65 : Word), axesOf (68 : Word), axesOf (72 : Word)}

private theorem logic3 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 : Prop)
    (h1 : p0)
    (h2 : p1)
    (h3 : p0 → p1 → p2)
    (h4 : p0 → p1 → p3)
    (h5 : p4 → p3 → False)
    (h6 : p5 → p3 → p6)
    (h7 : p7 → p1 → False)
    (h8 : p8 → p6 → p9)
    (h9 : p10 → p3 → False)
    (h10 : p11 → p1 → False)
    (h11 : p2 → p12 → False)
    (h12 : p2 → p13 → False)
    (h13 : p14 → p1 → False)
    (h14 : p15 → p16 → False)
    (h15 : p15 → p9 → False)
    (h16 : p17 → p9 → False)
    (h17 : p17 → p16 → False)
    (h18 : p0 → p1 → p5 ∨ p18)
    (h19 : p5 → p1 → p4 ∨ p8 ∨ p10)
    (h20 : p18 → p3 → p11 ∨ p19 ∨ p14)
    (h21 : p2 → p3 → p20 ∨ p11 ∨ p15)
    (h22 : p20 → p3 → p17 ∨ p7)
    (h23 : p19 → p3 → p13 ∨ p12 ∨ p16)
    : False := by
  have step24 : p2 := by
    clear h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23
    tauto
  have step25 : p3 := by
    clear h3 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 step24
    tauto
  have step26 : ¬p4 := by
    clear h1 h2 h3 h4 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 step24
    tauto
  have step27 : ¬p5 ∨ p6 := by
    clear h1 h2 h3 h4 h5 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 step24 step26
    tauto
  have step28 : ¬p7 := by
    clear h1 h3 h4 h5 h6 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 step24 step25 step26 step27
    tauto
  have step29 : ¬p10 := by
    clear h1 h2 h3 h4 h5 h6 h7 h8 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 step24 step26 step27 step28
    tauto
  have step30 : ¬p11 := by
    clear h1 h3 h4 h5 h6 h7 h8 h9 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 step24 step25 step26 step27 step28 step29
    tauto
  have step31 : ¬p12 := by
    clear h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 step25 step26 step27 step28 step29 step30
    tauto
  have step32 : ¬p13 := by
    clear h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 step25 step26 step27 step28 step29 step30 step31
    tauto
  have step33 : ¬p14 := by
    clear h1 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 step24 step25 step26 step27 step28 step29 step30 step31 step32
    tauto
  have step34 : p5 ∨ p18 := by
    clear h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h19 h20 h21 h22 h23 step24 step25 step26 step27 step28 step29 step30 step31 step32 step33
    tauto
  have step35 : ¬p5 ∨ p8 := by
    clear h1 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h20 h21 h22 h23 step24 step25 step27 step28 step30 step31 step32 step33 step34
    tauto
  have step36 : ¬p18 ∨ p19 := by
    clear h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h21 h22 h23 step24 step26 step27 step28 step29 step31 step32 step34 step35
    tauto
  have step37 : p20 ∨ p15 := by
    clear h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h22 h23 step26 step27 step28 step29 step31 step32 step33 step34 step35 step36
    tauto
  have step38 : ¬p20 ∨ p17 := by
    clear h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h23 step24 step26 step27 step29 step30 step31 step32 step33 step34 step35 step36 step37
    tauto
  have step39 : ¬p19 ∨ p16 := by
    clear h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 step24 step26 step27 step28 step29 step30 step33 step34 step35 step36 step37 step38
    tauto
  have step40 : ¬p9 := by
    clear h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h17 h18 h19 h20 h21 h22 h23 step24 step25 step26 step27 step28 step29 step30 step31 step32 step33 step34 step35 step36 step39
    tauto
  have step41 : ¬p16 := by
    clear h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h15 h16 h18 h19 h20 h21 h22 h23 step24 step25 step26 step27 step28 step29 step30 step31 step32 step33 step34 step35 step36 step39 step40
    tauto
  have step42 : ¬p19 := by
    clear h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 step24 step25 step26 step27 step28 step29 step30 step31 step32 step33 step34 step35 step36 step37 step38 step40
    tauto
  have step43 : ¬p18 := by
    clear h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 step24 step25 step26 step27 step28 step29 step30 step31 step32 step33 step34 step35 step37 step38 step39 step40 step41
    tauto
  have step44 : p5 := by
    clear h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 step24 step25 step26 step27 step28 step29 step30 step31 step32 step33 step35 step36 step37 step38 step39 step40 step41 step42
    tauto
  have step45 : p6 := by
    clear h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 step24 step25 step26 step28 step29 step30 step31 step32 step33 step34 step35 step36 step37 step38 step39 step40 step41 step42 step43
    tauto
  have step46 : p8 := by
    clear h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 step24 step25 step26 step27 step28 step29 step30 step31 step32 step33 step34 step36 step37 step38 step39 step40 step41 step42 step43 step45
    tauto
  have step47 : False := by
    clear h1 h2 h3 h4 h5 h6 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 step24 step25 step26 step27 step28 step29 step30 step31 step32 step33 step34 step35 step36 step37 step38 step39 step41 step42 step43 step44
    tauto
  exact step47

/-- The contact at mask three in FEl~? is incompatible with its local orbit. -/
theorem no_family3 {C D : Finset (Q 9)} (h : Inputs family3 C D) : False := by
  have h1 : vertex 0 ∈ C := leftRoot h
  have h2 : vertex 3 ∈ D := rightRoot h
  have h3 : vertex 0 ∈ C → vertex 3 ∈ D → vertex 80 ∈ C := by
    intro hx hy
    exact (translateWord h 0 0 1 4 6 (by decide +kernel) (by decide) (by decide) (by decide +kernel) hx hy).1
  have h4 : vertex 0 ∈ C → vertex 3 ∈ D → vertex 83 ∈ D := by
    intro hx hy
    exact (translateWord h 0 0 1 4 6 (by decide +kernel) (by decide) (by decide) (by decide +kernel) hx hy).2
  have h5 : vertex 17 ∈ C → vertex 83 ∈ D → False :=
    absent h 17 83 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h6 : vertex 18 ∈ C → vertex 83 ∈ D → vertex 95 ∈ D := by
    intro hx hy
    exact (translateWord h 18 6 0 2 3 (by decide +kernel) (by decide) (by decide) (by decide +kernel) hx hy).2
  have h7 : vertex 23 ∈ C → vertex 3 ∈ D → False :=
    absent h 23 3 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h8 : vertex 27 ∈ C → vertex 95 ∈ D → vertex 125 ∈ D := by
    intro hx hy
    exact (translateWord h 27 2 6 1 5 (by decide +kernel) (by decide) (by decide) (by decide +kernel) hx hy).2
  have h9 : vertex 51 ∈ C → vertex 83 ∈ D → False :=
    absent h 51 83 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h10 : vertex 65 ∈ C → vertex 3 ∈ D → False :=
    absent h 65 3 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h11 : vertex 80 ∈ C → vertex 89 ∈ D → False :=
    absent h 80 89 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h12 : vertex 80 ∈ C → vertex 90 ∈ D → False :=
    absent h 80 90 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h13 : vertex 99 ∈ C → vertex 3 ∈ D → False :=
    absent h 99 3 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h14 : vertex 113 ∈ C → vertex 123 ∈ D → False :=
    absent h 113 123 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h15 : vertex 113 ∈ C → vertex 125 ∈ D → False :=
    absent h 113 125 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h16 : vertex 119 ∈ C → vertex 125 ∈ D → False :=
    absent h 119 125 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h17 : vertex 119 ∈ C → vertex 123 ∈ D → False :=
    absent h 119 123 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h18 : vertex 0 ∈ C → vertex 3 ∈ D → vertex 18 ∈ C ∨ vertex 66 ∈ C := by
    intro hx hy
    obtain ⟨k, hne, hk, hv⟩ := secondLeft h 2 1 0 (by decide +kernel) hx hy
    have hc : ∀ u : Axis, u ≠ 1 → ({u,0} : Finset Axis) ∈ family3 → u = 4 ∨ u = 6 := by decide +kernel
    rcases hc k hne hk with rfl | rfl
    · exact Or.inl hv
    · exact Or.inr (hv)
  have h19 : vertex 18 ∈ C → vertex 3 ∈ D → vertex 17 ∈ C ∨ vertex 27 ∈ C ∨ vertex 51 ∈ C := by
    intro hx hy
    obtain ⟨k, hne, hk, hv⟩ := secondLeft h 19 0 4 (by decide +kernel) hx hy
    have hc : ∀ u : Axis, u ≠ 0 → ({u,4} : Finset Axis) ∈ family3 → u = 1 ∨ u = 3 ∨ u = 5 := by decide +kernel
    rcases hc k hne hk with rfl | rfl | rfl
    · exact Or.inl hv
    · exact Or.inr (Or.inl hv)
    · exact Or.inr (Or.inr (hv))
  have h20 : vertex 66 ∈ C → vertex 83 ∈ D → vertex 65 ∈ C ∨ vertex 75 ∈ C ∨ vertex 99 ∈ C := by
    intro hx hy
    obtain ⟨k, hne, hk, hv⟩ := secondLeft h 67 0 4 (by decide +kernel) hx hy
    have hc : ∀ u : Axis, u ≠ 0 → ({u,4} : Finset Axis) ∈ family3 → u = 1 ∨ u = 3 ∨ u = 5 := by decide +kernel
    rcases hc k hne hk with rfl | rfl | rfl
    · exact Or.inl hv
    · exact Or.inr (Or.inl hv)
    · exact Or.inr (Or.inr (hv))
  have h21 : vertex 80 ∈ C → vertex 83 ∈ D → vertex 85 ∈ C ∨ vertex 65 ∈ C ∨ vertex 113 ∈ C := by
    intro hx hy
    obtain ⟨k, hne, hk, hv⟩ := secondLeft h 81 0 1 (by decide +kernel) hx hy
    have hc : ∀ u : Axis, u ≠ 0 → ({u,1} : Finset Axis) ∈ family3 → u = 2 ∨ u = 4 ∨ u = 5 := by decide +kernel
    rcases hc k hne hk with rfl | rfl | rfl
    · exact Or.inl hv
    · exact Or.inr (Or.inl hv)
    · exact Or.inr (Or.inr (hv))
  have h22 : vertex 85 ∈ C → vertex 83 ∈ D → vertex 119 ∈ C ∨ vertex 23 ∈ C := by
    intro hx hy
    obtain ⟨k, hne, hk, hv⟩ := secondLeft h 87 1 2 (by decide +kernel) hx hy
    have hc : ∀ u : Axis, u ≠ 1 → ({u,2} : Finset Axis) ∈ family3 → u = 5 ∨ u = 6 := by decide +kernel
    rcases hc k hne hk with rfl | rfl
    · exact Or.inl hv
    · exact Or.inr (hv)
  have h23 : vertex 75 ∈ C → vertex 83 ∈ D → vertex 90 ∈ D ∨ vertex 89 ∈ D ∨ vertex 123 ∈ D := by
    intro hx hy
    obtain ⟨k, hne, hk, hv⟩ := secondRight h 91 4 3 (by decide +kernel) hx hy
    have hc : ∀ u : Axis, u ≠ 3 → ({u,4} : Finset Axis) ∈ family3 → u = 0 ∨ u = 1 ∨ u = 5 := by decide +kernel
    rcases hc k hne hk with rfl | rfl | rfl
    · exact Or.inl hv
    · exact Or.inr (Or.inl hv)
    · exact Or.inr (Or.inr (hv))
  exact logic3
    (vertex 0 ∈ C) (vertex 3 ∈ D) (vertex 80 ∈ C) (vertex 83 ∈ D) (vertex 17 ∈ C) (vertex 18 ∈ C) (vertex 95 ∈ D) (vertex 23 ∈ C) (vertex 27 ∈ C) (vertex 125 ∈ D) (vertex 51 ∈ C) (vertex 65 ∈ C) (vertex 89 ∈ D) (vertex 90 ∈ D) (vertex 99 ∈ C) (vertex 113 ∈ C) (vertex 123 ∈ D) (vertex 119 ∈ C) (vertex 66 ∈ C) (vertex 75 ∈ C) (vertex 85 ∈ C)
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23

#print axioms no_family1
#print axioms no_family2
#print axioms no_family3

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ContactFibreSmallObstructions
