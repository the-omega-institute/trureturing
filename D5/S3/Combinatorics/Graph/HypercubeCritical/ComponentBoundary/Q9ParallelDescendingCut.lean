/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ParallelDescendingCut
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ParallelDescendingCut
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: A parity-adjusted height excludes three parallel descending edges in a balanced cubic nine-cube. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeThreeCut
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedIncidence
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9PureParityLayers
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.HuangBalancedSymmetry
import D5.S3.Combinatorics.Graph.HypercubeCritical.SixtySixPointSupport.WeightLayerParity
import Batteries.Tactic.OpenPrivate

/-!
# Parallel descending edges in the nine-cube

For Hong–Wu–Xia, §7, Problem 2, a fixed parity class can be designated as the
lower class of an expected ascending edge. Subtracting the indicator of the
other parity class from Boolean weight gives a height that drops by two along
a descending edge and stays constant along an ascending edge.
[arXiv:2610.09483v1](https://arxiv.org/html/2610.09483v1#Thmproblem2)

For a height sublevel cut, internal edges cancel when the cubic degree sums
of the two parity classes are subtracted. A positive cut with at most three
edges therefore has size three. The final step uses
`BalancedCubeThreeCut.singleton_side_of_cut_card_eq_three` to find a singleton
side of the cut. Its three incident edges use distinct directions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ParallelDescendingCut

open scoped BigOperators
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced flip flip_adj flip_flip)
open BalancedCubeComponentBoundary (directions mem_directions directions_card
  regular_directions flip_injective)
open BalancedCubeGirth (adjacent_exists_flip)
open BalancedCubeCut (cutEdges)
open private cubeParity cubeParity_ne_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private parity_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedIncidence
open private trueDirections weight_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixtySixPointSupport.WeightLayerParity

/-- Weight corrected by the parity class expected at the upper endpoint. -/
def height (p : Bool) (x : Q 9) : ℤ :=
  (booleanWeight x : ℤ) - if cubeParity x = p then 0 else 1

/-- Vertices of the support at or below the specified height. -/
def heightSublevel (C : Finset (Q 9)) (p : Bool) (k : ℤ) : Finset (Q 9) :=
  C.filter fun x => height p x ≤ k

open Classical in
/-- Each descending edge is recorded once, with its chosen-parity endpoint first. -/
def descendingEdges (C : Finset (Q 9)) (p : Bool) :
    Finset (Sigma (fun _ : Q 9 => Q 9)) :=
  (C.filter fun x => cubeParity x = p).sigma fun x =>
    C.filter fun y => (hypercube 9).Adj x y ∧ booleanWeight y < booleanWeight x

private theorem mem_descendingEdges_iff {C : Finset (Q 9)} {p : Bool} {x y : Q 9} :
    (⟨x, y⟩ : Sigma (fun _ : Q 9 => Q 9)) ∈ descendingEdges C p ↔
      x ∈ C ∧ cubeParity x = p ∧ y ∈ C ∧
        (hypercube 9).Adj x y ∧ booleanWeight y < booleanWeight x := by
  simp only [descendingEdges, mem_sigma, mem_filter, and_assoc]

private theorem mem_cutEdges_iff {C T : Finset (Q 9)} {x y : Q 9} :
    (⟨x, y⟩ : Sigma (fun _ : Q 9 => Q 9)) ∈ cutEdges C T ↔
      x ∈ T ∧ y ∈ C \ T ∧ (hypercube 9).Adj x y := by
  simp only [cutEdges, mem_sigma, mem_filter]

private theorem weight_flip_int (x : Q 9) (i : Fin 9) :
    (booleanWeight (flip x i) : ℤ) =
      if x i = true then (booleanWeight x : ℤ) - 1 else (booleanWeight x : ℤ) + 1 := by
  have hw := weight_flip x i
  by_cases hi : x i = true
  · have hpos : 0 < booleanWeight x :=
      card_pos.mpr ⟨i, by simp [trueDirections, hi]⟩
    simp only [if_pos hi] at hw ⊢
    omega
  · simp only [if_neg hi] at hw ⊢
    omega

private theorem height_step {p : Bool} {x y : Q 9} (hp : cubeParity x = p)
    (hxy : (hypercube 9).Adj x y) :
    (height p y = height p x ∧ booleanWeight x < booleanWeight y) ∨
      (height p x = height p y + 2 ∧ booleanWeight y < booleanWeight x) := by
  obtain ⟨i, rfl⟩ := adjacent_exists_flip hxy
  have hn : cubeParity (flip x i) ≠ p := by
    rw [parity_flip, hp]
    cases p <;> decide
  have hw := weight_flip_int x i
  simp only [height, if_pos hp, if_neg hn, sub_zero]
  by_cases hi : x i = true
  · simp only [if_pos hi] at hw
    right
    constructor <;> omega
  · simp only [if_neg hi] at hw
    left
    constructor <;> omega

private theorem crossing_of_height_lt {p : Bool} {x y : Q 9}
    (hxy : (hypercube 9).Adj x y) (hheight : height p x < height p y) :
    cubeParity x ≠ p ∧ cubeParity y = p ∧ booleanWeight x < booleanWeight y := by
  have hx : cubeParity x ≠ p := by
    intro hp
    rcases height_step hp hxy with h | h <;> omega
  have hy : cubeParity y = p := by
    have hne := cubeParity_ne_of_adj hxy
    cases hpx : cubeParity x <;> cases hpy : cubeParity y <;> cases p <;> simp_all
  rcases height_step hy hxy.symm with h | h
  · omega
  · exact ⟨hx, hy, h.2⟩

private theorem heightSublevel_crossing {C : Finset (Q 9)} {p : Bool} {k : ℤ}
    {x y : Q 9} (hx : x ∈ heightSublevel C p k) (hy : y ∈ C \ heightSublevel C p k)
    (hxy : (hypercube 9).Adj x y) :
    cubeParity x ≠ p ∧ cubeParity y = p ∧ booleanWeight x < booleanWeight y := by
  have hlo : height p x ≤ k := (mem_filter.mp hx).2
  obtain ⟨hyC, hyT⟩ := mem_sdiff.mp hy
  have hhi : k < height p y := lt_of_not_ge (fun h => hyT (mem_filter.mpr ⟨hyC, h⟩))
  exact crossing_of_height_lt hxy (hlo.trans_lt hhi)

open Classical in
private def edgeCount (S U : Finset (Q 9)) : ℕ :=
  ∑ x ∈ S, (U.filter fun y => (hypercube 9).Adj x y).card

private theorem edgeCount_comm (S U : Finset (Q 9)) : edgeCount S U = edgeCount U S := by
  classical
  simp only [edgeCount, card_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  apply sum_congr rfl
  intro x _
  rw [(hypercube 9).adj_comm x y]

private theorem edgeCount_restrict {S U V : Finset (Q 9)} (hVU : V ⊆ U)
    (h : ∀ x ∈ S, ∀ y ∈ U, (hypercube 9).Adj x y → y ∈ V) :
    edgeCount S U = edgeCount S V := by
  classical
  unfold edgeCount
  apply sum_congr rfl
  intro x hx
  apply congrArg Finset.card
  ext y
  simp only [mem_filter]
  exact ⟨fun ⟨hy, hxy⟩ => ⟨h x hx y hy hxy, hxy⟩,
    fun ⟨hy, hxy⟩ => ⟨hVU hy, hxy⟩⟩

private theorem edgeCount_partition (S : Finset (Q 9)) {C T : Finset (Q 9)}
    (hTC : T ⊆ C) : edgeCount S C = edgeCount S T + edgeCount S (C \ T) := by
  classical
  unfold edgeCount
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro x _
  let N := C.filter fun y => (hypercube 9).Adj x y
  have hin : N.filter (· ∈ T) = T.filter (fun y => (hypercube 9).Adj x y) := by
    ext y
    simp only [N, mem_filter]
    exact ⟨fun ⟨⟨_, hxy⟩, hy⟩ => ⟨hy, hxy⟩,
      fun ⟨hy, hxy⟩ => ⟨⟨hTC hy, hxy⟩, hy⟩⟩
  have hout : N.filter (· ∉ T) = (C \ T).filter (fun y => (hypercube 9).Adj x y) := by
    ext y
    simp only [N, mem_filter, mem_sdiff]
    tauto
  rw [← hin, ← hout, card_filter_add_card_filter_not]

private theorem edgeCount_regular {C S : Finset (Q 9)} (hSC : S ⊆ C)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) :
    edgeCount S C = 3 * S.card := by
  classical
  unfold edgeCount
  calc
    _ = ∑ _x ∈ S, (3 : ℕ) := by
      apply sum_congr rfl
      intro x hx
      rw [← directions_card, regular_directions C hr (hSC hx)]
    _ = _ := by simp [Nat.nsmul_eq_mul, Nat.mul_comm]

private theorem cut_card_eq_degree_difference {C T : Finset (Q 9)} (p : Bool)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hTC : T ⊆ C)
    (hcross : ∀ x ∈ T, ∀ y ∈ C \ T, (hypercube 9).Adj x y → cubeParity x ≠ p) :
    ((cutEdges C T).card : ℤ) =
      3 * ((T.filter fun x => cubeParity x ≠ p).card : ℤ) -
        3 * ((T.filter fun x => cubeParity x = p).card : ℤ) := by
  classical
  let L := T.filter fun x => cubeParity x = p
  let R := T.filter fun x => cubeParity x ≠ p
  have hLT : L ⊆ T := filter_subset _ _
  have hRT : R ⊆ T := filter_subset _ _
  have hl : edgeCount L C = edgeCount L T := by
    apply edgeCount_restrict hTC
    intro x hx y hy hxy
    by_contra hyT
    exact hcross x (hLT hx) y (mem_sdiff.mpr ⟨hy, hyT⟩) hxy (mem_filter.mp hx).2
  have hlr : edgeCount L T = edgeCount L R := by
    apply edgeCount_restrict hRT
    intro x hx y hy hxy
    have hx' : cubeParity x = p := (mem_filter.mp hx).2
    exact mem_filter.mpr ⟨hy, fun hp => cubeParity_ne_of_adj hxy (hx'.trans hp.symm)⟩
  have hrl : edgeCount R T = edgeCount R L := by
    apply edgeCount_restrict hLT
    intro x hx y hy hxy
    have hx' : cubeParity x ≠ p := (mem_filter.mp hx).2
    have hne := cubeParity_ne_of_adj hxy
    have hp : cubeParity y = p := by
      cases hpx : cubeParity x <;> cases hpy : cubeParity y <;> cases p <;> simp_all
    exact mem_filter.mpr ⟨hy, hp⟩
  have hcut : (cutEdges C T).card = edgeCount R (C \ T) := by
    rw [show (cutEdges C T).card = edgeCount T (C \ T) by
      simp only [cutEdges, card_sigma, edgeCount]]
    rw [edgeCount_comm T (C \ T), edgeCount_comm R (C \ T)]
    apply edgeCount_restrict hRT
    intro y hy x hx hyx
    exact mem_filter.mpr ⟨hx, hcross x hx y hy hyx.symm⟩
  have htotal : edgeCount R C = edgeCount L C + (cutEdges C T).card := by
    rw [edgeCount_partition R hTC, hrl, edgeCount_comm R L, ← hlr, ← hl, ← hcut]
  rw [edgeCount_regular (hRT.trans hTC) hr, edgeCount_regular (hLT.trans hTC) hr] at htotal
  change ((cutEdges C T).card : ℤ) = 3 * (R.card : ℤ) - 3 * (L.card : ℤ)
  omega

/-- The boundary of a height sublevel is three times its parity-class
imbalance, with the parity opposite to `p` contributing positively. -/
theorem cut_card_heightSublevel (C : Finset (Q 9)) (p : Bool) (k : ℤ)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) :
    ((cutEdges C (heightSublevel C p k)).card : ℤ) =
      3 * (((heightSublevel C p k).filter fun x => cubeParity x ≠ p).card : ℤ) -
        3 * (((heightSublevel C p k).filter fun x => cubeParity x = p).card : ℤ) := by
  apply cut_card_eq_degree_difference p hr (filter_subset _ _)
  intro x hx y hy hxy
  exact (heightSublevel_crossing hx hy hxy).1

private theorem not_all_neighbours_in_direction {C : Finset (Q 9)} {x : Q 9}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hx : x ∈ C) (j : Fin 9)
    (h : ∀ y ∈ C, (hypercube 9).Adj x y → y = flip x j) : False := by
  have hsub : directions C x ⊆ {j} := by
    intro i hi
    apply mem_singleton.mpr
    exact flip_injective x (h _ ((mem_directions C x i).mp hi) (flip_adj x i))
  have hc := card_le_card hsub
  rw [regular_directions C hr hx, card_singleton] at hc
  omega

/-- A connected Huang-balanced induced cubic subgraph of the nine-cube cannot
have exactly three descending edges from one parity all in a single direction. -/
theorem not_parallel_descending_card_three {C : Finset (Q 9)} (p : Bool) (j : Fin 9)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hconn : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hthree : (descendingEdges C p).card = 3)
    (hparallel : ∀ e ∈ descendingEdges C p, e.2 = flip e.1 j) : False := by
  classical
  have hnonempty : (descendingEdges C p).Nonempty := card_pos.mp (by rw [hthree]; decide)
  obtain ⟨⟨a, b⟩, hab⟩ := hnonempty
  obtain ⟨haC, haP, hbC, hadj, hweight⟩ := mem_descendingEdges_iff.mp hab
  have hdrop : height p a = height p b + 2 := by
    rcases height_step haP hadj with h | h
    · omega
    · exact h.1
  let T := heightSublevel C p (height p b)
  have hTC : T ⊆ C := filter_subset _ _
  have hbT : b ∈ T := mem_filter.mpr ⟨hbC, le_rfl⟩
  have haT : a ∉ T := by
    intro ha
    have hle : height p a ≤ height p b := (mem_filter.mp ha).2
    omega
  have hpos : 0 < (cutEdges C T).card :=
    card_pos.mpr ⟨⟨b, a⟩,
      mem_cutEdges_iff.mpr ⟨hbT, mem_sdiff.mpr ⟨haC, haT⟩, hadj.symm⟩⟩
  have hdesc {x y : Q 9} (hx : x ∈ T) (hy : y ∈ C \ T) (hxy : (hypercube 9).Adj x y) :
      (⟨y, x⟩ : Sigma (fun _ : Q 9 => Q 9)) ∈ descendingEdges C p := by
    have h := heightSublevel_crossing hx hy hxy
    exact mem_descendingEdges_iff.mpr ⟨(mem_sdiff.mp hy).1, h.2.1, hTC hx, hxy.symm, h.2.2⟩
  let swapEnds (e : Sigma (fun _ : Q 9 => Q 9)) : Sigma (fun _ : Q 9 => Q 9) := ⟨e.2, e.1⟩
  have hswap : Function.Involutive swapEnds := by
    rintro ⟨x, y⟩
    rfl
  have hle : (cutEdges C T).card ≤ 3 := by
    rw [← hthree]
    refine card_le_card_of_injOn swapEnds ?_ hswap.injective.injOn
    rintro ⟨x, y⟩ he
    obtain ⟨hx, hy, hxy⟩ := mem_cutEdges_iff.mp he
    exact hdesc hx hy hxy
  have hbalance := cut_card_heightSublevel C p (height p b) hr
  change ((cutEdges C T).card : ℤ) =
    3 * ((T.filter fun x => cubeParity x ≠ p).card : ℤ) -
      3 * ((T.filter fun x => cubeParity x = p).card : ℤ) at hbalance
  have hdiv : (3 : ℤ) ∣ ((cutEdges C T).card : ℤ) := by
    refine ⟨((T.filter fun x => cubeParity x ≠ p).card : ℤ) -
      ((T.filter fun x => cubeParity x = p).card : ℤ), ?_⟩
    rw [mul_sub, hbalance]
  obtain ⟨d, hd⟩ := hdiv
  have hdpos : 0 < d := by omega
  have hdle : d ≤ 1 := by omega
  have hcut : (cutEdges C T).card = 3 := by omega
  have haxis {x y : Q 9} (hx : x ∈ T) (hy : y ∈ C \ T) (hxy : (hypercube 9).Adj x y) :
      x = flip y j :=
    hparallel ⟨y, x⟩ (hdesc hx hy hxy)
  rcases BalancedCubeThreeCut.singleton_side_of_cut_card_eq_three C T hr hb hconn hTC hcut with
    hleft | hright
  · obtain ⟨x, hx⟩ := card_eq_one.mp hleft
    have hxT : x ∈ T := by simp [hx]
    apply not_all_neighbours_in_direction hr (hTC hxT) j
    intro y hyC hxy
    have hyT : y ∉ T := by
      rw [hx]
      exact fun hy => hxy.ne (mem_singleton.mp hy).symm
    have hflip := haxis hxT (mem_sdiff.mpr ⟨hyC, hyT⟩) hxy
    calc
      y = flip (flip y j) j := (flip_flip y j).symm
      _ = flip x j := congrArg (fun z : Q 9 => BalancedCriticalSpectrum.flip z j) hflip.symm
  · obtain ⟨y, hy⟩ := card_eq_one.mp hright
    have hyOut : y ∈ C \ T := by simp [hy]
    apply not_all_neighbours_in_direction hr (mem_sdiff.mp hyOut).1 j
    intro x hxC hyx
    have hxT : x ∈ T := by
      by_contra hxT
      have hxOut : x ∈ C \ T := mem_sdiff.mpr ⟨hxC, hxT⟩
      rw [hy, mem_singleton] at hxOut
      exact hyx.ne hxOut.symm
    exact haxis hxT hyOut hyx.symm

section ProjectedPairs

open Q9OccupiedFibreParity (doubleFibres)
open Q9WeightedSaturation (xorTranslate)
open private dropAxis mem_double_projected_iff from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9CrossWitnessTotal
open private parity_split from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9PureParityLayers
open private translate_flip translate_translate from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.HuangTranslationObstruction
open private translate_adj from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.Q9ParityOverlap
open private parity_xorTranslate from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.Q9TranslationAperiodicity

private theorem translated_parity_eq_iff (t x : Q 9) :
    cubeParity (xorTranslate t x) = cubeParity t ↔ cubeParity x = false := by
  have hp : cubeParity (xorTranslate t x) = cubeParity t + cubeParity x :=
    parity_xorTranslate t x
  rw [hp]
  cases cubeParity t <;> cases cubeParity x <;> decide

private theorem translated_bit_true_iff (t x : Q 9) (i : Fin 9)
    (hx : cubeParity x = false) :
    xorTranslate t x i = true ↔ cubeParity (dropAxis i x) = !(t i) := by
  have hs : cubeParity x = Bool.xor (x i) (cubeParity (dropAxis i x)) := parity_split x i
  rw [hx] at hs
  change Bool.xor (t i) (x i) = true ↔ cubeParity (dropAxis i x) = !(t i)
  generalize ht : t i = a
  generalize hb : x i = b at hs ⊢
  generalize hz : cubeParity (dropAxis i x) = c at hs ⊢
  cases a <;> cases b <;> cases c <;> revert hs <;> decide

private theorem weight_flip_lt_iff (x : Q 9) (i : Fin 9) :
    booleanWeight (flip x i) < booleanWeight x ↔ x i = true := by
  have hw := weight_flip_int x i
  constructor
  · intro h
    by_contra hi
    simp only [if_neg hi] at hw
    omega
  · intro hi
    simp only [if_pos hi] at hw
    omega

/-- If all but one axis have double fibres of a single transverse parity,
the other axis cannot have exactly three double fibres in its opposite
transverse parity. The vector `t` records the selected parity on each axis. -/
theorem not_three_minority_pairs_one_axis {C : Finset (Q 9)} (t : Q 9) (j : Fin 9)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hconn : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hpure : ∀ i : Fin 9, i ≠ j → (doubleFibres C i (!(t i))).card = 0)
    (hthree : (doubleFibres C j (!(t j))).card = 3) : False := by
  classical
  let g := xorTranslate t
  let D := C.image g
  let B := doubleFibres C j (!(t j))
  have hgInv : Function.Involutive g := translate_translate t
  let f : Q 9 ≃ Q 9 := hgInv.toPerm g
  have hg : Function.Injective g := f.injective
  have hgflip (x : Q 9) (i : Fin 9) : g (flip x i) = flip (g x) i :=
    translate_flip t x i
  let e : (hypercube 9) ≃g (hypercube 9) :=
    { toEquiv := f
      map_rel_iff' := by
        intro x y
        exact translate_adj (a := t) (x := x) (y := y) }
  have he : Set.BijOn e (C : Set (Q 9)) (D : Set (Q 9)) := by
    change Set.BijOn g (C : Set (Q 9)) ((C.image g : Finset (Q 9)) : Set (Q 9))
    rw [coe_image]
    exact hg.bijOn_image
  have hconnD := (e.induce he).connected_iff.mp hconn
  obtain ⟨hrD, hbD⟩ :=
    HuangBalancedSymmetry.cube_action_regular_balanced f (Equiv.refl (Fin 9)) hgflip hr hb
  let lift (z : Q 8) : Q 9 := Fin.insertNth (α := fun _ => Bool) j (!(t j)) z
  let edge (z : Q 8) : Sigma (fun _ : Q 9 => Q 9) := ⟨g (lift z), g (flip (lift z) j)⟩
  have hdrop (z : Q 8) : dropAxis j (lift z) = z :=
    Fin.removeNth_insertNth (α := fun _ => Bool) j (!(t j)) z
  have hmaps (z : Q 8) (hz : z ∈ B) : edge z ∈ descendingEdges D (cubeParity t) := by
    have hB : dropAxis j (lift z) ∈ B := by rwa [hdrop]
    obtain ⟨⟨hx, hy⟩, hpar⟩ :=
      (mem_double_projected_iff C j (!(t j)) (lift z)).mp hB
    have hbit : lift z j = !(t j) := Fin.insertNth_apply_same (α := fun _ => Bool) j _ _
    have hpzero : cubeParity (lift z) = false := by
      have hp : cubeParity (lift z) =
          Bool.xor (lift z j) (cubeParity (dropAxis j (lift z))) := parity_split (lift z) j
      rw [hbit, hpar] at hp
      exact hp.trans (by cases t j <;> decide)
    have htrue : g (lift z) j = true := (translated_bit_true_iff t (lift z) j hpzero).mpr hpar
    change (⟨g (lift z), g (flip (lift z) j)⟩ : Sigma (fun _ : Q 9 => Q 9)) ∈
      descendingEdges D (cubeParity t)
    apply mem_descendingEdges_iff.mpr
    refine ⟨mem_image.mpr ⟨_, hx, rfl⟩, (translated_parity_eq_iff t _).mpr hpzero,
      mem_image.mpr ⟨_, hy, rfl⟩, ?_, ?_⟩
    · rw [hgflip]
      exact flip_adj _ _
    · rw [hgflip]
      exact (weight_flip_lt_iff _ _).mpr htrue
  have hsurj (s : Sigma (fun _ : Q 9 => Q 9)) (hs : s ∈ descendingEdges D (cubeParity t)) :
      ∃ z ∈ B, edge z = s := by
    obtain ⟨x, y⟩ := s
    obtain ⟨hx, hp, hy, hadj, hw⟩ := mem_descendingEdges_iff.mp hs
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hx
    obtain ⟨i, rfl⟩ := adjacent_exists_flip hadj
    have hv : flip u i ∈ C := by
      obtain ⟨v, hv, heq⟩ := mem_image.mp hy
      have huv : v = flip u i := hg (heq.trans (hgflip u i).symm)
      exact huv ▸ hv
    have hupar := (translated_parity_eq_iff t u).mp hp
    have hbit := (weight_flip_lt_iff (g u) i).mp hw
    have hproj := (translated_bit_true_iff t u i hupar).mp hbit
    have hmem := (mem_double_projected_iff C i (!(t i)) u).mpr ⟨⟨hu, hv⟩, hproj⟩
    have hij : i = j := by
      by_contra hne
      rw [card_eq_zero.mp (hpure i hne)] at hmem
      exact notMem_empty _ hmem
    subst i
    have hubit : u j = !(t j) := by
      change Bool.xor (t j) (u j) = true at hbit
      revert hbit
      cases t j <;> cases u j <;> decide
    have huLift : lift (dropAxis j u) = u := by
      dsimp only [lift]
      rw [← hubit]
      exact Fin.insertNth_self_removeNth (α := fun _ => Bool) j u
    refine ⟨dropAxis j u, hmem, ?_⟩
    simp only [edge, huLift, hgflip]
  have hcard : B.card = (descendingEdges D (cubeParity t)).card := by
    apply card_bij (fun z _ => edge z) hmaps
    · intro z _ w _ heq
      have hzw : lift z = lift w := hg (congrArg Sigma.fst heq)
      simpa only [hdrop] using congrArg (dropAxis j) hzw
    · intro s hs
      obtain ⟨z, hz, he⟩ := hsurj s hs
      exact ⟨z, hz, he⟩
  refine not_parallel_descending_card_three (cubeParity t) j hrD hbD hconnD
    (hcard.symm.trans hthree) ?_
  intro s hs
  obtain ⟨z, _, rfl⟩ := hsurj s hs
  exact hgflip (lift z) j

end ProjectedPairs

#print axioms cut_card_heightSublevel
#print axioms not_parallel_descending_card_three
#print axioms not_three_minority_pairs_one_axis

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ParallelDescendingCut
