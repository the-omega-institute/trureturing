/- GID: D5/S3/Combinatorics/Graph/LeapGroups/SchachnerUdellQuestion54
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LeapGroups/SchachnerUdellQuestion54
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Leap groups of all prisms and positive-dimensional cubes. -/

import D5.S3.Arith.FibonacciAtomic.Observer.SparseLiteralParityReadLowerBound
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.CubicContactDistance
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.GroupTheory.Perm.Sign
import D5.S3.Combinatorics.Graph.LeapGroups.LeapGroup

set_option autoImplicit false

open Equiv Set MulAction Pointwise SimpleGraph Finset
open D5.S3.Combinatorics.Graph.Hypercube D5.S3.Combinatorics.Graph.LeapGroups.LeapGroup
open D5.S3.Combinatorics.Graph.HypercubeCritical
open D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement

open D5.S3.Arith.FibonacciAtomic.Observer

namespace D5.S3.Combinatorics.Graph.LeapGroups.SchachnerUdellQuestion54

noncomputable section
open scoped BigOperators

-- Keep the ring instances used by the frozen statements on the parity carrier.
attribute [-instance] ZMod.instField

/-- The Cartesian product of the two-vertex complete graph and the cyclic graph. -/
def prism (n : ℕ) : SimpleGraph (ZMod 2 × ZMod n) :=
  (⊤ : SimpleGraph (ZMod 2)) □ circulantGraph ({1} : Set (ZMod n))

private theorem prism_adj_iff {n : ℕ} (hn : 3 ≤ n) (x y : ZMod 2 × ZMod n) :
    (prism n).Adj x y ↔
      (x.1 ≠ y.1 ∧ x.2 = y.2) ∨
      ((y.2 = x.2 + 1 ∨ x.2 = y.2 + 1) ∧ x.1 = y.1) := by
  have h1 : (1 : ZMod n) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff 1 n).mp (by simpa using h)
    have := Nat.le_of_dvd (by decide : 0 < 1) hd
    omega
  have cyc (u v : ZMod n) :
      (circulantGraph ({1} : Set (ZMod n))).Adj u v ↔
        v = u + 1 ∨ u = v + 1 := by
    simp only [circulantGraph_adj, Set.mem_singleton_iff]
    constructor
    · rintro ⟨_, h | h⟩
      · exact Or.inr (by simpa [add_comm] using sub_eq_iff_eq_add.mp h)
      · exact Or.inl (by simpa [add_comm] using sub_eq_iff_eq_add.mp h)
    · intro h
      have huv : u ≠ v := by
        intro he
        rcases h with h | h <;> rw [he] at h <;>
          exact h1 (by simpa using (add_left_cancel (show v + 1 = v + 0 by simpa using h.symm)))
      refine ⟨huv, ?_⟩
      rcases h with h | h
      · exact Or.inr (sub_eq_iff_eq_add.mpr (by simpa [add_comm] using h))
      · exact Or.inl (sub_eq_iff_eq_add.mpr (by simpa [add_comm] using h))
  simp only [prism, boxProd_adj, top_adj, cyc]

private def rung {n : ℕ} : Perm (ZMod 2 × ZMod n) where
  toFun x := (x.1+1, x.2)
  invFun x := (x.1+1, x.2)
  left_inv x := by simp [add_assoc, CharTwo.add_self_eq_zero (1 : ZMod 2)]
  right_inv x := by simp [add_assoc, CharTwo.add_self_eq_zero (1 : ZMod 2)]

private theorem rung_hop {n : ℕ} (hn : 3 ≤ n) : IsHop (prism n) rung := by
  intro x
  apply (prism_adj_iff hn _ _).mpr
  left
  change x.1 ≠ x.1+1 ∧ x.2 = x.2
  constructor
  · intro h
    have he : x.1 + 0 = x.1 + 1 := by rw [add_zero]; exact h
    exact zero_ne_one (add_left_cancel he)
  · rfl

private def advance {n : ℕ} (x : ZMod 2 × ZMod n) : ZMod 2 × ZMod n :=
  (x.1+1, x.2+1)

private theorem prism_advance_swap {n : ℕ} (hn : 3 ≤ n) (x : ZMod 2 × ZMod n) :
    swap x (advance x) ∈ leapGroup (prism n) := by
  apply swap_mem_of_cross_edges _ (rung_hop hn)
  · apply (prism_adj_iff hn _ _).mpr
    right
    exact ⟨Or.inl rfl, rfl⟩
  · apply (prism_adj_iff hn _ _).mpr
    right
    refine ⟨Or.inr rfl, ?_⟩
    change x.1 + 1 + 1 = x.1
    simp [add_assoc, CharTwo.add_self_eq_zero (1 : ZMod 2)]

private def advanceBy {n : ℕ} (x : ZMod 2 × ZMod n) (k : ℕ) : ZMod 2 × ZMod n :=
  (x.1+(k : ZMod 2), x.2+(k : ZMod n))

private theorem advanceBy_succ {n : ℕ} (x : ZMod 2 × ZMod n) (k : ℕ) :
    advanceBy x (k+1) = advance (advanceBy x k) := by
  simp [advanceBy, advance, Nat.cast_succ, add_assoc]

private theorem prism_advanceBy_swap {n : ℕ} (hn : 3 ≤ n) (x : ZMod 2 × ZMod n) (k : ℕ) :
    swap x (advanceBy x k) ∈ leapGroup (prism n) := by
  induction k with
  | zero =>
    have h : advanceBy x 0 = x := by simp [advanceBy]
    rw [h, swap_self]
    exact one_mem _
  | succ k ih =>
    rw [advanceBy_succ]
    exact SubmonoidClass.swap_mem_trans _ ih (prism_advance_swap hn _)

private theorem advanceBy_second {n : ℕ} (hn : 3 ≤ n) (x y : ZMod 2 × ZMod n) :
    (advanceBy x (y.2-x.2).val).2 = y.2 := by
  let : NeZero n := ⟨by omega⟩
  simp [advanceBy]

private theorem prism_odd_all_swaps {n : ℕ} (hn : 3 ≤ n) (ho : Odd n) (x y : ZMod 2 × ZMod n) :
    swap x y ∈ leapGroup (prism n) := by
  let k := (y.2-x.2).val
  have hsecond : (advanceBy x k).2 = y.2 := advanceBy_second hn x y
  by_cases hfirst : (advanceBy x k).1 = y.1
  · have he : advanceBy x k = y := Prod.ext hfirst hsecond
    rw [← he]
    exact prism_advanceBy_swap hn x k
  · have he : advanceBy x (k+n) = y := by
      apply Prod.ext
      · change x.1 + ((k+n : ℕ) : ZMod 2) = y.1
        rw [Nat.cast_add, ho.natCast_zmod_two, ← add_assoc]
        change (advanceBy x k).1 + 1 = y.1
        rcases (show (advanceBy x k).1 = 0 ∨ (advanceBy x k).1 = 1 from
          (Fin.exists_fin_two (p := ((advanceBy x k).1 = ·))).mp ⟨(advanceBy x k).1, rfl⟩) with h0 | h1 <;>
          rcases (show y.1 = 0 ∨ y.1 = 1 from
            (Fin.exists_fin_two (p := (y.1 = ·))).mp ⟨y.1, rfl⟩) with hy0 | hy1 <;>
          simp_all [CharTwo.add_self_eq_zero (1 : ZMod 2)]
      · change x.2 + ((k+n : ℕ) : ZMod n) = y.2
        rw [Nat.cast_add, ZMod.natCast_self, add_zero]
        exact hsecond
    rw [← he]
    exact prism_advanceBy_swap hn x (k+n)

/-- The odd prism leap group is the full symmetric group on the original vertices. -/
private theorem prism_odd {n : ℕ} (hn : 3 ≤ n) (ho : Odd n) :
    leapGroup (prism n) = ⊤ := by
  let : NeZero n := ⟨by omega⟩
  apply top_unique
  rw [← Equiv.Perm.closure_isSwap]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨x, y, _, rfl⟩
  exact prism_odd_all_swaps hn ho x y

/-- The parity b+i modulo two. -/
def prismParity {n : ℕ} (h : 2 ∣ n) (x : ZMod 2 × ZMod n) : ZMod 2 :=
  x.1 + ZMod.castHom h (ZMod 2) x.2

private theorem prism_adj_flip {n : ℕ} (hn : 3 ≤ n) (h : 2 ∣ n)
    (x y : ZMod 2 × ZMod n) (ha : (prism n).Adj x y) :
    prismParity h y = prismParity h x + 1 := by
  rcases (prism_adj_iff hn x y).mp ha with ⟨hb, hi⟩ | ⟨hi, hb⟩
  · have hf : y.1 = x.1 + 1 := by
      rcases (show x.1 = 0 ∨ x.1 = 1 from
        (Fin.exists_fin_two (p := (x.1 = ·))).mp ⟨x.1, rfl⟩) with h0 | h1 <;>
        rcases (show y.1 = 0 ∨ y.1 = 1 from
          (Fin.exists_fin_two (p := (y.1 = ·))).mp ⟨y.1, rfl⟩) with hy0 | hy1 <;>
        simp_all [CharTwo.add_self_eq_zero (1 : ZMod 2)]
    simp [prismParity, hf, hi, add_right_comm]
  · rcases hi with hi | hi
    · simp only [prismParity, hi, hb, map_add, map_one, add_assoc]
    · have hcast : ZMod.castHom h (ZMod 2) y.2 =
          ZMod.castHom h (ZMod 2) x.2 + 1 := by
        rw [hi, map_add, map_one, add_assoc]
        simp [CharTwo.add_self_eq_zero (1 : ZMod 2)]
      simp [prismParity, hb, hcast, add_assoc]

private theorem advanceBy_parity {n : ℕ} (h : 2 ∣ n) (x : ZMod 2 × ZMod n) (k : ℕ) :
    prismParity h (advanceBy x k) = prismParity h x := by
  simp only [prismParity, advanceBy, map_add, map_natCast]
  calc
    x.1 + (k : ZMod 2) + (ZMod.castHom h (ZMod 2) x.2 + (k : ZMod 2)) =
        (x.1 + ZMod.castHom h (ZMod 2) x.2) + ((k : ZMod 2) + (k : ZMod 2)) := by ac_rfl
    _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]

private theorem prism_even_same_class_swaps {n : ℕ} (hn : 3 ≤ n) (h : 2 ∣ n)
    (x y : ZMod 2 × ZMod n) (hp : prismParity h x = prismParity h y) :
    swap x y ∈ leapGroup (prism n) := by
  let k := (y.2-x.2).val
  have hsecond : (advanceBy x k).2 = y.2 := advanceBy_second hn x y
  have hpar := (advanceBy_parity h x k).trans hp
  unfold prismParity at hpar
  rw [hsecond] at hpar
  have hfirst := add_right_cancel hpar
  have he : advanceBy x k = y := Prod.ext hfirst hsecond
  rw [← he]
  exact prism_advanceBy_swap hn x k

/-- Exact subgroup equality for every even prism of cycle length at least four. -/
private theorem prism_even {n : ℕ} (hn : 4 ≤ n) (h : 2 ∣ n) :
    leapGroup (prism n) = parityStabilizer (prismParity h) := by
  let : NeZero n := ⟨by omega⟩
  have hn' : 3 ≤ n := by omega
  exact eq_parityStabilizer _ _ (prism_adj_flip hn' h) (prism_even_same_class_swaps hn' h)
    rung (rung_hop hn')

/-- The parity of the Hamming weight of a Boolean vertex. -/
def cubeParity {n : ℕ} (x : Fin n → Bool) : ZMod 2 :=
  ∑ i, if x i then 1 else 0

/-- Change exactly the specified Boolean coordinate. -/
private def cubeFlip {n : ℕ} (i : Fin n) : Perm (Fin n → Bool) where
  toFun x := BalancedCriticalSpectrum.flip x i
  invFun x := BalancedCriticalSpectrum.flip x i
  left_inv x := BalancedCriticalSpectrum.flip_flip x i
  right_inv x := BalancedCriticalSpectrum.flip_flip x i

@[simp] private theorem cubeFlip_symm {n : ℕ} (i : Fin n) : (cubeFlip i).symm = cubeFlip i := by
  ext x j
  rfl

private theorem cubeFlip_hop {n : ℕ} (i : Fin n) : IsHop (hypercube n) (cubeFlip i) := by
  intro x
  exact BalancedCriticalSpectrum.flip_adj x i

private theorem cubeFlip_comm {n : ℕ} (i j : Fin n) (x : Fin n → Bool) :
    cubeFlip i (cubeFlip j x) = cubeFlip j (cubeFlip i x) :=
  BalancedCubeGirth.flip_comm x j i

private theorem cube_double_flip_swap {n : ℕ} (i j : Fin n) (x : Fin n → Bool) :
    swap x (cubeFlip j (cubeFlip i x)) ∈ leapGroup (hypercube n) := by
  classical
  apply swap_mem_of_cross_edges _ (cubeFlip_hop i)
  · rw [cubeFlip_symm]
    exact cubeFlip_hop j _
  · rw [cubeFlip_symm, cubeFlip_comm i j]
    have he : cubeFlip i (cubeFlip i x) = x := by
      rw [← cubeFlip_symm i]
      exact (cubeFlip i).symm_apply_apply _
    rw [he]
    exact (cubeFlip_hop j x).symm

private def bitToZMod (b : Bool) : ZMod 2 := if b then 1 else 0

private theorem cubeParity_eq_map {n : ℕ} (x : Fin n → Bool) :
    cubeParity x = bitToZMod (SparseLiteralParityReadLowerBound.parity x) := by
  have hcast : cubeParity x = ((∑ i, (x i).toNat : ℕ) : ZMod 2) := by
    rw [cubeParity, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    cases x i <;> rfl
  have hval := (congrArg ZMod.val hcast).trans (ZMod.val_natCast 2 _)
  unfold SparseLiteralParityReadLowerBound.parity
  rw [← hval]
  rcases (Fin.exists_fin_two (p := (cubeParity x = ·))).mp ⟨cubeParity x, rfl⟩ with h | h <;>
    rw [h] <;> rfl

private theorem cubeParity_flip {n : ℕ} (i : Fin n) (x : Fin n → Bool) :
    cubeParity (cubeFlip i x) = cubeParity x + 1 := by
  change cubeParity (BalancedCriticalSpectrum.flip x i) = _
  rw [cubeParity_eq_map, cubeParity_eq_map]
  have h : SparseLiteralParityReadLowerBound.parity (BalancedCriticalSpectrum.flip x i) ≠
      SparseLiteralParityReadLowerBound.parity x :=
    SparseLiteralParityReadLowerBound.parity_flip x i
  generalize hx : SparseLiteralParityReadLowerBound.parity x = a at h ⊢
  generalize hy : SparseLiteralParityReadLowerBound.parity (BalancedCriticalSpectrum.flip x i) = b at h ⊢
  cases a <;> cases b <;> first | contradiction | decide

private theorem cube_adj_iff {n : ℕ} (x y : Fin n → Bool) :
    (hypercube n).Adj x y ↔ ∃ i, y = cubeFlip i x := by
  refine ⟨BalancedCubeGirth.adjacent_exists_flip, ?_⟩
  rintro ⟨i, rfl⟩
  exact cubeFlip_hop i x

private theorem cube_adj_flip {n : ℕ} (x y : Fin n → Bool) (h : (hypercube n).Adj x y) :
    cubeParity y = cubeParity x + 1 := by
  obtain ⟨i, rfl⟩ := (cube_adj_iff x y).mp h
  exact cubeParity_flip i x

private theorem cubeFlip_dist_decreases {n : ℕ} (x y : Fin n → Bool) (i : Fin n)
    (hi : x i ≠ y i) :
    hammingDist (cubeFlip i x) y = hammingDist x y - 1 :=
  Nat.eq_sub_of_add_eq (CubicContactDistance.hamming_flip_of_ne hi)

/-- Two coordinates are corrected at each induction step, with parity restored. -/
private theorem cube_same_class_swaps {n : ℕ} (x y : Fin n → Bool)
    (hp : cubeParity x = cubeParity y) :
    swap x y ∈ leapGroup (hypercube n) := by
  classical
  generalize hm : hammingDist x y = m
  induction m using Nat.strong_induction_on generalizing x with
  | h m ih =>
    by_cases he : x = y
    · rw [he, swap_self]
      exact one_mem _
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp he
      have hdist := cubeFlip_dist_decreases x y i hi
      have hn : cubeFlip i x ≠ y := by
        intro he'
        have hh := cubeParity_flip i x
        rw [he', hp] at hh
        have heq : cubeParity y + 0 = cubeParity y + 1 := by rw [add_zero]; exact hh
        exact zero_ne_one (add_left_cancel heq)
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hn
      have hdist' := cubeFlip_dist_decreases (cubeFlip i x) y j hj
      have hp' : cubeParity (cubeFlip j (cubeFlip i x)) = cubeParity y := by
        rw [cubeParity_flip, cubeParity_flip, hp, add_assoc]
        simp [CharTwo.add_self_eq_zero (1 : ZMod 2)]
      have hpos : 0 < m := by
        rw [← hm]
        exact hammingDist_pos.mpr he
      have hlt : hammingDist (cubeFlip j (cubeFlip i x)) y < m := by omega
      exact SubmonoidClass.swap_mem_trans _ (cube_double_flip_swap i j x)
        (ih _ hlt _ hp' rfl)

/-- Exact subgroup equality for every positive-dimensional hypercube. -/
private theorem cube_positive {n : ℕ} (hn : 1 ≤ n) :
    leapGroup (hypercube n) = parityStabilizer (cubeParity (n := n)) := by
  let i : Fin n := ⟨0, by omega⟩
  exact eq_parityStabilizer _ _ cube_adj_flip cube_same_class_swaps
    (cubeFlip i) (cubeFlip_hop i)

/-- Schachner–Udell Question 5.4, with all three unbounded clauses on the original
vertex permutation groups. The stabilizers here are of the actual unordered
pair of parity classes. -/
theorem result :
    (∀ n : ℕ, 3 ≤ n → Odd n → leapGroup (prism n) = ⊤) ∧
    (∀ (n : ℕ), 4 ≤ n → ∀ h : 2 ∣ n,
      leapGroup (prism n) =
        MulAction.stabilizer (Perm (ZMod 2 × ZMod n))
          ({{x | prismParity h x = 0}, {x | prismParity h x = 1}} :
            Set (Set (ZMod 2 × ZMod n)))) ∧
    (∀ n : ℕ, 1 ≤ n →
      leapGroup (hypercube n) =
        MulAction.stabilizer (Perm (Fin n → Bool))
          ({{x | cubeParity x = 0}, {x | cubeParity x = 1}} :
            Set (Set (Fin n → Bool)))) := by
  refine ⟨fun n hn ho => prism_odd hn ho, ?_, ?_⟩
  · intro n hn h
    rw [prism_even hn h, parityStabilizer]
  · intro n hn
    rw [cube_positive hn, parityStabilizer]

end
end D5.S3.Combinatorics.Graph.LeapGroups.SchachnerUdellQuestion54
