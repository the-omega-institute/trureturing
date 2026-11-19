import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourEmbeddingCheck
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoReconstruction

/-! The integer operations in the embedding search compute Hamming distance
and the same Huang parity reconstruction as for the twenty-two-point half. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourCubeMetric

open Finset SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q)
local notation "cubeFlip" => BalancedCriticalSpectrum.flip
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private hamming closedNeighborhood oppositeSize from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourEmbeddingCheck
open private neighborMask reconstructionSize from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoSingletonPlacements

private theorem hamming_zero (x : BitVec 8) :
    hamming x.toNat 0 = hammingDist (cubeBitVec 8 x) (cubeBitVec 8 0) := by
  decide +revert +kernel

private theorem hamming_encoded (x y : BitVec 8) :
    hamming x.toNat y.toNat = hammingDist (cubeBitVec 8 x) (cubeBitVec 8 y) := by
  have h₁ : hamming x.toNat y.toNat = hamming (x ^^^ y).toNat 0 := by
    simp only [hamming, BitVec.toNat_xor, Nat.xor_zero]
  rw [h₁, hamming_zero]
  unfold hammingDist
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and]
  change ((x ^^^ y).getLsbD i.val ≠ (0 : BitVec 8).getLsbD i.val) ↔
    x.getLsbD i.val ≠ y.getLsbD i.val
  rw [BitVec.getLsbD_xor,
    show (0 : BitVec 8).getLsbD i.val = false from Nat.zero_testBit _]
  cases x.getLsbD i.val <;> cases y.getLsbD i.val <;> decide

private theorem flip_dist_parity {n : Nat} (x y : Q n) (i : Fin n) :
    hammingDist (cubeFlip x i) y % 2 = (hammingDist x y + 1) % 2 := by
  let s := univ.filter (fun j => x j ≠ y j)
  let t := univ.filter (fun j => cubeFlip x i j ≠ y j)
  have he : s.erase i = t.erase i := by
    ext j
    by_cases h : j = i
    · subst j
      simp
    · simp only [mem_erase, h, not_false_eq_true, true_and, s, t, mem_filter, mem_univ]
      rw [BalancedCriticalSpectrum.flip, Function.update_of_ne h]
  have hm : i ∈ s ↔ i ∉ t := by
    simp only [s, t, mem_filter, mem_univ, true_and, BalancedCriticalSpectrum.flip_apply_same]
    cases x i <;> cases y i <;> decide
  change t.card % 2 = (s.card + 1) % 2
  by_cases h : i ∈ s
  · have hn := hm.mp h
    have hs := card_erase_add_one h
    rw [he, erase_eq_of_notMem hn] at hs
    omega
  · have ht : i ∈ t := Classical.not_not.mp (fun hn => h (hm.mpr hn))
    have hs := card_erase_add_one ht
    rw [← he, erase_eq_of_notMem h] at hs
    omega

private theorem walk_dist {V : Type*} {G : SimpleGraph V} {n : Nat} (f : V → Q n)
    (hf : ∀ {x y}, G.Adj x y → (hypercube n).Adj (f x) (f y))
    {x y : V} (w : G.Walk x y) :
    hammingDist (f x) (f y) ≤ w.length ∧ hammingDist (f x) (f y) % 2 = w.length % 2 := by
  induction w with
  | nil => simp
  | @cons x u y e p ih =>
    have hadj : (hypercube n).Adj (f x) (f u) := hf e
    have hd : hammingDist (f x) (f u) = 1 := hadj
    have htri := hammingDist_triangle (f x) (f u) (f y)
    obtain ⟨axis, ha⟩ := adjacent_exists_flip hadj.symm
    have hp : hammingDist (f x) (f y) % 2 = (hammingDist (f u) (f y) + 1) % 2 := by
      rw [ha]
      exact flip_dist_parity _ _ _
    rw [Walk.length_cons]
    exact ⟨by omega, by omega⟩

private def liftPoint (p : Nat) : BitVec 9 := BitVec.ofNat 9 (2 * p)

set_option maxRecDepth 4096 in
private theorem closedNeighborhood_lift (p : Fin 256) :
    closedNeighborhood p.val = neighborMask (liftPoint p.val) := by
  decide +revert +kernel

private theorem oppositeSize_lift (points : List Nat) (h : ∀ p ∈ points, p < 256) :
    oppositeSize points = reconstructionSize (points.map liftPoint) := by
  have fold_eq (l : List Nat) (h : ∀ p ∈ l, p < 256) (acc : Nat) :
      l.foldl (fun mask p => mask ^^^ closedNeighborhood p) acc =
        (l.map liftPoint).foldl (fun mask p => mask ^^^ neighborMask p) acc := by
    induction l generalizing acc with
    | nil => rfl
    | cons p l ih =>
      have hp := closedNeighborhood_lift ⟨p, h p (List.mem_cons_self ..)⟩
      simp only [List.foldl_cons, List.map_cons, hp]
      exact ih (fun q hq => h q (List.mem_cons_of_mem _ hq)) _
  change (List.range 256).countP
      (fun n => (points.foldl (fun mask p => mask ^^^ closedNeighborhood p) 0).testBit n) =
    (List.range 256).countP
      (fun n => ((points.map liftPoint).foldl (fun mask p => mask ^^^ neighborMask p) 0).testBit n)
  rw [fold_eq points h 0]

#print axioms walk_dist
#print axioms hamming_encoded
#print axioms oppositeSize_lift

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourCubeMetric
