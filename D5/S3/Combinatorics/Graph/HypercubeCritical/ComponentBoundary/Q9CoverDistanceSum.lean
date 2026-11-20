module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Fintype.Prod
public import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi

/-! Bounds on the distance sum of five covers from local rigidity and endpoint counts. -/

open scoped BigOperators

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9CoverDistanceSum

/-- An unordered pair of distinct covers, represented in increasing order. -/
public abbrev CoverPair := {p : Fin 5 × Fin 5 // p.1 < p.2}

private def adjacent (edges : CoverPair → Bool) (i j : Fin 5) : Bool :=
  if h : i < j then edges ⟨(i, j), h⟩
  else if h : j < i then edges ⟨(j, i), h⟩
  else false

private def neighbors (edges : CoverPair → Bool) (i : Fin 5) : Finset (Fin 5) :=
  Finset.univ.filter fun j => adjacent edges i j = true

private def commonNeighbor (edges : CoverPair → Bool) (p : CoverPair) : Bool :=
  decide (∃ k : Fin 5, adjacent edges p.1.1 k = true ∧ adjacent edges p.1.2 k = true)

private def edgeCount (edges : CoverPair → Bool) : ℕ :=
  (Finset.univ.filter fun p => edges p = true).card

private def twoStepCount (edges : CoverPair → Bool) : ℕ :=
  (Finset.univ.filter fun p => commonNeighbor edges p = true).card

set_option maxHeartbeats 2000000 in
-- Kernel reduction checks all 1024 graphs on the ten possible edges.
-- The count includes each pair with a common neighbor only once.
private theorem edgeCount_le_twoStepCount_add_two :
    ∀ edges : CoverPair → Bool, (∀ i, (neighbors edges i).card ≤ 2) →
      edgeCount edges ≤ twoStepCount edges + 2 := by
  decide +kernel

/-- Local distance-four rigidity gives total distance at least 48 across five covers. -/
public theorem distanceSum_ge_48 (D : Fin 5 → Fin 5 → ℕ)
    (hsymm : ∀ i j, D i j = D j i)
    (hmin : ∀ i j, i ≠ j → 4 ≤ D i j)
    (hdegree : ∀ i, (Finset.univ.filter fun j => i ≠ j ∧ D i j = 4).card ≤ 2)
    (htwo : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      D i k = 4 → D j k = 4 → 6 ≤ D i j) :
    48 ≤ ∑ p : CoverPair, D p.1.1 p.1.2 := by
  let edges : CoverPair → Bool := fun p => decide (D p.1.1 p.1.2 = 4)
  have hadj (i j : Fin 5) : adjacent edges i j = true ↔ i ≠ j ∧ D i j = 4 := by
    rcases lt_trichotomy i j with hij | rfl | hji
    · simp [adjacent, edges, hij, ne_of_lt hij]
    · simp [adjacent]
    · simp [adjacent, edges, not_lt_of_gt hji, hji, ne_of_gt hji, hsymm j i]
  have hcounts := edgeCount_le_twoStepCount_add_two edges (fun i => by
    simpa only [neighbors, hadj] using hdegree i)
  have hcard : (Finset.univ : Finset CoverPair).card = 10 := by decide
  let nonedges := (Finset.univ.filter fun p => ¬edges p = true).card
  have hpartition : edgeCount edges + nonedges = 10 := by
    simpa only [hcard, edgeCount, nonedges] using Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset CoverPair)) (fun p => edges p = true)
  have hpair (p : CoverPair) :
      4 + (if ¬edges p = true then 1 else 0) +
        (if commonNeighbor edges p = true then 1 else 0) ≤ D p.1.1 p.1.2 := by
    have hij := ne_of_lt p.2
    by_cases ht : commonNeighbor edges p = true
    · obtain ⟨k, hk1, hk2⟩ := of_decide_eq_true ht
      obtain ⟨hik, hdik⟩ := (hadj _ _).mp hk1
      obtain ⟨hjk, hdjk⟩ := (hadj _ _).mp hk2
      have hsix := htwo _ _ _ hij hik hjk hdik hdjk
      by_cases he : edges p = true <;> simp [he, ht] <;> omega
    · by_cases he : edges p = true
      · have hfour := hmin _ _ hij
        simpa [he, ht] using hfour
      · have hfour := hmin _ _ hij
        have hne : D p.1.1 p.1.2 ≠ 4 := by simpa [edges] using he
        simp [he, ht]
        omega
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset CoverPair)) (fun p _ => hpair p)
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcard,
    Finset.sum_boole] at hsum
  change 10 * 4 + nonedges + twoStepCount edges ≤ _ at hsum
  omega

#check distanceSum_ge_48
#print axioms edgeCount_le_twoStepCount_add_two
#print axioms distanceSum_ge_48

/-- Set the cover's free coordinate to the chosen endpoint bit. -/
@[expose] public def coverEndpoint (word : Fin 9 → Bool) (axis : Fin 9)
    (bit : Bool) (k : Fin 9) : Bool :=
  if k = axis then bit else word k

-- A column entry is absent precisely when the cover is free at that coordinate.
private def activeCount (column : Fin 5 → Option Bool) : ℕ :=
  ∑ i, if column i = none then 1 else 0

private def fixedMismatch : Option Bool → Option Bool → ℕ
  | some b, some c => if b ≠ c then 1 else 0
  | _, _ => 0

private def eitherActive (column : Fin 5 → Option Bool) (p : CoverPair) : ℕ :=
  if column p.1.1 = none ∨ column p.1.2 = none then 1 else 0

set_option maxHeartbeats 1000000 in
-- Kernel reduction checks all 243 columns. A free cover contributes one
-- within-cover pair. Across covers there are two disagreements if either is
-- free and four if both are fixed to opposite bits.
private theorem columnBound :
    ∀ column : Fin 5 → Option Bool,
      activeCount column + (∑ p : CoverPair,
        (4 * fixedMismatch (column p.1.1) (column p.1.2) + 2 * eitherActive column p)) ≤
        24 + activeCount column % 2 := by
  decide +kernel

private theorem chooseEndpointBits (x y : Fin 9 → Bool) (a b : Fin 9) :
    ∃ s t : Bool, ∀ k : Fin 9,
      (if coverEndpoint x a s k ≠ coverEndpoint y b t k then 1 else 0) =
        fixedMismatch (if k = a then none else some (x k))
          (if k = b then none else some (y k)) := by
  by_cases h : a = b
  · subst b
    refine ⟨false, false, fun k => ?_⟩
    by_cases hk : k = a <;> simp [coverEndpoint, fixedMismatch, hk]
  · refine ⟨y a, x b, fun k => ?_⟩
    by_cases ha : k = a
    · subst k
      simp [coverEndpoint, fixedMismatch, h]
    · by_cases hb : k = b
      · subst k
        simp [coverEndpoint, fixedMismatch, ha]
      · simp [coverEndpoint, fixedMismatch, ha, hb]

/-- The endpoint count gives `45 + 4L ≤ 216 + o + 2π`, where `L` sums
inter-cover distances, `o` counts axes with odd multiplicity, and `π` counts
parallel cover pairs. Each `D i j` can be the minimum of the four endpoint distances. -/
public theorem mixedAxis_distanceSum_bound (word : Fin 5 → Fin 9 → Bool) (axis : Fin 5 → Fin 9)
    (D : Fin 5 → Fin 5 → ℕ)
    (hD : ∀ i j s t, D i j ≤ hammingDist (coverEndpoint (word i) (axis i) s)
      (coverEndpoint (word j) (axis j) t)) :
    45 + 4 * (∑ p : CoverPair, D p.1.1 p.1.2) ≤
      216 + (∑ k : Fin 9, (∑ i : Fin 5, (if k = axis i then 1 else 0)) % 2) +
        2 * (∑ p : CoverPair, if axis p.1.1 = axis p.1.2 then 1 else 0) := by
  let column (k : Fin 9) (i : Fin 5) : Option Bool :=
    if k = axis i then none else some (word i k)
  have hactive (k : Fin 9) : activeCount (column k) = ∑ i : Fin 5, if k = axis i then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : k = axis i <;> simp [column, h]
  have hactiveTotal : (∑ k : Fin 9, activeCount (column k)) = 5 := by
    simp_rw [hactive]
    rw [Finset.sum_comm]
    simp
  have hpair (p : CoverPair) :
      (∑ k : Fin 9, eitherActive (column k) p) + (if axis p.1.1 = axis p.1.2 then 1 else 0) = 2 := by
    let axes : Finset (Fin 9) := {axis p.1.1, axis p.1.2}
    have hweight (k : Fin 9) : eitherActive (column k) p = if k ∈ axes then 1 else 0 := by
      by_cases hi : k = axis p.1.1 <;> by_cases hj : k = axis p.1.2 <;>
        simp [eitherActive, column, axes, hi, hj]
    have hfilter : Finset.univ.filter (fun k => k ∈ axes) = axes := by ext k; simp
    simp_rw [hweight, Finset.sum_boole, hfilter]
    by_cases h : axis p.1.1 = axis p.1.2
    · simp [axes, h]
    · simp [axes, Finset.card_pair h, h]
  have hpairTotal : (∑ p : CoverPair, ∑ k : Fin 9, eitherActive (column k) p) +
      (∑ p : CoverPair, if axis p.1.1 = axis p.1.2 then 1 else 0) = 20 := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _ : CoverPair, (2 : ℕ) := Finset.sum_congr rfl fun p _ => hpair p
      _ = 20 := by decide
  have hdistance (p : CoverPair) :
      D p.1.1 p.1.2 ≤ ∑ k : Fin 9, fixedMismatch (column k p.1.1) (column k p.1.2) := by
    obtain ⟨s, t, hbits⟩ := chooseEndpointBits (word p.1.1) (word p.1.2) (axis p.1.1) (axis p.1.2)
    refine (hD _ _ s t).trans_eq ?_
    rw [hammingDist, Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_congr rfl fun k _ => hbits k
  have hdistTotal := Finset.sum_le_sum (s := (Finset.univ : Finset CoverPair)) fun p _ => hdistance p
  have htotal := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 9))) fun k _ => columnBound (column k)
  have hfixedComm :
      (∑ k : Fin 9, ∑ p : CoverPair, fixedMismatch (column k p.1.1) (column k p.1.2)) =
        ∑ p : CoverPair, ∑ k : Fin 9, fixedMismatch (column k p.1.1) (column k p.1.2) :=
    Finset.sum_comm
  have hactiveComm :
      (∑ k : Fin 9, ∑ p : CoverPair, eitherActive (column k) p) =
        ∑ p : CoverPair, ∑ k : Fin 9, eitherActive (column k) p :=
    Finset.sum_comm
  have hbase : (∑ _ : Fin 9, (24 : ℕ)) = 216 := by decide
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hactiveTotal, hfixedComm, hactiveComm, hbase] at htotal
  simp_rw [hactive] at htotal
  omega

#check mixedAxis_distanceSum_bound
#print axioms columnBound
#print axioms mixedAxis_distanceSum_bound

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9CoverDistanceSum
