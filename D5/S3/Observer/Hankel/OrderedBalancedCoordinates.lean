/- GID: D5/S3/Observer/Hankel/OrderedBalancedCoordinates
   generality: G
   mirror-B: D5/B/S3/Observer/Hankel/OrderedBalancedCoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Sort genuine balancing weights and permute the actual realization by the same permutation. -/

import D5.S3.Observer.Hankel.BalancedRealizationTransport
import D5.S3.Observer.Hankel.BalancedHankelSchmidt
import Mathlib.Data.Fin.Tuple.Sort

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Hankel.OrderedBalancedCoordinates

open Matrix
open D5.S3.Observer.Hankel.PositiveGramianBalancing
open D5.S3.Observer.Hankel.BalancedRealizationTransport
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

variable {n m p : ℕ} {P Q : Matrix (Fin n) (Fin n) ℝ}

/-- The library sort applied to negative weights gives descending order;
ties use the original finite index. This does not compute real eigenvalues. -/
def descendingPermutation (w : Fin n → ℝ) : Equiv.Perm (Fin n) :=
  Tuple.sort (fun i => -w i)

theorem descendingPermutation_antitone (w : Fin n → ℝ) :
    Antitone (fun i => w (descendingPermutation w i)) := by
  intro i j hij
  have h := Tuple.monotone_sort (fun i => -w i) hij
  exact neg_le_neg_iff.mp h

private theorem rows_mul (M N : Matrix (Fin n) (Fin n) ℝ) (e : Equiv.Perm (Fin n)) :
    M.submatrix e id * N = (M * N).submatrix e id := by
  simpa only [Equiv.coe_refl, submatrix_id_id] using
    submatrix_mul_equiv M N e (Equiv.refl _) id

private theorem rows_cols (M N : Matrix (Fin n) (Fin n) ℝ) (e : Equiv.Perm (Fin n)) :
    M.submatrix e id * N.submatrix id e = (M * N).submatrix e e := by
  simpa only [Equiv.coe_refl] using submatrix_mul_equiv M N e (Equiv.refl _) e

private theorem diagonal_reindex (w : Fin n → ℝ) (e : Equiv.Perm (Fin n)) :
    (diagonal w).submatrix e e = diagonal (fun i => w (e i)) := by
  ext i j
  by_cases hij : i = j
  · subst j; simp
  · have hne : e i ≠ e j := fun he => hij (e.injective he)
    simp [diagonal, hij, hne]

/-- Apply the same state permutation to both inverse coordinate maps and weights.
All Gramian congruences and inverse identities are re-proved for the result. -/
def reindexCoordinates (b : Coordinates P Q) (e : Equiv.Perm (Fin n)) : Coordinates P Q where
  weight := fun i => b.weight (e i)
  toOriginal := b.toOriginal.submatrix id e
  fromOriginal := b.fromOriginal.submatrix e id
  positive := fun i => b.positive (e i)
  from_to := by
    rw [rows_cols, b.from_to]
    simpa using Matrix.submatrix_one_equiv e
  to_from := by
    rw [submatrix_mul_equiv b.toOriginal b.fromOriginal id e id,
      b.to_from, submatrix_id_id]
  controllability := by
    change b.fromOriginal.submatrix e id * P * b.fromOriginalᴴ.submatrix id e = _
    rw [rows_mul, rows_cols, b.controllability, diagonal_reindex]
  observability := by
    change b.toOriginalᴴ.submatrix e id * Q * b.toOriginal.submatrix id e = _
    rw [rows_mul, rows_cols, b.observability, diagonal_reindex]

/-- Sorting changes the realization coordinates as well as the displayed weights. -/
def orderedCoordinates (b : Coordinates P Q) : Coordinates P Q :=
  reindexCoordinates b (descendingPermutation b.weight)

theorem ordered_weight_antitone (b : Coordinates P Q) : Antitone (orderedCoordinates b).weight :=
  descendingPermutation_antitone b.weight

/-- Every retained coordinate has weight at least every discarded coordinate. -/
theorem retained_weight_ge_discarded (b : Coordinates P Q) (r : ℕ)
    (i j : Fin n) (hi : i.val < r) (hj : r ≤ j.val) :
    (orderedCoordinates b).weight j ≤ (orderedCoordinates b).weight i := by
  apply ordered_weight_antitone b
  change i.val ≤ j.val
  omega

/-- Sorting preserves the entire singular-weight multiset, including multiplicities. -/
theorem ordered_weight_multiset (b : Coordinates P Q) :
    List.Perm (List.ofFn (orderedCoordinates b).weight) (List.ofFn b.weight) := by
  exact (descendingPermutation b.weight).ofFn_comp_perm b.weight

/-- The sorted values are independent of which sorting permutation was chosen.
This asserts uniqueness of values, not of singular vectors in repeated eigenspaces. -/
theorem sorted_values_unique (b : Coordinates P Q) (e : Equiv.Perm (Fin n))
    (he : Antitone (fun i => b.weight (e i))) :
    (fun i => b.weight (e i)) = (orderedCoordinates b).weight := by
  exact Tuple.unique_antitone he (ordered_weight_antitone b)

/-- The transition matrix is genuinely conjugated by the sorting permutation. -/
theorem balancedA_reindex (b : Coordinates P Q) (e : Equiv.Perm (Fin n))
    (A : Matrix (Fin n) (Fin n) ℝ) :
    balancedA (reindexCoordinates b e) A = (balancedA b A).submatrix e e := by
  change b.fromOriginal.submatrix e id * A * b.toOriginal.submatrix id e = _
  rw [rows_mul, rows_cols]
  rfl

/-- The input rows use the same state permutation. -/
theorem balancedB_reindex (b : Coordinates P Q) (e : Equiv.Perm (Fin n))
    (B : Matrix (Fin n) (Fin m) ℝ) :
    balancedB (reindexCoordinates b e) B = (balancedB b B).submatrix e id := by
  simpa only [balancedB, reindexCoordinates, Equiv.coe_refl, submatrix_id_id] using
    submatrix_mul_equiv b.fromOriginal B e (Equiv.refl _) id

/-- The output columns use the same state permutation. -/
theorem balancedC_reindex (b : Coordinates P Q) (e : Equiv.Perm (Fin n))
    (C : Matrix (Fin p) (Fin n) ℝ) :
    balancedC (reindexCoordinates b e) C = (balancedC b C).submatrix id e := by
  simpa only [balancedC, reindexCoordinates, Equiv.coe_refl, submatrix_id_id] using
    submatrix_mul_equiv C b.toOriginal id (Equiv.refl _) e

#print axioms reindexCoordinates
#print axioms retained_weight_ge_discarded

end D5.S3.Observer.Hankel.OrderedBalancedCoordinates
