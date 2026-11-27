/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9ThreeAxisCapacityTransport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9ThreeAxisCapacityTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.ToLinearEquiv]
   utility: none
   digest: Masked Huang rank loss forces distinct four-faces with bounded room for other components. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9FourFaceDefect
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedBoundaryGram
import Mathlib.Data.Fintype.EquivFin
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9DominantAxisBoundary

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CubeCoordinateFace

open BalancedCriticalSpectrum (Q flip)
open BalancedCubeComponentBoundary (directions mem_directions)
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)

noncomputable section

variable {m n : ℕ}

/-- Fill the inactive coordinates with the fixed word and the active ones with the input. -/
private def lift (e : Fin m ↪ Fin n) (fixed : Q n) (x : Q m) : Q n :=
  Function.extend e x fixed

@[simp] private theorem lift_active (e : Fin m ↪ Fin n) (fixed : Q n) (x : Q m) (j : Fin m) :
    lift e fixed x (e j) = x j :=
  e.injective.extend_apply _ _ j

private theorem lift_inactive (e : Fin m ↪ Fin n) (fixed : Q n) (x : Q m) {i : Fin n}
    (h : ¬ ∃ j, e j = i) : lift e fixed x i = fixed i :=
  Function.extend_apply' _ _ _ h

private theorem lift_injective (e : Fin m ↪ Fin n) (fixed : Q n) :
    Function.Injective (lift e fixed) := by
  intro x y h
  funext j
  simpa using congrFun h (e j)

private theorem distance_lift (e : Fin m ↪ Fin n) (fixed : Q n) (x y : Q m) :
    hammingDist (lift e fixed x) (lift e fixed y) = hammingDist x y := by
  classical
  let diff₁ := Finset.univ.filter (fun j : Fin m => x j ≠ y j)
  let diff₂ := Finset.univ.filter (fun i : Fin n => lift e fixed x i ≠ lift e fixed y i)
  have h : diff₁.map e = diff₂ := by
    ext i
    by_cases hi : ∃ j, e j = i
    · obtain ⟨j, rfl⟩ := hi
      simp [diff₁, diff₂]
    · simp [diff₁, diff₂, lift_inactive e fixed x hi, lift_inactive e fixed y hi]
      exact fun j _ hj => hi ⟨j, hj⟩
  change diff₂.card = diff₁.card
  rw [← h, Finset.card_map]

private theorem adj_lift_iff (e : Fin m ↪ Fin n) (fixed : Q n) (x y : Q m) :
    (hypercube n).Adj (lift e fixed x) (lift e fixed y) ↔ (hypercube m).Adj x y := by
  change hammingDist (lift e fixed x) (lift e fixed y) = 1 ↔ hammingDist x y = 1
  rw [distance_lift]

private theorem lift_flip (e : Fin m ↪ Fin n) (fixed : Q n) (x : Q m) (j : Fin m) :
    lift e fixed (flip x j) = flip (lift e fixed x) (e j) := by
  funext i
  by_cases hi : ∃ k, e k = i
  · obtain ⟨k, rfl⟩ := hi
    by_cases hkj : k = j
    · subst k
      simp [BalancedCriticalSpectrum.flip]
    · have hne : e k ≠ e j := fun he => hkj (e.injective he)
      simp [BalancedCriticalSpectrum.flip, Function.update_of_ne hkj, Function.update_of_ne hne]
  · have hne : i ≠ e j := fun h => hi ⟨j, h.symm⟩
    simp [lift_inactive e fixed _ hi, BalancedCriticalSpectrum.flip, Function.update_of_ne hne]

open Classical in
/-- The part of a finite support on the chosen face, expressed in its active coordinates. -/
private def restriction (e : Fin m ↪ Fin n) (fixed : Q n) (C : Finset (Q n)) : Finset (Q m) :=
  Finset.univ.filter fun x => lift e fixed x ∈ C

@[simp] private theorem mem_restriction (e : Fin m ↪ Fin n) (fixed : Q n) (C : Finset (Q n)) (x : Q m) :
    x ∈ restriction e fixed C ↔ lift e fixed x ∈ C := by
  classical
  simp [restriction]

/-- Restriction to a coordinate face cannot increase the induced degree. -/
private theorem directions_restriction_card_le (e : Fin m ↪ Fin n) (fixed : Q n)
    (C : Finset (Q n)) (x : Q m) :
    (directions (restriction e fixed C) x).card ≤ (directions C (lift e fixed x)).card := by
  refine Finset.card_le_card_of_injOn e ?_ e.injective.injOn
  intro j hj
  change e j ∈ directions C (lift e fixed x)
  rw [mem_directions, ← lift_flip]
  exact (mem_restriction e fixed C _).mp ((mem_directions _ _ _).mp hj)

end
end D5.S3.Combinatorics.Graph.HypercubeCritical.CubeCoordinateFace


/-!
# The weighted Huang block on a fixed three-axis face

The face uses an embedding of the three active coordinates and an ambient vertex
giving the frozen bits. Both parity blocks inherit the entries of the original
weighted Huang matrix.
-/



namespace Q9ThreeAxisBlock

open scoped BigOperators Matrix
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open D5.S3.Combinatorics.Graph.HypercubeCritical
open D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary
open BalancedCriticalSpectrum (Q flip flip_adj flip_apply_same)
open BalancedCubeComponentBoundary (flip_injective)
open CubeCoordinateFace (lift lift_active lift_injective lift_flip)
open BalancedCubeGirth (adjacent_exists_flip)
open Q9IsotropicHuang (flipSign parity)
open Q9WeightedBoundaryGram (signed signed_transpose)
open private signed_square from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedBoundaryGram
open private flipSign_eq_one_or_neg_one from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9DominantAxisBoundary
open private cubeParity cubeParity_ne_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum

def active (a : Fin 3 ↪ Fin 9) : Finset (Fin 9) :=
  Finset.univ.map a

private theorem mem_active (a : Fin 3 ↪ Fin 9) (j : Fin 9) :
    j ∈ active a ↔ ∃ k : Fin 3, a k = j := by
  simp only [active, Finset.mem_map, Finset.mem_univ, true_and]

private def sparse (a : Fin 3 ↪ Fin 9) (w : Fin 9 → ℝ) (j : Fin 9) : ℝ :=
  if j ∈ active a then w j else 0

private def squareNorm (a : Fin 3 ↪ Fin 9) (w : Fin 9 → ℝ) : ℝ :=
  ∑ k : Fin 3, w (a k) ^ 2

private theorem sum_sparse_sq (a : Fin 3 ↪ Fin 9) (w : Fin 9 → ℝ) :
    ∑ j : Fin 9, sparse a w j ^ 2 = squareNorm a w := by
  symm
  refine Fintype.sum_of_injective a a.injective _ _ ?_ ?_
  · intro j hj
    have hn : j ∉ active a := fun h => hj ((mem_active a j).mp h)
    simp [sparse, hn]
  · intro k
    simp [sparse, (mem_active a (a k)).mpr ⟨k, rfl⟩]

private theorem squareNorm_ne_zero (a : Fin 3 ↪ Fin 9) (w : Fin 9 → ℝ)
    (hw : ∀ k, w (a k) ≠ 0) : squareNorm a w ≠ 0 := by
  change (∑ k : Fin 3, w (a k) ^ 2) ≠ 0
  exact ne_of_gt (Finset.sum_pos (fun k _ => sq_pos_of_ne_zero (hw k))
    Finset.univ_nonempty)

private theorem lift_inactive (a : Fin 3 ↪ Fin 9) (z : Q 9) (x : Q 3) {j : Fin 9}
    (hj : j ∉ active a) : lift a z x j = z j :=
  CubeCoordinateFace.lift_inactive a z x (fun h => hj ((mem_active a j).mpr h))

private theorem lift_eq_of_agree (a : Fin 3 ↪ Fin 9) (z v : Q 9)
    (hv : ∀ j ∉ active a, v j = z j) : lift a z (fun k => v (a k)) = v := by
  funext j
  by_cases hj : j ∈ active a
  · obtain ⟨k, rfl⟩ := (mem_active a j).mp hj
    simp only [lift_active]
  · exact (lift_inactive a z _ hj).trans (hv j hj).symm

/-- The principal submatrix with the frozen coordinates supplied by `z`. -/
private def faceMatrix (a : Fin 3 ↪ Fin 9) (z : Q 9) (w : Fin 9 → ℝ) :
    Matrix (Q 3) (Q 3) ℝ :=
  (signed (sparse a w)).submatrix (lift a z) (lift a z)

/-- A nonzero masked entry must flip an active coordinate. -/
private theorem signed_zero_of_no_active_flip (a : Fin 3 ↪ Fin 9) (w : Fin 9 → ℝ)
    (x y : Q 9) (h : ∀ k : Fin 3, flip x (a k) ≠ y) :
    signed (sparse a w) x y = 0 := by
  unfold signed
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : j ∈ active a
  · obtain ⟨k, rfl⟩ := (mem_active a j).mp hj
    simp only [if_neg (h k)]
  · simp [sparse, hj]

private theorem signed_apply_flip (v : Fin 9 → ℝ) (x : Q 9) (j : Fin 9) :
    signed v x (flip x j) = v j * (flipSign j x : ℝ) := by
  classical
  unfold signed
  rw [Finset.sum_eq_single j]
  · simp only [ite_true]
  · intro k _ hkj
    exact if_neg (fun h => hkj (flip_injective x h))
  · simp

private theorem flipSign_ne_zero (x : Q 9) (j : Fin 9) : (flipSign j x : ℝ) ≠ 0 := by
  rcases flipSign_eq_one_or_neg_one j x with h | h <;> simp [h]

private def parityClass (p : Bool) : Finset (Q 3) :=
  Finset.univ.filter fun x => cubeParity x = p

private theorem parityClass_card (p : Bool) : (parityClass p).card = 4 := by
  cases p <;> decide +kernel

private def parityEquiv (p : Bool) : Fin 4 ≃ ↥(parityClass p) :=
  (Fintype.equivFinOfCardEq ((Fintype.card_coe (parityClass p)).trans
    (parityClass_card p))).symm

/-- A fixed enumeration of the four face vertices of parity `p`. -/
private def word (p : Bool) (c : Fin 4) : Q 3 :=
  (parityEquiv p c).val

private theorem word_parity (p : Bool) (c : Fin 4) : cubeParity (word p c) = p :=
  (Finset.mem_filter.mp (parityEquiv p c).property).2

private theorem word_injective (p : Bool) : Function.Injective (word p) :=
  Subtype.val_injective.comp (parityEquiv p).injective

private theorem exists_word (p : Bool) (x : Q 3) (hx : cubeParity x = p) :
    ∃ c, word p c = x := by
  let u : ↥(parityClass p) := ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
  obtain ⟨c, hc⟩ := (parityEquiv p).surjective u
  exact ⟨c, congrArg Subtype.val hc⟩

private def antipode (x : Q 3) : Q 3 := fun k => !x k

private theorem antipode_parity : ∀ x : Q 3, cubeParity (antipode x) = !cubeParity x := by
  decide +kernel

private def antipodeEquiv (p : Bool) : ↥(parityClass p) ≃ ↥(parityClass (!p)) where
  toFun x := ⟨antipode x.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    (antipode_parity x.val).trans
      (congrArg Bool.not ((Finset.mem_filter.mp x.property).2))⟩⟩
  invFun x := ⟨antipode x.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
    rw [antipode_parity, (Finset.mem_filter.mp x.property).2, Bool.not_not]⟩⟩
  left_inv x := Subtype.ext (funext fun k => Bool.not_not (x.val k))
  right_inv x := Subtype.ext (funext fun k => Bool.not_not (x.val k))

private def antipodeIndex (p : Bool) : Fin 4 ≃ Fin 4 :=
  ((parityEquiv p).trans (antipodeEquiv p)).trans (parityEquiv (!p)).symm

private theorem word_antipodeIndex (p : Bool) (c : Fin 4) :
    word (!p) (antipodeIndex p c) = antipode (word p c) := by
  simp [word, antipodeIndex, antipodeEquiv]

/-- The rows have local parity `!p` and the columns have local parity `p`. -/
private def block (a : Fin 3 ↪ Fin 9) (z : Q 9) (w : Fin 9 → ℝ) (p : Bool) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  (faceMatrix a z w).submatrix (word (!p)) (word p)

private theorem parity_flip (x : Q 3) (k : Fin 3) :
    cubeParity (flip x k) = !cubeParity x :=
  (Bool.not_eq_iff.mpr (cubeParity_ne_of_adj (flip_adj x k))).symm

private theorem block_transpose (a : Fin 3 ↪ Fin 9) (z : Q 9) (w : Fin 9 → ℝ) (p : Bool) :
    (block a z w p)ᵀ = block a z w (!p) := by
  ext c r
  change signed (sparse a w) (lift a z (word (!p) r)) (lift a z (word p c)) =
    signed (sparse a w) (lift a z (word (!(!p)) c)) (lift a z (word (!p) r))
  rw [Bool.not_not]
  have h := congrFun (congrFun (signed_transpose (sparse a w))
    (lift a z (word p c))) (lift a z (word (!p) r))
  exact h

/-- Terms outside the column image vanish in the ambient row Gram. -/
private theorem block_mul_transpose (a : Fin 3 ↪ Fin 9) (z : Q 9) (w : Fin 9 → ℝ) (p : Bool) :
    block a z w p * (block a z w p)ᵀ = squareNorm a w • 1 := by
  classical
  let row (r : Fin 4) := lift a z (word (!p) r)
  let col (c : Fin 4) := lift a z (word p c)
  let M := signed (sparse a w)
  have hrow : Function.Injective row := (lift_injective a z).comp (word_injective (!p))
  have hcol : Function.Injective col := (lift_injective a z).comp (word_injective p)
  have hzero (r : Fin 4) (y : Q 9) (hy : y ∉ Set.range col) : M (row r) y = 0 := by
    apply signed_zero_of_no_active_flip
    intro k hk
    have hp : cubeParity (flip (word (!p) r) k) = p := by
      rw [parity_flip, word_parity, Bool.not_not]
    obtain ⟨c, hc⟩ := exists_word p _ hp
    exact hy ⟨c, (congrArg (lift a z) hc).trans ((lift_flip a z _ k).trans hk)⟩
  ext r s
  calc
    (block a z w p * (block a z w p)ᵀ) r s = (M * Mᵀ) (row r) (row s) := by
      change (∑ c : Fin 4, M (row r) (col c) * M (row s) (col c)) =
        ∑ y : Q 9, M (row r) y * M (row s) y
      refine Fintype.sum_of_injective col hcol _ _ ?_ (fun _ => rfl)
      intro y hy
      rw [hzero r y hy, zero_mul]
    _ = (squareNorm a w • (1 : Matrix (Fin 4) (Fin 4) ℝ)) r s := by
      change (signed (sparse a w) * (signed (sparse a w))ᵀ) (row r) (row s) = _
      rw [signed_transpose, signed_square, sum_sparse_sq]
      simp only [Matrix.smul_apply, Matrix.one_apply, hrow.eq_iff]

private theorem block_transpose_mul (a : Fin 3 ↪ Fin 9) (z : Q 9) (w : Fin 9 → ℝ) (p : Bool) :
    (block a z w p)ᵀ * block a z w p = squareNorm a w • 1 := by
  simpa only [block_transpose, Bool.not_not] using block_mul_transpose a z w (!p)

private theorem opposite_adj_iff (x y : Q 3) (h : cubeParity y ≠ cubeParity x) :
    (hypercube 3).Adj x y ↔ y ≠ antipode x := by
  have table : ∀ x y : Q 3, cubeParity y ≠ cubeParity x →
      (hammingDist x y = 1 ↔ y ≠ antipode x) := by
    decide +kernel
  exact table x y h

/-- With all three weights nonzero, each column has its sole zero at its antipode. -/
private theorem block_eq_zero_iff (a : Fin 3 ↪ Fin 9) (z : Q 9) (w : Fin 9 → ℝ)
    (p : Bool) (hw : ∀ k, w (a k) ≠ 0) (r c : Fin 4) :
    block a z w p r c = 0 ↔ r = antipodeIndex p c := by
  let x := word p c
  let y := word (!p) r
  have hp : cubeParity y ≠ cubeParity x := by
    change cubeParity (word (!p) r) ≠ cubeParity (word p c)
    rw [word_parity, word_parity]
    cases p <;> decide
  have hmatch : y = antipode x ↔ r = antipodeIndex p c := by
    rw [← word_antipodeIndex p c]
    exact (word_injective (!p)).eq_iff
  have hsym : block a z w p r c = signed (sparse a w) (lift a z x) (lift a z y) :=
    congrFun (congrFun (signed_transpose (sparse a w)) (lift a z x)) (lift a z y)
  rw [hsym, ← hmatch]
  constructor
  · intro hz
    by_contra hn
    obtain ⟨k, hk⟩ := adjacent_exists_flip ((opposite_adj_iff x y hp).mpr hn)
    rw [hk, lift_flip, signed_apply_flip, sparse, if_pos
      ((mem_active a (a k)).mpr ⟨k, rfl⟩)] at hz
    exact (mul_ne_zero (hw k) (flipSign_ne_zero _ _)) hz
  · intro ha
    apply signed_zero_of_no_active_flip
    intro k hk
    have hxy := (lift_injective a z) ((lift_flip a z x k).trans hk)
    have hadj : (hypercube 3).Adj x y := by
      rw [← hxy]
      exact flip_adj x k
    exact ((opposite_adj_iff x y hp).mp hadj) ha

end Q9ThreeAxisBlock

/-!
# Rank classification on an actual masked empty-fibre boundary

The full mask kernel can be restricted at any nonzero paired coefficient.
The column image consists of the actual paired vertices on that face, and
the tested rows come from the actual empty-fibre carrier.
-/



namespace Q9ThreeAxisBoundaryTransport

open scoped BigOperators Matrix
open D5.S3.Combinatorics.Graph.HypercubeCritical
open D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary
open CoordinateHalves.Q9DominantAxisBoundary (PairedRows EmptyExterior emptyFibreBoundary)
open BalancedCriticalSpectrum (Q)
local notation "cubeFlip" => BalancedCriticalSpectrum.flip
open Q9IsotropicHuang (parity)
open Q9WeightedBoundaryGram (signed)
open Q9ThreeAxisBlock
open CubeCoordinateFace (lift lift_active lift_injective lift_flip)
open private cubeParity from D5.S3.Combinatorics.Graph.HypercubeSubQuorum

private def frozenParity (a : Fin 3 ↪ Fin 9) (z : Q 9) : Bool :=
  ∑ j ∈ Finset.univ \ active a, z j

/-- In a fixed face, the ambient and local parities differ by the frozen bits. -/
def columnParity (a : Fin 3 ↪ Fin 9) (z : Q 9) (b : Bool) : Bool :=
  b + frozenParity a z

private theorem lift_parity (a : Fin 3 ↪ Fin 9) (z : Q 9) (x : Q 3) :
    parity (lift a z x) = frozenParity a z + cubeParity x := by
  have hactive : (∑ j ∈ active a, lift a z x j) = cubeParity x := by
    rw [active, Finset.sum_map]
    simp only [lift_active, cubeParity]
  have hfrozen : (∑ j ∈ Finset.univ \ active a, lift a z x j) = frozenParity a z := by
    apply Finset.sum_congr rfl
    intro j hj
    exact lift_inactive a z x (Finset.mem_sdiff.mp hj).2
  change (∑ j : Fin 9, lift a z x j) = _
  rw [← Finset.sum_sdiff (f := lift a z x) (Finset.subset_univ (active a)), hfrozen, hactive]

private theorem xor_eq_iff (f x b : Bool) : f + x = b ↔ x = b + f := by
  cases f <;> cases x <;> cases b <;> decide

private theorem lift_parity_eq_iff (a : Fin 3 ↪ Fin 9) (z : Q 9) (b : Bool) (x : Q 3) :
    parity (lift a z x) = b ↔ cubeParity x = columnParity a z b := by
  rw [lift_parity, columnParity, xor_eq_iff]

private def columnVertex (a : Fin 3 ↪ Fin 9) (z : Q 9) (b : Bool) (c : Fin 4) : Q 9 :=
  lift a z (word (columnParity a z b) c)

private def rowVertex (a : Fin 3 ↪ Fin 9) (z : Q 9) (b : Bool) (r : Fin 4) : Q 9 :=
  lift a z (word (!columnParity a z b) r)

private theorem columnVertex_parity (a : Fin 3 ↪ Fin 9) (z : Q 9) (b : Bool) (c : Fin 4) :
    parity (columnVertex a z b c) = b :=
  (lift_parity_eq_iff a z b _).mpr (word_parity _ _)

private theorem rowVertex_parity_ne (a : Fin 3 ↪ Fin 9) (z : Q 9) (b : Bool) (r : Fin 4) :
    parity (rowVertex a z b r) ≠ b := by
  intro h
  have hp := (lift_parity_eq_iff a z b (word (!columnParity a z b) r)).mp h
  rw [word_parity] at hp
  cases columnParity a z b <;> simp at hp

private def pairedColumns (C : Finset (Q 9)) (b : Bool) (i : Fin 9)
    (a : Fin 3 ↪ Fin 9) (z : Q 9) : Finset (Fin 4) :=
  Finset.univ.filter fun c =>
    columnVertex a z b c ∈ C ∧ cubeFlip (columnVertex a z b c) i ∈ C

private def emptyRows (C : Finset (Q 9)) (b : Bool) (i : Fin 9)
    (a : Fin 3 ↪ Fin 9) (z : Q 9) : Finset (Fin 4) :=
  Finset.univ.filter fun r =>
    rowVertex a z b r ∉ C ∧ cubeFlip (rowVertex a z b r) i ∉ C

private def pairedColumn (C : Finset (Q 9)) (b : Bool) (i : Fin 9)
    (a : Fin 3 ↪ Fin 9) (z : Q 9) (c : ↥(pairedColumns C b i a z)) : PairedRows C b i := by
  have hc := (Finset.mem_filter.mp c.property).2
  exact ⟨⟨⟨columnVertex a z b c.val, hc.1⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, columnVertex_parity a z b c.val⟩⟩, hc.2⟩

private def emptyRow (C : Finset (Q 9)) (b : Bool) (i : Fin 9)
    (a : Fin 3 ↪ Fin 9) (z : Q 9) (r : ↥(emptyRows C b i a z)) : EmptyExterior C b i := by
  have hr := (Finset.mem_filter.mp r.property).2
  exact ⟨⟨⟨rowVertex a z b r.val, rowVertex_parity_ne a z b r.val⟩, hr.1⟩, hr.2⟩

private theorem pairedColumn_injective (C : Finset (Q 9)) (b : Bool) (i : Fin 9)
    (a : Fin 3 ↪ Fin 9) (z : Q 9) : Function.Injective (pairedColumn C b i a z) := by
  intro c d h
  apply Subtype.ext
  apply word_injective (columnParity a z b)
  apply lift_injective a z
  exact congrArg (fun x : PairedRows C b i => x.1.1.1) h

private theorem pairedColumn_range (C : Finset (Q 9)) (b : Bool) (i : Fin 9)
    (a : Fin 3 ↪ Fin 9) (z : Q 9) (x : PairedRows C b i)
    (hx : ∀ j ∉ active a, x.1.1.1 j = z j) :
    x ∈ Set.range (pairedColumn C b i a z) := by
  have hlift := lift_eq_of_agree a z x.1.1.1 hx
  have hb : parity x.1.1.1 = b := (Finset.mem_filter.mp x.1.property).2
  have hlocal : cubeParity (fun k => x.1.1.1 (a k)) = columnParity a z b :=
    (lift_parity_eq_iff a z b _).mp ((congrArg parity hlift).trans hb)
  obtain ⟨c, hc⟩ := exists_word _ _ hlocal
  have he : columnVertex a z b c = x.1.1.1 :=
    (congrArg (lift a z) hc).trans hlift
  have hcP : c ∈ pairedColumns C b i a z := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [he]
    exact ⟨x.1.1.property, x.property⟩
  exact ⟨⟨c, hcP⟩, Subtype.ext (Subtype.ext (Subtype.ext he))⟩

private theorem boundary_entry (C : Finset (Q 9)) (b : Bool) (i : Fin 9)
    (a : Fin 3 ↪ Fin 9) (hi : i ∉ active a) (w : Fin 9 → ℝ)
    (y : EmptyExterior C b i) (x : PairedRows C b i) :
    emptyFibreBoundary C b i (sparse a w) y x = signed (sparse a w) y.1.1.1 x.1.1.1 := by
  change signed (fun j => if j = i then 0 else sparse a w j) y.1.1.1 x.1.1.1 = _
  have hw : (fun j => if j = i then 0 else sparse a w j) = sparse a w := by
    funext j
    by_cases hj : j = i
    · subst j
      simp [sparse, hi]
    · simp [hj]
  rw [hw]

/-- The restricted ambient matrix is the paired-column and empty-row submatrix
of the fixed-face Huang block, entry for entry. -/
private theorem boundary_submatrix (C : Finset (Q 9)) (b : Bool) (i : Fin 9)
    (a : Fin 3 ↪ Fin 9) (hi : i ∉ active a) (z : Q 9) (w : Fin 9 → ℝ) :
    (emptyFibreBoundary C b i (sparse a w)).submatrix
      (emptyRow C b i a z) (pairedColumn C b i a z) =
    (block a z w (columnParity a z b)).submatrix
      (Subtype.val : ↥(emptyRows C b i a z) → Fin 4)
      (Subtype.val : ↥(pairedColumns C b i a z) → Fin 4) := by
  ext r c
  exact boundary_entry C b i a hi w (emptyRow C b i a z r) (pairedColumn C b i a z c)

private theorem restrict_kernel (C : Finset (Q 9)) (b : Bool) (i : Fin 9)
    (a : Fin 3 ↪ Fin 9) (hi : i ∉ active a) (z : Q 9) (w : Fin 9 → ℝ)
    (f : PairedRows C b i → ℝ) (hker : emptyFibreBoundary C b i (sparse a w) *ᵥ f = 0) :
    ((block a z w (columnParity a z b)).submatrix
      (Subtype.val : ↥(emptyRows C b i a z) → Fin 4)
      (Subtype.val : ↥(pairedColumns C b i a z) → Fin 4)) *ᵥ
      (fun c => f (pairedColumn C b i a z c)) = 0 := by
  classical
  rw [← boundary_submatrix C b i a hi z w]
  funext r
  let y := emptyRow C b i a z r
  let B := emptyFibreBoundary C b i (sparse a w)
  calc
    _ = (B *ᵥ f) y := by
      change (∑ c : ↥(pairedColumns C b i a z),
        B y (pairedColumn C b i a z c) * f (pairedColumn C b i a z c)) =
        ∑ x : PairedRows C b i, B y x * f x
      refine Fintype.sum_of_injective _ (pairedColumn_injective C b i a z) _ _ ?_ (fun _ => rfl)
      intro x hx
      have hzero : B y x = 0 := by
        rw [show B y x = signed (sparse a w) y.1.1.1 x.1.1.1 from boundary_entry C b i a hi w y x]
        apply signed_zero_of_no_active_flip
        intro k hk
        apply hx
        apply pairedColumn_range C b i a z x
        intro j hj
        have hne : j ≠ a k := fun he => hj ((mem_active a j).mpr ⟨k, he.symm⟩)
        rw [← hk]
        change cubeFlip (rowVertex a z b r.val) (a k) j = z j
        simpa only [BalancedCriticalSpectrum.flip, Function.update_of_ne hne, rowVertex] using
          lift_inactive a z (word (!columnParity a z b) r.val) hj
      rw [hzero, zero_mul]
    _ = 0 := congrFun hker y

/-- The rank alternatives on the face through any nonzero masked kernel coefficient. -/
private theorem defect_on_face_of_kernel (C : Finset (Q 9)) (b : Bool) (i : Fin 9)
    (a : Fin 3 ↪ Fin 9) (hi : i ∉ active a) (w : Fin 9 → ℝ) (hw : ∀ k, w (a k) ≠ 0)
    (f : PairedRows C b i → ℝ) (hker : emptyFibreBoundary C b i (sparse a w) *ᵥ f = 0)
    (x₀ : PairedRows C b i) (hx₀ : f x₀ ≠ 0) :
    let z := x₀.1.1.1
    let P := pairedColumns C b i a z
    let T := emptyRows C b i a z
    let σ := antipodeIndex (columnParity a z b)
    T.card < P.card ∨
      (∃ c, P = {c} ∧ T = {σ c}) ∨
      (∃ c, P = {c}ᶜ ∧ T = {σ c}ᶜ) := by
  dsimp only
  let z := x₀.1.1.1
  let p := columnParity a z b
  have hne : (fun c => f (pairedColumn C b i a z c)) ≠ 0 := by
    obtain ⟨c, hc⟩ := pairedColumn_range C b i a z x₀ (fun _ _ => rfl)
    intro h
    exact hx₀ (by simpa only [hc, Pi.zero_apply] using congrFun h c)
  exact (Q9ThreeAxisRank.submatrix_has_nonzero_kernel_iff
    (block a z w p) (antipodeIndex p) (squareNorm_ne_zero a w hw)
    (block_mul_transpose a z w p) (block_eq_zero_iff a z w p hw)
    (pairedColumns C b i a z) (emptyRows C b i a z)).mp
      ⟨_, hne, restrict_kernel C b i a hi z w f hker⟩

end Q9ThreeAxisBoundaryTransport

/-!
# The four-face capacity witness from a masked boundary kernel

Coordinate zero of the four-cube is the dominant axis. Projecting it away
leaves the same three local coordinates used in the signed block.
-/



namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9ThreeAxisCapacityTransport

open scoped BigOperators Matrix
open D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9DominantAxisBoundary (PairedRows emptyFibreBoundary
  exists_two_components_with_fixed_projectedParity_emptyFibre_kernels)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.TwoBalancedComponents (componentFinset componentFinset_subset)
open private componentFinset_neighbor_closed componentFinset_disjoint from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwoBalancedComponents
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary (directions directions_card)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.SupportedEigenSaturation (selected_neighbor_card)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum (Q)
local notation "cubeFlip" => BalancedCriticalSpectrum.flip
open Q9ThreeAxisBlock
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.CubeCoordinateFace (lift lift_active lift_injective lift_flip)
open Q9ThreeAxisBoundaryTransport
open private cubeParity from D5.S3.Combinatorics.Graph.HypercubeSubQuorum

/-- The ambient four-face obtained by unfreezing the dominant axis. -/
private def liftFour (a : Fin 3 ↪ Fin 9) (z : Q 9) (i : Fin 9) (y : Q 4) : Q 9 :=
  Function.update (lift a z (Q4FaceCapacity.project 0 y)) i (y 0)

/-- The chosen support in the four-face, expressed in the four local coordinates. -/
def faceSupport (C : Finset (Q 9)) (a : Fin 3 ↪ Fin 9) (z : Q 9) (i : Fin 9) :
    Finset (Q 4) :=
  Finset.univ.filter fun y => liftFour a z i y ∈ C

private theorem endpoints (a : Fin 3 ↪ Fin 9) (z : Q 9) (i : Fin 9)
    (hi : i ∉ active a) (x : Q 3) :
    liftFour a z i (Q4FaceCapacity.lift 0 (z i) x) = lift a z x ∧
    liftFour a z i (Q4FaceCapacity.lift 0 (!(z i)) x) = cubeFlip (lift a z x) i := by
  have hzi : lift a z x i = z i := lift_inactive a z x hi
  constructor
  · simp only [liftFour, Fin.removeNth_insertNth, Fin.insertNth_apply_same]
    rw [← hzi, Function.update_eq_self]
  · simp only [liftFour, Fin.removeNth_insertNth, Fin.insertNth_apply_same, BalancedCriticalSpectrum.flip, hzi]

private theorem paired_membership (C : Finset (Q 9)) (b : Bool) (i : Fin 9)
    (a : Fin 3 ↪ Fin 9) (hi : i ∉ active a) (z : Q 9) (c : Fin 4) :
    word (columnParity a z b) c ∈
        Q4FaceCapacity.doubleColumns (faceSupport C a z i) 0 (columnParity a z b) ↔
      c ∈ pairedColumns C b i a z := by
  let x := word (columnParity a z b) c
  have h := endpoints a z i hi x
  change x ∈ Q4FaceCapacity.doubleColumns _ _ _ ↔ _
  simp only [Q4FaceCapacity.doubleColumns, Q4FaceCapacity.parityClass, faceSupport,
    Finset.mem_filter, Finset.mem_univ, true_and]
  unfold pairedColumns
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  change (cubeParity x = columnParity a z b ∧
    liftFour a z i (Q4FaceCapacity.lift 0 false x) ∈ C ∧
    liftFour a z i (Q4FaceCapacity.lift 0 true x) ∈ C) ↔
    lift a z x ∈ C ∧ cubeFlip (lift a z x) i ∈ C
  have hx : cubeParity x = columnParity a z b := word_parity _ _
  cases hb : z i <;> rw [hb] at h
  · have hfirst := h.1
    have hsecond : liftFour a z i (Q4FaceCapacity.lift 0 true x) = cubeFlip (lift a z x) i := h.2
    rw [hx, hfirst, hsecond]
    simp only [eq_self, true_and]
  · have hfirst := h.1
    have hsecond : liftFour a z i (Q4FaceCapacity.lift 0 false x) = cubeFlip (lift a z x) i := h.2
    rw [hx, hfirst, hsecond]
    simp only [eq_self, true_and, and_comm]

private theorem empty_membership (C : Finset (Q 9)) (b : Bool) (i : Fin 9)
    (a : Fin 3 ↪ Fin 9) (hi : i ∉ active a) (z : Q 9) (r : Fin 4) :
    word (!columnParity a z b) r ∈
        Q4FaceCapacity.emptyRows (faceSupport C a z i) 0 (columnParity a z b) ↔
      r ∈ Q9ThreeAxisBoundaryTransport.emptyRows C b i a z := by
  let x := word (!columnParity a z b) r
  have h := endpoints a z i hi x
  change x ∈ Q4FaceCapacity.emptyRows _ _ _ ↔ _
  simp only [Q4FaceCapacity.emptyRows, Q4FaceCapacity.parityClass, faceSupport,
    Finset.mem_filter, Finset.mem_univ, true_and]
  unfold Q9ThreeAxisBoundaryTransport.emptyRows
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  change (cubeParity x = !columnParity a z b ∧
    liftFour a z i (Q4FaceCapacity.lift 0 false x) ∉ C ∧
    liftFour a z i (Q4FaceCapacity.lift 0 true x) ∉ C) ↔
    lift a z x ∉ C ∧ cubeFlip (lift a z x) i ∉ C
  have hx : cubeParity x = !columnParity a z b := word_parity _ _
  cases hb : z i <;> rw [hb] at h
  · have hfirst := h.1
    have hsecond : liftFour a z i (Q4FaceCapacity.lift 0 true x) = cubeFlip (lift a z x) i := h.2
    rw [hx, hfirst, hsecond]
    simp only [eq_self, true_and]
  · have hfirst := h.1
    have hsecond : liftFour a z i (Q4FaceCapacity.lift 0 false x) = cubeFlip (lift a z x) i := h.2
    rw [hx, hfirst, hsecond]
    simp only [eq_self, true_and, and_comm]

private theorem map_eq_of_occupancy (p : Bool) (S : Finset (Fin 4)) (A : Finset (Q 3))
    (hA : ∀ x ∈ A, cubeParity x = p) (hmem : ∀ c, word p c ∈ A ↔ c ∈ S) :
    S.map (⟨word p, word_injective p⟩ : Fin 4 ↪ Q 3) = A := by
  ext x
  rw [Finset.mem_map]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact (hmem c).mpr hc
  · intro hx
    obtain ⟨c, rfl⟩ := exists_word p x (hA x hx)
    exact ⟨c, (hmem c).mp hx, rfl⟩

/-- The face through a nonzero kernel coefficient meets the hypothesis of
`Q4FaceCapacity.exterior_card_le_capacity` on the dominant axis. -/
private theorem deficiencyWitness_of_kernel (C : Finset (Q 9)) (b : Bool) (i : Fin 9)
    (a : Fin 3 ↪ Fin 9) (hi : i ∉ active a) (w : Fin 9 → ℝ) (hw : ∀ k, w (a k) ≠ 0)
    (f : PairedRows C b i → ℝ) (hker : emptyFibreBoundary C b i (sparse a w) *ᵥ f = 0)
    (x₀ : PairedRows C b i) (hx₀ : f x₀ ≠ 0) :
    Q4FaceCapacity.DeficiencyWitness (faceSupport C a x₀.1.1.1 i) 0
      (columnParity a x₀.1.1.1 b) := by
  classical
  let z := x₀.1.1.1
  let p := columnParity a z b
  let P := pairedColumns C b i a z
  let T := Q9ThreeAxisBoundaryTransport.emptyRows C b i a z
  let A := faceSupport C a z i
  let P₄ := Q4FaceCapacity.doubleColumns A 0 p
  let T₄ := Q4FaceCapacity.emptyRows A 0 p
  have hmP (c : Fin 4) : word p c ∈ P₄ ↔ c ∈ P := paired_membership C b i a hi z c
  have hmT (r : Fin 4) : word (!p) r ∈ T₄ ↔ r ∈ T := empty_membership C b i a hi z r
  have hP : P₄.card = P.card := by
    have h := map_eq_of_occupancy p P P₄ (by
      intro x hx
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2) hmP
    rw [← h, Finset.card_map]
  have hT : T₄.card = T.card := by
    have h := map_eq_of_occupancy (!p) T T₄ (by
      intro x hx
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2) hmT
    rw [← h, Finset.card_map]
  have hanti (c : Fin 4) : word (!p) (antipodeIndex p c) = Q4FaceCapacity.antipode (word p c) :=
    word_antipodeIndex p c
  unfold Q4FaceCapacity.DeficiencyWitness
  change T₄.card < P₄.card ∨
    (P₄.card = 1 ∧ T₄.card = 1 ∧ ∃ x ∈ P₄, Q4FaceCapacity.antipode x ∈ T₄) ∨
    (P₄.card = 3 ∧ T₄.card = 3 ∧ ∃ x ∈ Q4FaceCapacity.parityClass p \ P₄,
      Q4FaceCapacity.antipode x ∈ Q4FaceCapacity.parityClass (!p) \ T₄)
  rw [hP, hT]
  have hdef := defect_on_face_of_kernel C b i a hi w hw f hker x₀ hx₀
  change T.card < P.card ∨
    (∃ c, P = {c} ∧ T = {antipodeIndex p c}) ∨
    (∃ c, P = {c}ᶜ ∧ T = {antipodeIndex p c}ᶜ) at hdef
  rcases hdef with hsurplus | ⟨c, hc, hr⟩ | ⟨c, hc, hr⟩
  · exact Or.inl hsurplus
  · refine Or.inr (Or.inl ⟨by rw [hc, Finset.card_singleton], by rw [hr, Finset.card_singleton],
      word p c, (hmP c).mpr (by rw [hc]; simp), ?_⟩)
    rw [← hanti c]
    exact (hmT _).mpr (by rw [hr]; simp)
  · have hcard (d : Fin 4) : ({d}ᶜ : Finset (Fin 4)).card = 3 := by
      simp [Finset.card_compl]
    refine Or.inr (Or.inr ⟨by rw [hc]; exact hcard _, by rw [hr]; exact hcard _,
      word p c, ?_, ?_⟩)
    · exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, word_parity _ _⟩,
        fun hx => by simpa [hc] using (hmP c).mp hx⟩
    · rw [← hanti c]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, word_parity _ _⟩,
        fun hx => by simpa [hr] using (hmT (antipodeIndex p c)).mp hx⟩

/-- Enumerate the four active axes, using local coordinate zero for the dominant axis. -/
private def fourEmbedding (a : Fin 3 ↪ Fin 9) (i : Fin 9) (hi : i ∉ active a) : Fin 4 ↪ Fin 9 :=
  ⟨Fin.cons i a, by
    intro u v
    refine Fin.cases ?_ (fun k => ?_) u
    · refine Fin.cases ?_ (fun l h => ?_) v
      · exact fun _ => rfl
      · exact (hi ((mem_active a i).mpr ⟨l, h.symm⟩)).elim
    · refine Fin.cases ?_ (fun l h => ?_) v
      · intro h
        exact (hi ((mem_active a i).mpr ⟨k, h⟩)).elim
      · exact congrArg Fin.succ (a.injective h)⟩

private theorem liftFour_eq (a : Fin 3 ↪ Fin 9) (z : Q 9) (i : Fin 9)
    (hi : i ∉ active a) (y : Q 4) :
    liftFour a z i y = lift (fourEmbedding a i hi) z y := by
  funext j
  by_cases hj : j = i
  · subst j
    have he : fourEmbedding a i hi 0 = i := rfl
    have hright : lift (fourEmbedding a i hi) z y i = y 0 := by
      simpa only [he] using lift_active (fourEmbedding a i hi) z y 0
    rw [hright]
    simp [liftFour]
  · by_cases hja : j ∈ active a
    · obtain ⟨k, rfl⟩ := (mem_active a j).mp hja
      have he : fourEmbedding a i hi k.succ = a k := rfl
      rw [← he, lift_active, he]
      simp [liftFour, Function.update_of_ne hj, Q4FaceCapacity.project, Fin.tail]
    · have hout : ¬ ∃ k, fourEmbedding a i hi k = j := by
        rintro ⟨k, hk⟩
        revert hk
        refine Fin.cases ?_ (fun l => ?_) k
        · exact fun hk => hj hk.symm
        · exact fun hk => hja ((mem_active a j).mpr ⟨l, hk⟩)
      rw [CubeCoordinateFace.lift_inactive _ _ _ hout]
      simp [liftFour, Function.update_of_ne hj, lift_inactive _ _ _ hja]

private theorem faceSupport_eq_restriction (C : Finset (Q 9)) (a : Fin 3 ↪ Fin 9)
    (z : Q 9) (i : Fin 9) (hi : i ∉ active a) :
    faceSupport C a z i = CubeCoordinateFace.restriction (fourEmbedding a i hi) z C := by
  ext y
  simp [faceSupport, liftFour_eq a z i hi]

open Classical in
/-- A component with a masked boundary defect has a four-face containing at most
three vertices from all the other selected components together. -/
private theorem other_selected_card_le_three (U C : Finset (Q 9))
    (hC : C ⊆ U) (hdegree : ∀ x : (U : Set (Q 9)),
      ((hypercube 9).induce (U : Set (Q 9))).degree x ≤ 3)
    (hclosed : ∀ x ∈ C, ∀ y ∈ U, (hypercube 9).Adj x y → y ∈ C)
    (a : Fin 3 ↪ Fin 9) (z : Q 9) (i : Fin 9) (hi : i ∉ active a) (b : Bool)
    (h : Q4FaceCapacity.DeficiencyWitness (faceSupport C a z i) 0 b) :
    (faceSupport (U \ C) a z i).card ≤ 3 := by
  classical
  let e := fourEmbedding a i hi
  let A := CubeCoordinateFace.restriction e z C
  let B := CubeCoordinateFace.restriction e z (U \ C)
  have hA : Q4FaceCapacity.DeficiencyWitness A 0 b := by
    simpa only [faceSupport_eq_restriction C a z i hi] using h
  have hdeg (x : Q 4) (hx : x ∈ A) : (directions A x).card ≤ 3 := by
    have hxC := (CubeCoordinateFace.mem_restriction e z C x).mp hx
    refine (CubeCoordinateFace.directions_restriction_card_le e z C x).trans ?_
    rw [directions_card]
    have hsub : C.filter (fun y => (hypercube 9).Adj (lift e z x) y) ⊆
        U.filter (fun y => (hypercube 9).Adj (lift e z x) y) := by
      intro y hy
      exact Finset.mem_filter.mpr ⟨hC (Finset.mem_filter.mp hy).1, (Finset.mem_filter.mp hy).2⟩
    refine (Finset.card_le_card hsub).trans ?_
    have hFilter : U.filter (fun y => (hypercube 9).Adj (lift e z x) y) =
        (hypercube 9).neighborFinset (lift e z x) ∩ U := by
      ext y
      simp [SimpleGraph.mem_neighborFinset, and_comm]
    rw [hFilter, selected_neighbor_card (hC hxC)]
    exact hdegree ⟨_, hC hxC⟩
  have hB : B ⊆ Q4FaceCapacity.exterior A := by
    intro y hy
    have hMem := Finset.mem_sdiff.mp ((CubeCoordinateFace.mem_restriction e z (U \ C) y).mp hy)
    apply Q4FaceCapacity.mem_exterior.mpr
    refine ⟨fun hyC => hMem.2 ((CubeCoordinateFace.mem_restriction e z C y).mp hyC), ?_⟩
    intro x hx hAdj
    exact hMem.2 (hclosed _ ((CubeCoordinateFace.mem_restriction e z C x).mp hx)
      _ hMem.1 ((CubeCoordinateFace.adj_lift_iff e z y x).2 hAdj).symm)
  rw [faceSupport_eq_restriction (U \ C) a z i hi]
  exact (Finset.card_le_card hB).trans (Q4FaceCapacity.exterior_card_le_three A 0 _ hdeg hA)

open Classical in
/-- Every four-axis mask forces a witness face for each of two actual components
of a 258-point subcubic support. In its witness face each component leaves
space for at most three points of the rest of the entire support. For each
dominant axis the two projected parities are chosen before the transverse
mask, and the witnesses are anchored at actual paired vertices. -/
theorem two_components_four_face_capacity (U : Finset (Q 9)) (hU : U.card = 258)
    (hdeg : ∀ x : (U : Set (Q 9)),
      ((hypercube 9).induce (U : Set (Q 9))).degree x ≤ 3) :
    ∃ C D : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent,
      C ≠ D ∧ ∀ i : Fin 9, ∃ pC pD : Bool, ∀ a : Fin 3 ↪ Fin 9, i ∉ active a →
        ∃ (xC : PairedRows (componentFinset U C) false i)
          (xD : PairedRows (componentFinset U D) false i),
          let zC := xC.1.1.1
          let zD := xD.1.1.1
          (∃ j, j ≠ i ∧ j ∉ active a ∧ zC j ≠ zD j) ∧
          (∑ j : Fin 8, zC (i.succAbove j)) = pC ∧
          (∑ j : Fin 8, zD (i.succAbove j)) = pD ∧
          Q4FaceCapacity.DeficiencyWitness (faceSupport (componentFinset U C) a zC i)
            0 (columnParity a zC false) ∧
          Q4FaceCapacity.DeficiencyWitness (faceSupport (componentFinset U D) a zD i)
            0 (columnParity a zD false) ∧
          (faceSupport (U \ componentFinset U C) a zC i).card ≤ 3 ∧
          (faceSupport (U \ componentFinset U D) a zD i).card ≤ 3 := by
  obtain ⟨C, D, hCD, hCDker⟩ :=
    exists_two_components_with_fixed_projectedParity_emptyFibre_kernels U hU hdeg false
  refine ⟨C, D, hCD, fun i => ?_⟩
  obtain ⟨pC, pD, hker⟩ := hCDker i
  refine ⟨pC, pD, fun a hi => ?_⟩
  let w : Fin 9 → ℝ := fun _ => 1
  have one (K : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent) (p : Bool)
      (hk : ∃ f : PairedRows (componentFinset U K) false i → ℝ,
        f ≠ 0 ∧ emptyFibreBoundary (componentFinset U K) false i (sparse a w) *ᵥ f = 0 ∧
          ∀ x, (∑ j : Fin 8, x.1.1.1 (i.succAbove j)) ≠ p → f x = 0) :
      ∃ x : PairedRows (componentFinset U K) false i,
        let z := x.1.1.1
        (∑ j : Fin 8, z (i.succAbove j)) = p ∧
        Q4FaceCapacity.DeficiencyWitness (faceSupport (componentFinset U K) a z i)
          0 (columnParity a z false) ∧
        (faceSupport (U \ componentFinset U K) a z i).card ≤ 3 := by
    obtain ⟨f, hf, hfker, hparity⟩ := hk
    have hpoint : ∃ x₀, f x₀ ≠ 0 := by
      by_contra! h
      exact hf (funext h)
    obtain ⟨x₀, hx₀⟩ := hpoint
    have hw : ∀ k, w (a k) ≠ 0 := fun _ => one_ne_zero
    have hdef := deficiencyWitness_of_kernel _ false i a hi w hw f hfker x₀ hx₀
    exact ⟨x₀, not_ne_iff.mp (fun h => hx₀ (hparity x₀ h)), hdef,
      other_selected_card_le_three U _ (componentFinset_subset U K) hdeg
        (componentFinset_neighbor_closed U K) a _ i hi _ hdef⟩
  obtain ⟨xC, hpC, hzC, hC⟩ := one C pC (hker (active a) w).1
  obtain ⟨xD, hpD, hzD, hD⟩ := one D pD (hker (active a) w).2
  let zC := xC.1.1.1
  let zD := xD.1.1.1
  refine ⟨xC, xD, ?_, hpC, hpD, hzC, hzD, hC, hD⟩
  change ∃ j, j ≠ i ∧ j ∉ active a ∧ zC j ≠ zD j
  by_contra! hagree
  have hLift (x : Q 4) : liftFour a zC i x = liftFour a zD i x := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [liftFour]
    rw [liftFour, liftFour, Function.update_of_ne hji, Function.update_of_ne hji]
    by_cases hj : j ∈ active a
    · obtain ⟨k, rfl⟩ := (mem_active a j).mp hj
      rw [lift_active, lift_active]
    · rw [lift_inactive a zC _ hj, lift_inactive a zD _ hj]
      exact hagree j hji hj
  have hsub : faceSupport (componentFinset U D) a zD i ⊆
      faceSupport (U \ componentFinset U C) a zC i := by
    intro x hx
    have hm : liftFour a zD i x ∈ componentFinset U D := (Finset.mem_filter.mp hx).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hLift x]
    exact Finset.mem_sdiff.mpr ⟨componentFinset_subset U D hm, fun hc =>
      Finset.disjoint_left.mp (componentFinset_disjoint U C D hCD) hc hm⟩
  have hsize := (Finset.card_le_card hsub).trans hC
  exact (by omega : ¬ 5 ≤ (faceSupport (componentFinset U D) a zD i).card)
    (Q4FaceCapacity.five_le_card_of_deficiencyWitness hzD)

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9ThreeAxisCapacityTransport
