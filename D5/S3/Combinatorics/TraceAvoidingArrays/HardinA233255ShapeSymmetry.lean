/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry
   mirror-E: none
   anchors: []
   utility: none
   digest: Completed-scanner continuations depend only on proper canonical boundaries. -/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer

/-! Relabelling all three complementary pairs preserves the completed-scanner transfer. -/

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry

open HardinA233255LiteralBridge (labelAdvance labelWeight rowFinish rowWeight)
open HardinA233255PairTransfer

private theorem full_cell (q : Fin 3) :
    labelAdvance (true, true) q = (true, true) ∧ labelWeight (true, true) q = 2 := by
  fin_cases q <;> decide +kernel

private theorem full_row (k : ℕ) (q : Fin k → Fin 3) :
    rowFinish (true, true) q = (true, true) ∧ rowWeight (true, true) q = (2 : ℤ)^k := by
  induction k with
  | zero => simp [rowFinish, rowWeight]
  | succ k ih =>
    simp only [rowFinish, rowWeight, (full_cell (q 0)).1, (full_cell (q 0)).2]
    exact ⟨(ih (Fin.tail q)).1, by rw [(ih (Fin.tail q)).2, pow_succ]; ring⟩

private theorem full_step (n : ℕ) (p : Boundary) :
    pairV (n + 1) (true, true) p =
      ∑ q : PairRow, if rowProper q ∧ labelCompatible p q then
        128 * pairV n (true, true) (labelBoundary q) else 0 := by
  simp only [pairV, (full_row 7 _).1, (full_row 7 _).2]
  norm_num

private theorem permutation_invariant (n : ℕ) (e : Equiv.Perm (Fin 3)) (p : Boundary) :
    pairV n (true, true) (fun j => e (p j)) = pairV n (true, true) p := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    rw [full_step, full_step]
    let E : PairRow ≃ PairRow := Equiv.arrowCongr (Equiv.refl (Fin 7)) e
    rw [← E.sum_comp]
    apply Finset.sum_congr rfl
    intro q _
    change (if rowProper (fun j => e (q j)) ∧
        labelCompatible (fun j => e (p j)) (fun j => e (q j)) then
        128 * pairV n (true, true) (fun j => e (labelBoundary q j)) else 0) = _
    simp only [rowProper, labelCompatible, e.injective.ne_iff]
    rw [ih]
    rfl

def proper (p : Boundary) : Prop := ∀ j : Fin 5, p j.castSucc ≠ p j.succ
instance decidableProper (p : Boundary) : Decidable (proper p) :=
  inferInstanceAs (Decidable (∀ _, _))

abbrev Shape := {p : Boundary // proper p ∧ p 0 = 0 ∧ p 1 = 1}

private noncomputable def normalizer (a b : Fin 3) (hab : a ≠ b) : Equiv.Perm (Fin 3) :=
  Equiv.ofBijective (fun x => if x = a then 0 else if x = b then 1 else 2) (by
    have h : ∀ a b : Fin 3, a ≠ b → Function.Bijective
        (fun x : Fin 3 => if x = a then (0 : Fin 3) else if x = b then 1 else 2) := by
      decide +kernel
    exact h a b hab)

noncomputable def canonical (p : Boundary) (hp : proper p) : Shape := by
  have hab : p 0 ≠ p 1 := hp 0
  let e := normalizer (p 0) (p 1) hab
  refine ⟨fun j => e (p j), ?_, ?_, ?_⟩
  · intro j
    exact e.injective.ne (hp j)
  · simp [e, normalizer, Equiv.ofBijective]
  · simp [e, normalizer, Equiv.ofBijective, Ne.symm hab]

/-- Every completed-scanner continuation factors through the canonical proper boundary. -/
theorem completed_canonical_bridge (n : ℕ) (p : Boundary) (hp : proper p) :
    pairV n (true, true) (canonical p hp).val = pairV n (true, true) p := by
  exact permutation_invariant n (normalizer (p 0) (p 1) (hp 0)) p

/-- All proper canonical six-cell boundaries, without an orbit divisor. -/
def representatives : Fin 16 → Boundary :=
  ![![0, 1, 0, 1, 0, 1],
    ![0, 1, 0, 1, 0, 2],
    ![0, 1, 0, 1, 2, 0],
    ![0, 1, 0, 1, 2, 1],
    ![0, 1, 0, 2, 0, 1],
    ![0, 1, 0, 2, 0, 2],
    ![0, 1, 0, 2, 1, 0],
    ![0, 1, 0, 2, 1, 2],
    ![0, 1, 2, 0, 1, 0],
    ![0, 1, 2, 0, 1, 2],
    ![0, 1, 2, 0, 2, 0],
    ![0, 1, 2, 0, 2, 1],
    ![0, 1, 2, 1, 0, 1],
    ![0, 1, 2, 1, 0, 2],
    ![0, 1, 2, 1, 2, 0],
    ![0, 1, 2, 1, 2, 1]]

def normalize (p : Boundary) : Boundary :=
  fun j => if p j = p 0 then 0 else if p j = p 1 then 1 else 2

private def index (p : Boundary) : Fin 16 :=
  if p = representatives 0 then 0
  else if p = representatives 1 then 1
  else if p = representatives 2 then 2
  else if p = representatives 3 then 3
  else if p = representatives 4 then 4
  else if p = representatives 5 then 5
  else if p = representatives 6 then 6
  else if p = representatives 7 then 7
  else if p = representatives 8 then 8
  else if p = representatives 9 then 9
  else if p = representatives 10 then 10
  else if p = representatives 11 then 11
  else if p = representatives 12 then 12
  else if p = representatives 13 then 13
  else if p = representatives 14 then 14
  else 15

def classOf (p : Boundary) : Fin 16 := index (normalize p)

set_option maxRecDepth 20000 in
private theorem representatives_spec : ∀ i, proper (representatives i) ∧
    representatives i 0 = 0 ∧ representatives i 1 = 1 ∧ classOf (representatives i) = i := by
  decide +kernel

set_option maxRecDepth 20000 in
private theorem representatives_complete : ∀ p : Boundary, proper p →
    representatives (classOf p) = normalize p := by
  decide +kernel

private theorem normalize_fixed (p : Shape) : normalize p.val = p.val := by
  funext j
  have h0 := p.property.2.1
  have h1 := p.property.2.2
  simp only [normalize, h0, h1]
  have h : ∀ x : Fin 3, (if x = 0 then (0 : Fin 3) else if x = 1 then 1 else 2) = x := by
    decide +kernel
  exact h _

/-- The enumeration is an equivalence with the actual canonical-boundary subtype. -/
def shapeEquiv : Fin 16 ≃ Shape where
  toFun i := ⟨representatives i, (representatives_spec i).1,
    (representatives_spec i).2.1, (representatives_spec i).2.2.1⟩
  invFun p := classOf p.val
  left_inv i := (representatives_spec i).2.2.2
  right_inv p := by
    apply Subtype.ext
    exact (representatives_complete p.val p.property.1).trans (normalize_fixed p)

private theorem representative_canonical (p : Boundary) (hp : proper p) :
    representatives (classOf p) = (canonical p hp).val := by
  exact representatives_complete p hp

/-- The actual proper seven-cell pair-row fibres define every matrix entry. -/
def K : Matrix (Fin 16) (Fin 16) ℤ := fun i j =>
  ∑ q : PairRow, if rowProper q ∧ labelCompatible (representatives i) q ∧
    classOf (labelBoundary q) = j then 1 else 0

/-- Completed-scanner vector, with 128 individual-colour lifts per row. -/
def F (n : ℕ) (i : Fin 16) : ℤ := (128 : ℤ)^n * (K^n).mulVec (1 : Fin 16 → ℤ) i

private theorem boundary_proper (q : PairRow) (hq : rowProper q) :
    proper (labelBoundary q) := by
  intro j
  exact hq j.succ

private theorem K_mulVec (v : Fin 16 → ℤ) (i : Fin 16) :
    K.mulVec v i = ∑ q : PairRow,
      if rowProper q ∧ labelCompatible (representatives i) q then
        v (classOf (labelBoundary q)) else 0 := by
  simp only [Matrix.mulVec, dotProduct, K, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  by_cases h : rowProper q ∧ labelCompatible (representatives i) q
  · simp [h.1, h.2]
  · simp only [show ∀ j, ¬ (rowProper q ∧ labelCompatible (representatives i) q ∧
        classOf (labelBoundary q) = j) from fun _ hh => h ⟨hh.1, hh.2.1⟩,
      ite_false, zero_mul, Finset.sum_const_zero, h]

/-- Exact all-height identification with powers of the actual canonical transfer. -/
theorem completed_transfer_bridge (n : ℕ) (p : Boundary) (hp : proper p) :
    pairV n (true, true) p = F n (classOf p) := by
  induction n generalizing p with
  | zero => simp [pairV, F, Matrix.one_mulVec]
  | succ n ih =>
    rw [← completed_canonical_bridge (n + 1) p hp,
      ← representative_canonical p hp, full_step]
    have hr (q : PairRow) (hq : rowProper q ∧
        labelCompatible (representatives (classOf p)) q) :=
      ih (labelBoundary q) (boundary_proper q hq.1)
    simp_rw [F] at *
    simp only [pow_succ', ← Matrix.mulVec_mulVec, K_mulVec]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    split_ifs with h
    · rw [hr q h]
      ring
    · ring

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry
