/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Completed-scanner continuations depend only on proper canonical boundaries. -/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer

/-! Relabelling all three complementary pairs preserves the completed-scanner transfer. -/

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry

open HardinA233255LiteralBridge (labelAdvance labelWeight rowFinish rowWeight)
open HardinA233255PairTransfer

theorem full_cell (q : Fin 3) :
    labelAdvance (true, true) q = (true, true) ∧ labelWeight (true, true) q = 2 := by
  fin_cases q <;> decide +kernel

theorem full_row (k : ℕ) (q : Fin k → Fin 3) :
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
  have hc : classOf (canonical p hp).val = classOf p := by
    unfold classOf
    rw [normalize_fixed (canonical p hp)]
    rfl
  have h := congrArg Subtype.val (shapeEquiv.apply_symm_apply (canonical p hp))
  change representatives (classOf (canonical p hp).val) = (canonical p hp).val at h
  rw [hc] at h
  exact h

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

private def hasTwo {k : ℕ} (q : Fin k → Fin 3) : Prop := ∃ j, q j = 2
private instance {k : ℕ} (q : Fin k → Fin 3) : Decidable (hasTwo q) :=
  inferInstanceAs (Decidable (∃ j, q j = 2))

private def alternating : Boundary := ![0, 1, 0, 1, 0, 1]
private def alternating' : Boundary := ![1, 0, 1, 0, 1, 0]
private def absentRow (p : Boundary) : PairRow := Fin.cons (p 5) p

set_option maxRecDepth 20000 in
private theorem unfinished_row : ∀ q : PairRow,
    rowFinish (true, false) q = (if hasTwo q then (true, true) else (true, false)) ∧
    rowWeight (true, false) q = (if hasTwo q then 64 else 128) := by
  decide +kernel

set_option maxRecDepth 20000 in
private theorem absent_row : ∀ p : Boundary, p = alternating ∨ p = alternating' →
    (rowProper (absentRow p) ∧ labelCompatible p (absentRow p)) ∧
    ¬ hasTwo (absentRow p) ∧
    (∀ q : PairRow, rowProper q ∧ labelCompatible p q → ¬ hasTwo q → q = absentRow p) := by
  decide +kernel

private theorem incomplete_step (n : ℕ) (p : Boundary)
    (hp : p = alternating ∨ p = alternating') :
    2 * pairV (n + 1) (true, false) p = pairV (n + 1) (true, true) p +
      128 * (2 * pairV n (true, false) p - pairV n (true, true) p) := by
  rw [pairV, full_step, Finset.mul_sum]
  have hs := absent_row p hp
  have hq (q : PairRow) :
      2 * (if rowProper q ∧ labelCompatible p q then
        rowWeight (true, false) q * pairV n (rowFinish (true, false) q) (labelBoundary q) else 0) =
      (if rowProper q ∧ labelCompatible p q then
        128 * pairV n (true, true) (labelBoundary q) else 0) +
      (if q = absentRow p then
        128 * (2 * pairV n (true, false) p - pairV n (true, true) p) else 0) := by
    by_cases hl : rowProper q ∧ labelCompatible p q
    · have hf := (unfinished_row q).1
      have hw := (unfinished_row q).2
      by_cases ht : hasTwo q
      · have hne : q ≠ absentRow p := fun h => hs.2.1 (h ▸ ht)
        simp only [ite_eq_left hl, hf, hw, ite_eq_left ht, ite_eq_right hne, add_zero]
        ring
      · have he := hs.2.2 q hl ht
        subst q
        simp only [ite_eq_left hs.1, (unfinished_row (absentRow p)).1,
          (unfinished_row (absentRow p)).2, ite_eq_right hs.2.1]
        change 2 * (128 * pairV n (true, false) p) = 128 * pairV n (true, true) p +
          128 * (2 * pairV n (true, false) p - pairV n (true, true) p)
        ring
    · have hne : q ≠ absentRow p := fun h => hl (h ▸ hs.1)
      simp [hl, hne]
  simp_rw [hq]
  rw [Finset.sum_add_distrib]
  simp

private theorem incomplete_relation (n : ℕ) (p : Boundary)
    (hp : p = alternating ∨ p = alternating') :
    2 * pairV n (true, false) p = pairV n (true, true) p + (128 : ℤ)^n := by
  induction n with
  | zero => norm_num [pairV]
  | succ n ih =>
    rw [incomplete_step n p hp]
    have h : 2 * pairV n (true, false) p - pairV n (true, true) p = (128 : ℤ)^n := by
      linarith
    rw [h, pow_succ]
    ring

private def initialFull (q : Boundary) : Prop :=
  rowProper (Fin.cons 0 q) ∧ q 0 = 1 ∧ hasTwo q
private instance (q : Boundary) : Decidable (initialFull q) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

set_option maxRecDepth 20000 in
private theorem initial_row : ∀ q : Boundary,
    (q = alternating' → rowProper (Fin.cons 0 q) ∧
      rowWeight (false, false) q = 32 ∧ rowFinish (false, false) q = (true, false)) ∧
    (initialFull q → proper q ∧ rowWeight (false, false) q = 16 ∧
      rowFinish (false, false) q = (true, true)) ∧
    (rowProper (Fin.cons 0 q) → q ≠ alternating' → ¬ initialFull q →
      rowWeight (false, false) q = 0) ∧
    (q = alternating' → ¬ initialFull q) := by
  decide +kernel

set_option maxRecDepth 20000 in
private theorem initial_mass : ∀ i : Fin 16,
    (∑ q : Boundary, if initialFull q ∧ classOf q = i then (16 : ℤ) else 0) =
      if i = 0 then 16 else 32 := by
  decide +kernel

set_option maxRecDepth 20000 in
private theorem initial_aggregation (n : ℕ) :
    (a ⟨n + 1, Nat.succ_pos n⟩ : ℤ) =
      32 * pairV n (true, false) alternating' +
        ∑ i : Fin 16, (if i = 0 then 16 else 32) * F n i := by
  rw [literal_pair_bridge]
  have hq (q : Boundary) :
      (if rowProper (Fin.cons 0 q) then
        rowWeight (false, false) q * pairV n (rowFinish (false, false) q) q else 0) =
      (if q = alternating' then 32 * pairV n (true, false) alternating' else 0) +
      (if initialFull q then 16 * F n (classOf q) else 0) := by
    have h := initial_row q
    by_cases ha : q = alternating'
    · subst q
      have hh := h.1 rfl
      simp only [ite_eq_left hh.1, hh.2.1, hh.2.2, ite_eq_right (h.2.2.2 rfl), add_zero, ite_true]
    · by_cases hf : initialFull q
      · have hh := h.2.1 hf
        have hl := hf.1
        simp only [ite_eq_left hl, hh.2.1, hh.2.2, completed_transfer_bridge n q hh.1,
          ite_eq_right ha, ite_eq_left hf, zero_add]
      · by_cases hl : rowProper (Fin.cons 0 q)
        · simp [hl, h.2.2.1 hl ha hf, ha, hf]
        · simp [hl, ha, hf]
  rw [Finset.sum_congr rfl (fun q _ => hq q), Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  congr 1
  simp_rw [← initial_mass, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  by_cases h : initialFull q
  · simp [h]
  · simp [h]

/-- Exact all-height formula for the original anchored individual-array count. -/
theorem literal_canonical_bridge (n : ℕ) :
    (a ⟨n + 1, Nat.succ_pos n⟩ : ℤ) = (16 : ℤ) * 128^n + 32 * ∑ i : Fin 16, F n i := by
  rw [initial_aggregation]
  have hp : proper alternating' := by decide +kernel
  have hc : classOf alternating' = 0 := by decide +kernel
  have hr := incomplete_relation n alternating' (Or.inr rfl)
  rw [completed_transfer_bridge n alternating' hp, hc] at hr
  have hm : (∑ i : Fin 16, (if i = 0 then (16 : ℤ) else 32) * F n i) =
      32 * ∑ i : Fin 16, F n i - 16 * F n 0 := by
    have he (i : Fin 16) : (if i = 0 then (16 : ℤ) else 32) * F n i =
        32 * F n i - (if i = 0 then 16 * F n 0 else 0) := by
      split_ifs with h
      · subst i; ring
      · ring
    simp_rw [he]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp
  rw [hm]
  linarith

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry
