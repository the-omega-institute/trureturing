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

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry
