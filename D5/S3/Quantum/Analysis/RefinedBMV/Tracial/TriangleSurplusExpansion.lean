/- GID: D5/S3/Quantum/Analysis/RefinedBMV/Tracial/TriangleSurplusExpansion
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bounds for the shifted surplus polynomials without expanding their coefficients. -/

import D5.S3.Quantum.Analysis.RefinedBMV.Tracial.TriangleSurplusFormula
import D5.S3.Quantum.Analysis.RefinedBMV.ThreeSpectrum.QuarticPacking

/-! The bounded expansion is used symbolically. Its degree and mass fields
reduce without materializing the terms of the polynomial. -/

namespace RefinedBMV.Tracial.TriangleSurplus

open RefinedBMV.DividedDifference.SparseExpansion

abbrev Expansion := BoundedExpansion

private def const (n : Nat) : Expansion := BoundedExpansion.single ⟨0, 0, 0, 0, 0⟩ n
private instance : NatCast Expansion := ⟨const⟩

/-- Interpret the circuit over the shifted variables `1 + u` and `1 + v`. -/
def expansion : Expansion × Expansion × Expansion :=
  surplus (const 1 + BoundedExpansion.single ⟨0, 1, 0, 0, 0⟩ 1)
    (const 1 + BoundedExpansion.single ⟨0, 0, 1, 0, 0⟩ 1)

def select {R : Type*} (e : Fin 3) (p : R × R × R) : R :=
  if e.val = 0 then p.1 else if e.val = 1 then p.2.1 else p.2.2

def evalExpansion {R : Type*} [CommRing R] (u v : R) (a : Expansion) : R :=
  a.eval (1 : R) u v 1 1

variable {R : Type*} [CommRing R] (u v : R)

@[simp] private theorem eval_add (a b : Expansion) :
    evalExpansion u v (a + b) = evalExpansion u v a + evalExpansion u v b :=
  eval_bounded_add _ _ _ _ _ _ _

@[simp] private theorem eval_sub (a b : Expansion) :
    evalExpansion u v (a - b) = evalExpansion u v a - evalExpansion u v b :=
  eval_bounded_sub _ _ _ _ _ _ _

@[simp] private theorem eval_mul (a b : Expansion) :
    evalExpansion u v (a * b) = evalExpansion u v a * evalExpansion u v b :=
  eval_bounded_mul _ _ _ _ _ _ _

@[simp] private theorem eval_pow (a : Expansion) (n : Nat) :
    evalExpansion u v (a ^ n) = evalExpansion u v a ^ n :=
  eval_bounded_pow _ _ _ _ _ _ _

@[simp] private theorem eval_nat (n : ℕ) :
    evalExpansion u v (↑n : Expansion) = (n : R) := by
  change (BoundedExpansion.single ⟨0, 0, 0, 0, 0⟩ n).eval (1 : R) u v 1 1 = _
  simp [eval_bounded_single]

private theorem eval_adjoin (x prev : Expansion) (row : List Expansion) :
    (adjoin x prev row).map (evalExpansion u v) =
      adjoin (evalExpansion u v x) (evalExpansion u v prev) (row.map (evalExpansion u v)) := by
  induction row generalizing prev with
  | nil => rfl
  | cons a as ih => simp [adjoin, ih]

private theorem eval_extend (x : Expansion) (row : List Expansion) :
    (extend x row).map (evalExpansion u v) =
      extend (evalExpansion u v x) (row.map (evalExpansion u v)) := by
  cases row <;> simp [extend, eval_adjoin]

private theorem eval_getD (row : List Expansion) (i : Nat) (fallback : Expansion) :
    evalExpansion u v (row[i]?.getD fallback) =
      (row.map (evalExpansion u v))[i]?.getD (evalExpansion u v fallback) := by
  rw [List.getElem?_map]
  cases row[i]? <;> rfl

@[simp] private theorem eval_gap (a b c d : Expansion) :
    evalExpansion u v (gap a b c d) =
      gap (evalExpansion u v a) (evalExpansion u v b) (evalExpansion u v c) (evalExpansion u v d) := by
  simp only [gap, eval_sub, eval_getD, eval_extend, eval_mul, eval_pow, eval_nat,
    List.map_cons, List.map_replicate]

theorem eval_selected_expansion (e : Fin 3) :
    evalExpansion u v (select e expansion) = select e (surplus (1 + u) (1 + v)) := by
  have hu : evalExpansion u v (const 1 + BoundedExpansion.single ⟨0, 1, 0, 0, 0⟩ 1) =
      1 + u := by
    rw [eval_add]
    change (BoundedExpansion.single ⟨0, 0, 0, 0, 0⟩ 1).eval (1 : R) u v 1 1 +
      (BoundedExpansion.single ⟨0, 1, 0, 0, 0⟩ 1).eval (1 : R) u v 1 1 = _
    simp [eval_bounded_single]
  have hv : evalExpansion u v (const 1 + BoundedExpansion.single ⟨0, 0, 1, 0, 0⟩ 1) =
      1 + v := by
    rw [eval_add]
    change (BoundedExpansion.single ⟨0, 0, 0, 0, 0⟩ 1).eval (1 : R) u v 1 1 +
      (BoundedExpansion.single ⟨0, 0, 1, 0, 0⟩ 1).eval (1 : R) u v 1 1 = _
    simp [eval_bounded_single]
  unfold expansion
  generalize const 1 + BoundedExpansion.single ⟨0, 1, 0, 0, 0⟩ 1 = a at hu ⊢
  generalize const 1 + BoundedExpansion.single ⟨0, 0, 1, 0, 0⟩ 1 = b at hv ⊢
  rw [← hu, ← hv]
  fin_cases e <;>
    simp only [select, Nat.reduceEqDiff, ite_true, ite_false, surplus, cleared, clearedOfEntries,
      eval_sub, eval_add, eval_mul, eval_pow, eval_nat, eval_gap, Edge.form, edge]

set_option maxHeartbeats 0 in
-- Reduce the degree and mass fields of the three closed circuits.
theorem expansion_bounds (e : Fin 3) :
    (select e expansion).degree.x ≤ 816 ∧ (select e expansion).degree.y ≤ 918 ∧
      (select e expansion).mass < (2 : ℤ) ^ 1983 := by
  fin_cases e <;> decide +kernel

/-- Bounds for the terms of any one of the three shifted surpluses. -/
theorem expansion_term_bounds (e : Fin 3) (t : Term) (ht : t ∈ (select e expansion).terms) :
    t.exponents.x ≤ 816 ∧ t.exponents.y ≤ 918 := by
  have hterm := (select e expansion).term_bound t ht
  have hd := expansion_bounds e
  exact ⟨hterm.2.1.trans hd.1, hterm.2.2.1.trans hd.2.1⟩

theorem expansion_mass (e : Fin 3) :
    coeffMass (select e expansion).terms < (2 : ℤ) ^ 1983 :=
  (select e expansion).mass_bound.trans_lt (expansion_bounds e).2.2

#print axioms expansion_bounds

end RefinedBMV.Tracial.TriangleSurplus
