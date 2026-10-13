import D5.S3.Geometry.Polytope.SimplexTruncationCollar
import D5.S3.Geometry.Hyperideal.LengthGramPolytope

/-! # Marked collars for positive length-Gram bodies

The six positive original lengths determine a collar homeomorphism from the fixed
coordinate truncation to the length-Gram cut body, with labeled faces and endpoints.
-/
noncomputable section
open Set
open scoped BigOperators
set_option autoImplicit false
namespace NativeMarkedCollar

open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Polytope.SimplexTruncationCollar

/-- Independently fixed, length-free coefficient source. -/
abbrev T : Set (Fin 4 → ℝ) :=
  stdSimplex ℝ (Fin 4) ∩ {x | ∀ i, x i ≤ 2 / 3}

private theorem gram_diag (l : Fin 6 → ℝ) (i : Fin 4) : lengthGram l i i = 1 := by
  fin_cases i <;> rfl

private theorem gram_off (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q)
    (i j : Fin 4) (hij : i ≠ j) : lengthGram l i j < -1 := by
  have hc (q : Fin 6) : 1 < Real.cosh (l q) := Real.one_lt_cosh.mpr (ne_of_gt (hl q))
  fin_cases i <;> fin_cases j <;> first
    | exact (hij rfl).elim
    | exact neg_lt_neg (hc 0)
    | exact neg_lt_neg (hc 1)
    | exact neg_lt_neg (hc 2)
    | exact neg_lt_neg (hc 3)
    | exact neg_lt_neg (hc 4)
    | exact neg_lt_neg (hc 5)

/-- The collar homeomorphism onto the original length-Gram cut body. -/
def originalHomeomorph (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q) : T ≃ₜ cutBody l :=
  D5.S3.Geometry.Polytope.SimplexTruncationCollar.homeomorph (lengthGram l) (gram_diag l) (gram_off l hl)

/-- The forward and inverse formulas, face markings, and ordered endpoint markings. -/
example (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q) :
    ∃ h : T ≃ₜ cutBody l,
      (∀ x : T, (h x).val = D5.S3.Geometry.Polytope.SimplexTruncationCollar.H (lengthGram l) x.val) ∧
      (∀ z : cutBody l, (h.symm z).val = D5.S3.Geometry.Polytope.SimplexTruncationCollar.J (lengthGram l) z.val) ∧
      (∀ x : T, ∀ i, (h x).val i = 0 ↔ x.val i = 0) ∧
      (∀ x : T, ∀ i,
        (∑ j, lengthGram l i j * (h x).val j) = 0 ↔ x.val i = 2 / 3) ∧
      (∀ i j (hij : i ≠ j),
        (h ⟨D5.S3.Geometry.Polytope.SimplexTruncationCollar.standardEndpoint i j, D5.S3.Geometry.Polytope.SimplexTruncationCollar.standardEndpoint_mem hij⟩).val = D5.S3.Geometry.Hyperideal.LengthGramPolytope.endpoint l i j) := by
  refine ⟨originalHomeomorph l hl, fun _ => rfl, fun _ => rfl, ?_, ?_, ?_⟩
  · intro x i
    exact D5.S3.Geometry.Polytope.SimplexTruncationCollar.H_side_zero (lengthGram l) (gram_diag l) (gram_off l hl) x.property i
  · intro x i
    exact D5.S3.Geometry.Polytope.SimplexTruncationCollar.H_cap_zero (lengthGram l) (gram_diag l) (gram_off l hl) x.property i
  · intro i j hij
    exact D5.S3.Geometry.Polytope.SimplexTruncationCollar.H_endpoint (lengthGram l) (gram_off l hl) hij

/-- Every ordered length-Gram endpoint belongs to the cut body. -/
example (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q) (i j : Fin 4) (hij : i ≠ j) :
    D5.S3.Geometry.Hyperideal.LengthGramPolytope.endpoint l i j ∈ cutBody l :=
  ((D5.S3.Geometry.Hyperideal.LengthGramPolytope.cut_body_polytope l hl).2.2.2 i j hij).1

end NativeMarkedCollar

-- A two-coordinate truncation with a nonsymmetric matrix.
example : Nonempty
    ((D5.S3.Geometry.Polytope.SimplexTruncationCollar.standard : Set (Fin 2 → ℝ)) ≃ₜ
      D5.S3.Geometry.Polytope.SimplexTruncationCollar.cut
        (fun i j : Fin 2 => if i = j then (1 : ℝ) else if i = 0 then -2 else -3)) := by
  refine ⟨D5.S3.Geometry.Polytope.SimplexTruncationCollar.homeomorph _ ?_ ?_⟩
  · intro i; simp
  · intro i j hij
    simp only [if_neg hij]
    split_ifs <;> norm_num

#print axioms D5.S3.Geometry.Polytope.SimplexTruncationCollar.H_mem
#print axioms D5.S3.Geometry.Polytope.SimplexTruncationCollar.J_mem
#print axioms D5.S3.Geometry.Polytope.SimplexTruncationCollar.J_H
#print axioms D5.S3.Geometry.Polytope.SimplexTruncationCollar.H_J
#print axioms D5.S3.Geometry.Polytope.SimplexTruncationCollar.continuous_H
#print axioms D5.S3.Geometry.Polytope.SimplexTruncationCollar.continuous_J
#print axioms D5.S3.Geometry.Polytope.SimplexTruncationCollar.homeomorph
#print axioms D5.S3.Geometry.Polytope.SimplexTruncationCollar.H_side_zero
#print axioms D5.S3.Geometry.Polytope.SimplexTruncationCollar.H_cap_zero
#print axioms D5.S3.Geometry.Polytope.SimplexTruncationCollar.H_endpoint
#print axioms D5.S3.Geometry.Polytope.SimplexTruncationCollar.standardEndpoint_mem
#print axioms D5.S3.Geometry.Polytope.SimplexTruncationCollar.marked_spec
#print axioms NativeMarkedCollar.originalHomeomorph
