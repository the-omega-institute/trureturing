/- GID: D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation.claim; result=D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation.result; claim=D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation.claim
   digest: The traceless degree-five complex at matrix size four is not free over diagonal creators. -/

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

set_option linter.style.longLine false

noncomputable section

namespace TierzTracelessFreenessRefutation

abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℂ

/-- The source's complex space of traceless matrices. -/
def traceless : Submodule ℂ Mat4 := LinearMap.ker (Matrix.traceLinearMap (Fin 4) ℂ ℂ)

abbrev V := ↥traceless
abbrev E := ExteriorAlgebra ℂ V

/-- The traceless part of the matrix-unit creator. -/
def creatorVec (i j : Fin 4) : V :=
  ⟨Matrix.single i j 1 - (if i = j then (1 / 4 : ℂ) else 0) • (1 : Mat4), by
    change Matrix.trace (Matrix.single i j (1 : ℂ) -
      (if i = j then (1 / 4 : ℂ) else 0) • (1 : Mat4)) = 0
    by_cases h : i = j
    · subst j
      simp only [Matrix.trace_sub, Matrix.trace_single_eq_same,
        Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]
      norm_num
    · simp only [if_neg h, zero_smul, sub_zero, Matrix.trace_single_eq_of_ne i j (1 : ℂ) h]⟩

/-- The actual traceless creator matrix. -/
def A : Matrix (Fin 4) (Fin 4) E := fun i j => ExteriorAlgebra.ι ℂ (creatorVec i j)

/-- The degree-five differential element. -/
def Q : E := Matrix.trace (A ^ 5)

private def coordMat (x : Fin 15 → ℂ) : Mat4 :=
  !![(3 * x 0 - x 1 - x 2) / 4, x 3, x 4, x 5;
     x 6, (3 * x 1 - x 0 - x 2) / 4, x 7, x 8;
     x 9, x 10, (3 * x 2 - x 0 - x 1) / 4, x 11;
     x 12, x 13, x 14, -(x 0 + x 1 + x 2) / 4]

private def fromCoords : (Fin 15 → ℂ) →ₗ[ℂ] V where
  toFun x := ⟨coordMat x, by
    change Matrix.trace (coordMat x) = 0
    rw [Matrix.trace]
    simp [Fin.sum_univ_succ, coordMat]
    ring⟩
  map_add' x y := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coordMat] <;> ring
  map_smul' r x := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coordMat] <;> ring

private def toCoords : V →ₗ[ℂ] (Fin 15 → ℂ) where
  toFun X := ![X.1 0 0 - X.1 3 3, X.1 1 1 - X.1 3 3, X.1 2 2 - X.1 3 3,
    X.1 0 1, X.1 0 2, X.1 0 3, X.1 1 0, X.1 1 2, X.1 1 3,
    X.1 2 0, X.1 2 1, X.1 2 3, X.1 3 0, X.1 3 1, X.1 3 2]
  map_add' X Y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' r X := by ext i; fin_cases i <;> simp <;> ring

private def coordinates : (Fin 15 → ℂ) ≃ₗ[ℂ] V :=
  LinearEquiv.ofLinearMap fromCoords toCoords
    (by
      apply LinearMap.ext
      intro X
      apply Subtype.ext
      have ht : X.1 0 0 + (X.1 1 1 + (X.1 2 2 + X.1 3 3)) = 0 := by
        have ht := X.2
        change Matrix.trace X.1 = 0 at ht
        rw [Matrix.trace] at ht
        simpa [Matrix.diag, Fin.sum_univ_succ] using ht
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [fromCoords, toCoords, coordMat] <;> linear_combination -ht / 4)
    (by
      apply LinearMap.ext
      intro x
      funext i
      fin_cases i <;> simp [fromCoords, toCoords, coordMat] <;> ring)

private def coordBasis : Module.Basis (Fin 15) ℂ V :=
  (Pi.basisFun ℂ (Fin 15)).map coordinates

private def ij : Fin 15 → Fin 4 × Fin 4 :=
  ![(0,0), (1,1), (2,2), (0,1), (0,2), (0,3), (1,0), (1,2), (1,3),
    (2,0), (2,1), (2,3), (3,0), (3,1), (3,2)]

set_option maxHeartbeats 1200000 in
-- This proof checks the 240 entries of the ordered coordinate basis.
private theorem coordBasis_eq (k : Fin 15) :
    coordBasis k = creatorVec (ij k).1 (ij k).2 := by
  change coordinates ((Pi.basisFun ℂ (Fin 15)) k) = _
  rw [Pi.basisFun_apply]
  change fromCoords (Pi.single k 1) = _
  apply Subtype.ext
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [fromCoords, coordMat, creatorVec, ij, Pi.single_apply,
      Matrix.single_apply, Matrix.one_apply, Fin.ext_iff]

private def g (k : Fin 15) : E := ExteriorAlgebra.ι ℂ (coordBasis k)

private theorem A_coordinates :
    A = !![g 0, g 3, g 4, g 5; g 6, g 1, g 7, g 8;
      g 9, g 10, g 2, g 11; g 12, g 13, g 14, -g 0 - g 1 - g 2] := by
  have hd : creatorVec 3 3 = -creatorVec 0 0 - creatorVec 1 1 - creatorVec 2 2 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [creatorVec, Matrix.single_apply,
      Matrix.one_apply, Fin.ext_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A, g, coordBasis_eq, ij, hd, map_sub, map_neg]

private abbrev Mask := Finset (Fin 15)
private abbrev Poly := List (Mask × ℤ)

/-- The increasing exterior-basis word indexed by the support mask. -/
private def mono (s : Mask) : E := coordBasis.ExteriorAlgebra s

private def eval (p : Poly) : E := (p.map fun t => t.2 • mono t.1).sum

private theorem eval_nil : eval [] = 0 := rfl

private theorem eval_cons (t : Mask × ℤ) (p : Poly) :
    eval (t :: p) = t.2 • mono t.1 + eval p := rfl

/-- Signature of the shuffle that sorts the two increasing words; overlap annihilates. -/
private def sign (s t : Mask) : ℤ :=
  if h : Disjoint s t then
    ((Set.powersetCard.permOfDisjoint
      (s := Set.powersetCard.ofCard (s := s) rfl)
      (t := Set.powersetCard.ofCard (s := t) rfl) h).sign : ℤ)
  else 0

private theorem mono_mul (s t : Mask) : mono s * mono t = sign s t • mono (s ∪ t) := by
  by_cases h : Disjoint s t
  · have he := ExteriorAlgebra.basis_mul_of_disjoint coordBasis
      (Set.powersetCard.ofCard (s := s) rfl)
      (Set.powersetCard.ofCard (s := t) rfl) h
    unfold Set.powersetCard.disjUnion at he
    simpa only [mono, sign, dif_pos h, Units.smul_def, Set.powersetCard.val_ofCard,
      Finset.disjUnion_eq_union] using he
  · have he := ExteriorAlgebra.basis_mul_of_not_disjoint coordBasis
      (Set.powersetCard.ofCard (s := s) rfl)
      (Set.powersetCard.ofCard (s := t) rfl) h
    simpa only [mono, sign, dif_neg h, zero_smul, Set.powersetCard.val_ofCard] using he

private def mergeTerm (t : Mask × ℤ) : Poly → Poly :=
  List.rec [t] (fun u us acc =>
    if t.1 = u.1 then (u.1, t.2 + u.2) :: us else u :: acc)

private def normalize (p : Poly) : Poly :=
  (p.foldr mergeTerm []).filter (fun t => t.2 != 0)

private theorem eval_mergeTerm (t : Mask × ℤ) (p : Poly) :
    eval (mergeTerm t p) = t.2 • mono t.1 + eval p := by
  induction p with
  | nil => simp [mergeTerm, eval]
  | cons u us ih =>
    change eval (if t.1 = u.1 then (u.1, t.2 + u.2) :: us else u :: mergeTerm t us) = _
    by_cases h : t.1 = u.1
    · rw [if_pos h, eval_cons]
      change (t.2 + u.2) • mono u.1 + eval us = _
      rw [add_smul, h, eval_cons]
      exact add_assoc _ _ _
    · rw [if_neg h]
      change u.2 • mono u.1 + eval (mergeTerm t us) = _
      rw [ih]
      rw [eval_cons]
      exact add_left_comm _ _ _

private theorem eval_filter (p : Poly) :
    eval (p.filter (fun t => t.2 != 0)) = eval p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    by_cases h : t.2 = 0
    · rw [List.filter_cons_of_neg (by simp [h])]
      rw [ih, eval_cons, h, zero_smul, zero_add]
    · have hb : (t.2 != 0) = true := bne_iff_ne.mpr h
      simp only [List.filter_cons, hb, if_true, eval_cons, ih]

private theorem eval_normalize (p : Poly) : eval (normalize p) = eval p := by
  rw [normalize, eval_filter]
  induction p with
  | nil => rfl
  | cons t p ih =>
    rw [List.foldr_cons, eval_mergeTerm, ih]
    rfl

private def add (p q : Poly) : Poly := normalize (p ++ q)

private theorem eval_add (p q : Poly) : eval (add p q) = eval p + eval q := by
  rw [add, eval_normalize]
  simp only [eval, List.map_append, List.sum_append]

private def termMul (t u : Mask × ℤ) : Mask × ℤ :=
  (t.1 ∪ u.1, (t.2 * u.2) * sign t.1 u.1)

private def mul (p q : Poly) : Poly :=
  normalize (p.flatMap fun t => q.map (termMul t))

private theorem eval_termMul (t u : Mask × ℤ) :
    (termMul t u).2 • mono (termMul t u).1 =
      (t.2 • mono t.1) * (u.2 • mono u.1) := by
  rw [smul_mul_assoc, mul_smul_comm, mono_mul, smul_smul, smul_smul]
  rfl

private theorem eval_mul_row (t : Mask × ℤ) (q : Poly) :
    eval (q.map (termMul t)) = (t.2 • mono t.1) * eval q := by
  induction q with
  | nil => simp [eval]
  | cons u q ih =>
    simp only [List.map_cons, eval, List.map_cons, List.sum_cons] at ih ⊢
    rw [eval_termMul, ih, mul_add]

private theorem eval_mul (p q : Poly) : eval (mul p q) = eval p * eval q := by
  rw [mul, eval_normalize]
  induction p with
  | nil => simp [eval]
  | cons t p ih =>
    simp only [List.flatMap_cons, eval, List.map_append, List.sum_append]
    change eval (q.map (termMul t)) + eval (p.flatMap _) = _
    rw [eval_mul_row, ih]
    simp only [eval, List.map_cons, List.sum_cons, add_mul]

private theorem mono_empty : mono ∅ = 1 := by
  rw [mono, ExteriorAlgebra.basis_apply]
  exact ExteriorAlgebra.ιMulti_zero_apply _

private theorem mono_singleton (k : Fin 15) : mono {k} = g k := by
  rw [mono, ExteriorAlgebra.basis_apply_ofCard coordBasis (Finset.card_singleton k),
    ExteriorAlgebra.ιMulti_family]
  simp only [ Set.powersetCard.ofFinEmbEquiv_symm_apply,
    Set.powersetCard.val_ofCard, Finset.orderEmbOfFin_singleton, Function.comp_apply,
    ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one, g]

private def varData (k : Fin 15) : Poly := [({k}, 1)]

private theorem eval_varData (k : Fin 15) : eval (varData k) = g k := by
  simp only [varData, eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    one_smul, add_zero, mono_singleton]

private def matrixEval (X : Matrix (Fin 4) (Fin 4) Poly) : Matrix (Fin 4) (Fin 4) E :=
  fun i j => eval (X i j)

private def matrixMul (X Y : Matrix (Fin 4) (Fin 4) Poly) :
    Matrix (Fin 4) (Fin 4) Poly :=
  fun i j => add (add (mul (X i 0) (Y 0 j)) (mul (X i 1) (Y 1 j)))
    (add (mul (X i 2) (Y 2 j)) (mul (X i 3) (Y 3 j)))

private theorem eval_matrix_mul (X Y : Matrix (Fin 4) (Fin 4) Poly) :
    matrixEval (matrixMul X Y) = matrixEval X * matrixEval Y := by
  ext i j
  simp only [matrixEval, matrixMul, eval_add, eval_mul, Matrix.mul_apply,
    Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  exact add_assoc _ _ _

private def matrixOne : Matrix (Fin 4) (Fin 4) Poly :=
  fun i j => if i = j then [(∅, 1)] else []

private theorem eval_matrix_one : matrixEval matrixOne = 1 := by
  ext i j
  by_cases h : i = j <;>
    simp [matrixEval, matrixOne, h, eval, mono_empty, Matrix.one_apply]

private def matrixPow (X : Matrix (Fin 4) (Fin 4) Poly) (n : ℕ) :
    Matrix (Fin 4) (Fin 4) Poly :=
  Nat.rec matrixOne (fun _ acc => matrixMul acc X) n

private theorem eval_matrix_pow (X : Matrix (Fin 4) (Fin 4) Poly) (n : ℕ) :
    matrixEval (matrixPow X n) = matrixEval X ^ n := by
  induction n with
  | zero => exact eval_matrix_one
  | succ n ih =>
    change matrixEval (matrixMul (matrixPow X n) X) = _
    rw [eval_matrix_mul, ih, pow_succ]

private def tracePow (X : Matrix (Fin 4) (Fin 4) Poly) (n : ℕ) : Poly :=
  let P := matrixPow X n
  add (add (P 0 0) (P 1 1)) (add (P 2 2) (P 3 3))

private theorem eval_tracePow (X : Matrix (Fin 4) (Fin 4) Poly) (n : ℕ) :
    eval (tracePow X n) = Matrix.trace (matrixEval X ^ n) := by
  rw [← eval_matrix_pow, Matrix.trace]
  simp only [tracePow, eval_add, Matrix.diag, matrixEval,
    Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  exact add_assoc _ _ _

private def AData : Matrix (Fin 4) (Fin 4) Poly :=
  !![varData 0, varData 3, varData 4, varData 5;
     varData 6, varData 1, varData 7, varData 8;
     varData 9, varData 10, varData 2, varData 11;
     varData 12, varData 13, varData 14, [({0}, -1), ({1}, -1), ({2}, -1)]]

private theorem eval_AData : matrixEval AData = A := by
  rw [A_coordinates]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixEval, AData, eval_varData, eval_cons, eval_nil, mono_singleton,
      sub_eq_add_neg, add_assoc]

private theorem Q_eq_eval : Q = eval (tracePow AData 5) := by
  rw [eval_tracePow, eval_AData]
  rfl

end TierzTracelessFreenessRefutation
