/- GID: D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation.claim; result=D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation.result; claim=D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation.claim
   digest: Refutes diagonal freeness for the traceless degree-five complex at size four. -/

import Mathlib.Algebra.Lie.Classical
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.CliffordAlgebra.Prod
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.Tactic.LinearCombination

set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Quantum.Fermionic.TierzTracelessFreenessRefutation

/-- The source's complex space of traceless matrices. -/
abbrev V := ↥(LieAlgebra.SpecialLinear.sl (Fin 4) ℂ)
abbrev E := ExteriorAlgebra ℂ V

/-- The traceless part of the matrix-unit creator. -/
def creatorVec (i j : Fin 4) : V :=
  ⟨Matrix.single i j 1 - (if i = j then (1 / 4 : ℂ) else 0) •
    (1 : Matrix (Fin 4) (Fin 4) ℂ), by
    change Matrix.trace (Matrix.single i j (1 : ℂ) -
      (if i = j then (1 / 4 : ℂ) else 0) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) = 0
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

private def coordMat (x : Fin 15 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(3 * x 0 - x 1 - x 2) / 4, x 3, x 4, x 5;
     x 6, (3 * x 1 - x 0 - x 2) / 4, x 7, x 8;
     x 9, x 10, (3 * x 2 - x 0 - x 1) / 4, x 11;
     x 12, x 13, x 14, -(x 0 + x 1 + x 2) / 4]

private def fromCoords : (Fin 15 → ℂ) →ₗ[ℂ] V where
  toFun x := ⟨coordMat x, by
    change Matrix.trace (coordMat x) = 0
    rw [Matrix.trace]
    simp [Fin.sum_univ_succ, coordMat.eq_1]
    ring⟩
  map_add' x y := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coordMat.eq_1] <;> ring
  map_smul' r x := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coordMat.eq_1] <;> ring

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
        simp [fromCoords.eq_1, toCoords.eq_1, coordMat.eq_1] <;> linear_combination -ht / 4)
    (by
      apply LinearMap.ext
      intro x
      funext i
      fin_cases i <;> simp [fromCoords.eq_1, toCoords.eq_1, coordMat.eq_1] <;> ring)

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
    norm_num [fromCoords.eq_1, coordMat.eq_1, creatorVec.eq_1, ij.eq_1, Pi.single_apply,
      Matrix.single_apply, Matrix.one_apply, Fin.ext_iff]

private def g (k : Fin 15) : E := ExteriorAlgebra.ι ℂ (coordBasis k)

private theorem A_coordinates :
    A = !![g 0, g 3, g 4, g 5; g 6, g 1, g 7, g 8;
      g 9, g 10, g 2, g 11; g 12, g 13, g 14, -g 0 - g 1 - g 2] := by
  have hd : creatorVec 3 3 = -creatorVec 0 0 - creatorVec 1 1 - creatorVec 2 2 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [creatorVec.eq_1, Matrix.single_apply,
      Matrix.one_apply, Fin.ext_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A.eq_1, g.eq_1, coordBasis_eq, ij.eq_1, hd, map_sub, map_neg]

variable {U : Type*} [AddCommGroup U] [Module ℂ U]
private def word (n : ℕ) : (ℕ → U) → ℕ → ExteriorAlgebra ℂ U :=
  Nat.rec (fun _ _ => 1) (fun _ rec v s =>
    if s % 2 = 1 then ExteriorAlgebra.ι ℂ (v 0) * rec (fun i => v (i+1)) (s/2)
    else rec (fun i => v (i+1)) (s/2)) n
private def parity (n : ℕ) : ℕ → ℤ :=
  Nat.rec (fun _ => 1) (fun _ rec s =>
    (if s % 2 = 1 then -1 else 1) * rec (s/2)) n
private def sg (n : ℕ) : ℕ → ℕ → ℤ :=
  Nat.rec (fun _ _ => 1) (fun k rec s t =>
    if s % 2 = 1 ∧ t % 2 = 1 then 0 else
    (if t % 2 = 1 then parity k (s/2) else 1) * rec (s/2) (t/2)) n
private theorem word_succ (n : ℕ) (v : ℕ → U) (s : ℕ) :
    word (n+1) v s = if s % 2 = 1 then ExteriorAlgebra.ι ℂ (v 0) *
      word n (fun i => v (i+1)) (s/2) else word n (fun i => v (i+1)) (s/2) := rfl
private theorem parity_succ (n s : ℕ) : parity (n+1) s =
    (if s % 2 = 1 then -1 else 1) * parity n (s/2) := rfl
private theorem sg_succ (n s t : ℕ) : sg (n+1) s t =
    if s % 2 = 1 ∧ t % 2 = 1 then 0 else
    (if t % 2 = 1 then parity n (s/2) else 1) * sg n (s/2) (t/2) := rfl
private theorem word_comm (n : ℕ) (v : ℕ → U) (s : ℕ) (u : U) :
    word n v s * ExteriorAlgebra.ι ℂ u =
      parity n s • (ExteriorAlgebra.ι ℂ u * word n v s) := by
  induction n generalizing s v with
  | zero => simp [word.eq_1, parity.eq_1]
  | succ n ih =>
    rw [word_succ, parity_succ]
    by_cases hs : s % 2 = 1
    · simp only [if_pos hs, mul_assoc, ih, mul_smul_comm]
      rw [← mul_assoc, eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (v 0) u)]
      simp [neg_smul, mul_assoc]
    · simp only [if_neg hs, one_mul]
      exact ih _ _
private theorem word_mul (n : ℕ) (v : ℕ → U) (s t : ℕ) :
    word n v s * word n v t = sg n s t • word n v (s ||| t) := by
  induction n generalizing v s t with
  | zero => simp [word.eq_1, sg.eq_1]
  | succ n ih =>
    have hor : (s ||| t) % 2 = 1 ↔ s % 2 = 1 ∨ t % 2 = 1 := Nat.or_mod_two_eq_one
    rw [word_succ, word_succ, word_succ, sg_succ]
    by_cases hs : s % 2 = 1 <;> by_cases ht : t % 2 = 1
    · simp only [hs, ht, true_and, if_true, zero_smul]
      rw [mul_assoc, ← mul_assoc (word n _ _) _ _, word_comm]
      rw [smul_mul_assoc, mul_smul_comm]
      simp only [mul_assoc]
      rw [← mul_assoc (ExteriorAlgebra.ι ℂ (v 0)) (ExteriorAlgebra.ι ℂ (v 0)),
        ExteriorAlgebra.ι_sq_zero, zero_mul, smul_zero]
    · simp only [hs, ht, and_false, if_false, if_true, one_mul,
        if_pos (hor.mpr (Or.inl hs)), Nat.or_div_two]
      rw [mul_assoc, ih, mul_smul_comm]
    · simp only [hs, ht, false_and, if_false, if_true,
        if_pos (hor.mpr (Or.inr ht)), Nat.or_div_two]
      rw [← mul_assoc, word_comm, smul_mul_assoc, mul_assoc, ih, mul_smul_comm, smul_smul]
    · simp only [hs, ht, false_and, if_false, one_mul,
        if_neg (fun h => (hor.mp h).elim hs ht), Nat.or_div_two]
      exact ih _ _ _
private def allowed (n : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (fun _ _ => true) (fun _ rec s k =>
    (if s % 2 = 1 then decide (k % 2 = 1) else true) && rec (s/2) (k/2)) n
private theorem allowed_succ (n s k : ℕ) : allowed (n+1) s k =
    ((if s % 2 = 1 then decide (k % 2 = 1) else true) && allowed n (s/2) (k/2)) := rfl
private theorem word_projection (n : ℕ) (v : ℕ → U) (s k : ℕ)
    (π : ExteriorAlgebra ℂ U →ₐ[ℂ] ExteriorAlgebra ℂ U)
    (hv : ∀ i < n, π (ExteriorAlgebra.ι ℂ (v i)) =
      if k.testBit i then ExteriorAlgebra.ι ℂ (v i) else 0) :
    π (word n v s) = if allowed n s k then word n v s else 0 := by
  induction n generalizing v s k with
  | zero => simp [word.eq_1,allowed.eq_1]
  | succ n ih =>
    have hv0 := hv 0 (Nat.zero_lt_succ _)
    have hvt : ∀ i < n, π (ExteriorAlgebra.ι ℂ (v (i+1))) =
        if (k/2).testBit i then ExteriorAlgebra.ι ℂ (v (i+1)) else 0 := by
      intro i hi
      simpa only [Nat.testBit_div_two] using hv (i+1) (Nat.succ_lt_succ hi)
    rw [word_succ, allowed_succ]
    by_cases hs : s % 2 = 1
    · rw [if_pos hs, map_mul, hv0, ih _ _ _ hvt]
      rw [Nat.testBit_eq_decide_div_mod_eq] at *
      by_cases hk : k%2=1 <;> by_cases ha : allowed n (s/2) (k/2) = true <;>
        simp [hs,hk,ha] at *
    · rw [if_neg hs, ih _ _ _ hvt]
      simp [hs]
private theorem word_zero_mask (n : ℕ) (v : ℕ → U) : word n v 0=1 := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => rw [word_succ]; simpa using ih (fun i => v (i+1))
private theorem word_single (n k : ℕ) (hk : k < n) (v : ℕ → U) :
    word n v (2^k) = ExteriorAlgebra.ι ℂ (v k) := by
  induction n generalizing k v with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero => simp [word_succ,word_zero_mask]
    | succ k =>
      have hmod : 2^(k+1)%2=0 := by simp [pow_succ]
      have hdiv : 2^(k+1)/2=2^k := by simp [pow_succ]
      rw [word_succ,if_neg (by omega),hdiv]
      exact ih k (by omega) (fun i => v (i+1))
private def weight (n : ℕ) : ℕ → ℕ :=
  Nat.rec (fun _ => 0) (fun _ rec s => if s%2=1 then rec (s/2)+1 else rec (s/2)) n
private theorem word_hom (n : ℕ) (v : ℕ → U) (s : ℕ) :
    word n v s ∈ ExteriorAlgebra.exteriorPower ℂ (weight n s) U := by
  induction n generalizing v s with
  | zero => exact Submodule.algebraMap_mem (R := ℂ) 1
  | succ n ih =>
    change word (n+1) v s ∈ LinearMap.range (ExteriorAlgebra.ι ℂ)^
      (if s%2=1 then weight n (s/2)+1 else weight n (s/2))
    rw [word_succ]
    by_cases hs : s%2=1
    · rw [if_pos hs,if_pos hs,pow_succ']
      exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) (ih _ _)
    · rw [if_neg hs,if_neg hs]
      exact ih _ _

private abbrev Mask := Fin (2^15)
private abbrev Poly := List (Mask × ℤ)
private def basisSeq (i : ℕ) : V := coordBasis ⟨i % 15, Nat.mod_lt _ (by decide)⟩
private def mono (s : Mask) : E := word 15 basisSeq s.val
private def eval (p : Poly) : E := (p.map fun t => t.2 • mono t.1).sum
private theorem eval_nil : eval [] = 0 := rfl
private theorem eval_cons (t : Mask × ℤ) (p : Poly) :
    eval (t :: p) = t.2 • mono t.1 + eval p := rfl
private def join (s t : Mask) : Mask := ⟨s.val ||| t.val, Nat.or_lt_two_pow s.isLt t.isLt⟩
private def sign (s t : Mask) : ℤ := sg 15 s.val t.val
private theorem mono_mul (s t : Mask) : mono s * mono t = sign s t • mono (join s t) :=
  word_mul 15 basisSeq s.val t.val

private def mergeTerm (t : Mask × ℤ) : Poly → Poly :=
  List.rec [t] (fun u us acc =>
    if t.1 = u.1 then (u.1, t.2 + u.2) :: us else u :: acc)

private def normalize (p : Poly) : Poly :=
  ((p.filter (fun t => t.2 != 0)).foldr mergeTerm []).filter (fun t => t.2 != 0)

private theorem eval_mergeTerm (t : Mask × ℤ) (p : Poly) :
    eval (mergeTerm t p) = t.2 • mono t.1 + eval p := by
  induction p with
  | nil => simp [mergeTerm.eq_1, eval.eq_1]
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
  have hf (q : Poly) : eval (q.foldr mergeTerm [])=eval q := by
    induction q with
    | nil => rfl
    | cons t q ih => rw [List.foldr_cons,eval_mergeTerm,ih]; rfl
  rw [normalize,eval_filter,hf,eval_filter]

private def add (p q : Poly) : Poly := normalize (p ++ q)

private theorem eval_add (p q : Poly) : eval (add p q) = eval p + eval q := by
  rw [add, eval_normalize]
  simp only [eval.eq_1, List.map_append, List.sum_append]

private def termMul (t u : Mask × ℤ) : Mask × ℤ :=
  (join t.1 u.1, (t.2 * u.2) * sign t.1 u.1)

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
  | nil => simp [eval.eq_1]
  | cons u q ih =>
    simp only [List.map_cons, eval.eq_1, List.map_cons, List.sum_cons] at ih ⊢
    rw [eval_termMul, ih, mul_add]

private theorem eval_mul (p q : Poly) : eval (mul p q) = eval p * eval q := by
  rw [mul, eval_normalize]
  induction p with
  | nil => simp [eval.eq_1]
  | cons t p ih =>
    simp only [List.flatMap_cons, eval.eq_1, List.map_append, List.sum_append]
    change eval (q.map (termMul t)) + eval (p.flatMap _) = _
    rw [eval_mul_row, ih]
    simp only [eval.eq_1, List.map_cons, List.sum_cons, add_mul]

private theorem mono_empty : mono 0 = 1 := word_zero_mask 15 basisSeq
private def singletonMask (k : Fin 15) : Mask :=
  ⟨2^k.val, Nat.pow_lt_pow_right (by decide) k.isLt⟩
private theorem mono_singleton (k : Fin 15) : mono (singletonMask k) = g k := by
  exact (word_single 15 k.val k.isLt basisSeq).trans (by simp [basisSeq.eq_1,g.eq_1,Nat.mod_eq_of_lt k.isLt])
private def varData (k : Fin 15) : Poly := [(singletonMask k, 1)]
private theorem eval_varData (k : Fin 15) : eval (varData k) = g k := by
  simp only [varData.eq_1, eval.eq_1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
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
  simp only [matrixEval.eq_1, matrixMul.eq_1, eval_add, eval_mul, Matrix.mul_apply,
    Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  exact add_assoc _ _ _

private def matrixOne : Matrix (Fin 4) (Fin 4) Poly :=
  fun i j => if i = j then [(0, 1)] else []

private theorem eval_matrix_one : matrixEval matrixOne = 1 := by
  ext i j
  by_cases h : i = j <;>
    simp [matrixEval.eq_1, matrixOne.eq_1, h, eval.eq_1, mono_empty, Matrix.one_apply]

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
  simp only [tracePow.eq_1, eval_add, Matrix.diag, matrixEval.eq_1,
    Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  exact add_assoc _ _ _

private def AData : Matrix (Fin 4) (Fin 4) Poly :=
  !![varData 0, varData 3, varData 4, varData 5;
     varData 6, varData 1, varData 7, varData 8;
     varData 9, varData 10, varData 2, varData 11;
     varData 12, varData 13, varData 14, [(singletonMask 0, -1), (singletonMask 1, -1), (singletonMask 2, -1)]]

private theorem eval_AData : matrixEval AData = A := by
  rw [A_coordinates]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixEval.eq_1, AData.eq_1, eval_varData, eval_cons, eval_nil, mono_singleton,
      sub_eq_add_neg, add_assoc]

private theorem Q_eq_eval : Q = eval (tracePow AData 5) := by
  rw [eval_tracePow, eval_AData]
  rfl

variable {U : Type*} [AddCommGroup U] [Module ℂ U]
private theorem odd_involute {a : ExteriorAlgebra ℂ U}
    (ha : a ∈ ExteriorAlgebra.exteriorPower ℂ 5 U) : CliffordAlgebra.involute a = -a :=
  CliffordAlgebra.involute_eq_of_mem_odd
    (Submodule.mem_iSup_of_mem ⟨5,by decide⟩ ha)
private theorem odd_comm (a : ExteriorAlgebra ℂ U)
    (ha : a ∈ ExteriorAlgebra.exteriorPower ℂ 5 U) (x : ExteriorAlgebra ℂ U) :
    x*a = a*CliffordAlgebra.involute x := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes, Algebra.commutes]
  | ι v =>
    have hoa : a ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ U) 1 :=
      Submodule.mem_iSup_of_mem ⟨5,by decide⟩ ha
    have hov := CliffordAlgebra.ι_mem_evenOdd_one (0 : QuadraticForm ℂ U) v
    have h := CliffordAlgebra.map_mul_map_eq_neg_of_isOrtho_of_mem_evenOdd_one
      (QuadraticMap.Isometry.id (0 : QuadraticForm ℂ U))
      (QuadraticMap.Isometry.id (0 : QuadraticForm ℂ U))
      (fun _ _ => .all _ _) (ExteriorAlgebra.ι ℂ v) a hov hoa
    simpa only [CliffordAlgebra.map_id,AlgHom.id_apply,neg_mul,
      CliffordAlgebra.involute_ι,mul_neg] using h
  | mul x y hx hy => rw [map_mul, mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
  | add x y hx hy => rw [map_add, add_mul, hx, hy, mul_add]
private theorem odd_square (a : ExteriorAlgebra ℂ U)
    (ha : a ∈ ExteriorAlgebra.exteriorPower ℂ 5 U) : a*a=0 := by
  have h := odd_comm a ha a
  have ht := odd_involute ha
  rw [ht, mul_neg] at h
  have h2 : (2 : ℂ) • (a*a) = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp h
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
private theorem free_creator_exact
    {M : Type*} [AddCommGroup M] [Module (ExteriorAlgebra ℂ U) M]
    [Module.Free (ExteriorAlgebra ℂ U) M]
    (u : U) (hu : u ≠ 0) (m : M) :
    ExteriorAlgebra.ι ℂ u • m = 0 ↔ ∃ n : M, ExteriorAlgebra.ι ℂ u • n = m := by
  constructor
  · intro hm
    classical
    obtain ⟨φ,hφ⟩ := Module.Projective.exists_dual_eq_one ℂ hu
    let b := Module.Free.chooseBasis (ExteriorAlgebra ℂ U) M
    let c := CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ U)) φ
    let f := (b.repr m).mapRange c c.map_zero
    refine ⟨b.repr.symm f, b.repr.injective ?_⟩
    ext i
    have hi : ExteriorAlgebra.ι ℂ u * b.repr m i = 0 := by
      have hi := congrArg (fun t => b.repr t i) hm
      simpa using hi
    have hc := CliffordAlgebra.contractLeft_ι_mul (Q := (0 : QuadraticForm ℂ U)) φ u (b.repr m i)
    rw [hi, map_zero, hφ, one_smul] at hc
    have he : ExteriorAlgebra.ι ℂ u * c (b.repr m i) = b.repr m i := (sub_eq_zero.mp hc.symm).symm
    simpa [f, Finsupp.mapRange_apply] using he
  · rintro ⟨n,rfl⟩
    rw [smul_smul,ExteriorAlgebra.ι_sq_zero,zero_smul]

private theorem projection_obstruction (q y : ExteriorAlgebra ℂ U) (u : U)
    (φ : U →ₗ[ℂ] ℂ) (hφ : φ u = 1)
    (π : ExteriorAlgebra ℂ U →ₐ[ℂ] ExteriorAlgebra ℂ U)
    (hql : π (q * ExteriorAlgebra.ι ℂ u) = 0) (hqy : π (q * y) ≠ 0) :
    ¬ ∃ x : ExteriorAlgebra ℂ U, q*x=0 ∧ ExteriorAlgebra.ι ℂ u*x=ExteriorAlgebra.ι ℂ u*y := by
  rintro ⟨x,hx,hxy⟩
  have hz : ExteriorAlgebra.ι ℂ u*(x-y)=0 := by rw [mul_sub,hxy,sub_self]
  have hc := CliffordAlgebra.contractLeft_ι_mul (Q := (0 : QuadraticForm ℂ U)) φ u (x-y)
  rw [hz,map_zero,hφ,one_smul] at hc
  have he : x-y = ExteriorAlgebra.ι ℂ u*CliffordAlgebra.contractLeft φ (x-y) := sub_eq_zero.mp hc.symm
  have hp := congrArg π (congrArg (q*·) he)
  rw [mul_sub,hx,zero_sub,←mul_assoc,map_neg, map_mul π (q*ExteriorAlgebra.ι ℂ u), hql,zero_mul] at hp
  exact hqy (neg_eq_zero.mp hp)
private theorem matrix_power_hom (n : ℕ) (i j : Fin 4) :
    (A^n) i j ∈ ExteriorAlgebra.exteriorPower ℂ n V := by
  induction n generalizing i j with
  | zero =>
    by_cases h : i=j
    · simp only [pow_zero,Matrix.one_apply,if_pos h]
      exact Submodule.algebraMap_mem (R := ℂ) 1
    · simp only [pow_zero,Matrix.one_apply,if_neg h]
      exact Submodule.zero_mem _
  | succ n ih =>
    rw [pow_succ,Matrix.mul_apply]
    apply Submodule.sum_mem
    intro k hk
    change _ ∈ LinearMap.range (ExteriorAlgebra.ι ℂ : V →ₗ[ℂ] E) ^ (n+1)
    rw [pow_succ]
    exact Submodule.mul_mem_mul (ih i k) (LinearMap.mem_range_self _ _)
private theorem Q_hom : Q ∈ ExteriorAlgebra.exteriorPower ℂ 5 V := by
  change Matrix.trace (A^5) ∈ _
  rw [Matrix.trace]
  exact Submodule.sum_mem _ (fun i _ => matrix_power_hom 5 i i)
private theorem Q_sq : Q*Q=0 := odd_square Q Q_hom
/-- The span of all four traceless diagonal creators. -/
def H : Submodule ℂ V := Submodule.span ℂ (Set.range (fun i : Fin 4 => creatorVec i i))
abbrev R := ExteriorAlgebra ℂ H
/-- The exterior algebra map induced by the diagonal inclusion. -/
def actionMap : R →ₐ[ℂ] E := ExteriorAlgebra.map H.subtype
instance : Module R E := actionMap.toRingHom.toModule
/-- Right multiplication by the source's differential element. -/
def dR : E →ₗ[R] E where
  toFun x := x*Q
  map_add' x y := add_mul x y Q
  map_smul' r x := mul_assoc (actionMap r) x Q
/-- The cycles of the degree-five traceless complex. -/
def Cycles : Submodule R E := LinearMap.ker dR
/-- The square-zero differential with its codomain restricted to cycles. -/
def dToCycle : E →ₗ[R] Cycles := dR.codRestrict Cycles (fun x => by
  change (x*Q)*Q=0
  rw [mul_assoc,Q_sq,mul_zero])
/-- The cohomology of the traceless complex, carrying the diagonal action. -/
def B0 := Cycles ⧸ LinearMap.range dToCycle
instance : AddCommGroup B0 := inferInstanceAs (AddCommGroup (Cycles ⧸ LinearMap.range dToCycle))
instance : Module R B0 := inferInstanceAs (Module R (Cycles ⧸ LinearMap.range dToCycle))
/-- Freeness of the source cohomology over the diagonal exterior algebra. -/
def claim : Prop := Module.Free R B0
private theorem right_left (x : E) : x*Q = -CliffordAlgebra.involute (Q*x) := by
  have ht := odd_involute Q_hom
  rw [map_mul,ht,neg_mul,neg_neg]
  exact odd_comm Q Q_hom x
private theorem cycle_left (x : E) : x*Q=0 ↔ Q*x=0 := by
  rw [right_left,neg_eq_zero]
  exact (map_eq_zero_iff _ CliffordAlgebra.involute_involutive.injective)
private theorem range_left (x : E) : (∃ t : E, t*Q=x) ↔ ∃ t : E, Q*t=x := by
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨CliffordAlgebra.involute t,(odd_comm Q Q_hom t).symm⟩
  · rintro ⟨t,rfl⟩
    exact ⟨CliffordAlgebra.involute t,by rw [odd_comm Q Q_hom,CliffordAlgebra.involute_involute]⟩
private theorem degree_four_boundary (t : E) :
    GradedAlgebra.proj (fun i : ℕ => ⋀[ℂ]^i V) 4 (t*Q)=0 := by
  obtain ⟨u,hu⟩ := (range_left (t*Q)).mp ⟨t,rfl⟩
  rw [←hu]
  exact DirectSum.coe_decompose_mul_of_left_mem_of_not_le
    (fun i : ℕ => ⋀[ℂ]^i V) Q_hom (by decide)
private theorem free_lift (u : H) (hu : u ≠ 0) (z : E)
    (hz : z ∈ ⋀[ℂ]^4 V) (hcycle : z * Q = 0)
    (hkill : ExteriorAlgebra.ι ℂ (u : V) * z = 0) (hfree : claim) :
    ∃ x : ⋀[ℂ]^3 V, Q*(x:E)=0 ∧ ExteriorAlgebra.ι ℂ (u:V)*(x:E)=z := by
  let : Module.Free R B0 := hfree
  let zc : Cycles := ⟨z,hcycle⟩
  let cls : B0 := Submodule.Quotient.mk zc
  have hk : ExteriorAlgebra.ι ℂ u • cls = 0 := by
    change Submodule.Quotient.mk (ExteriorAlgebra.ι ℂ u • zc) = 0
    have he : ExteriorAlgebra.ι ℂ u • zc = 0 := by
      apply Subtype.ext
      change actionMap (ExteriorAlgebra.ι ℂ u)*z=0
      rw [actionMap,ExteriorAlgebra.map_apply_ι]
      exact hkill
    rw [he,Submodule.Quotient.mk_zero]
  obtain ⟨c,hc⟩ := (free_creator_exact u hu cls).mp hk
  obtain ⟨xc,hxc⟩ := Submodule.Quotient.mk_surjective (LinearMap.range dToCycle) c
  rw [←hxc] at hc
  change Submodule.Quotient.mk (ExteriorAlgebra.ι ℂ u • xc) = Submodule.Quotient.mk zc at hc
  obtain ⟨t,ht⟩ := (LinearMap.mem_range.mp ((Submodule.Quotient.eq _).mp hc))
  have he : ExteriorAlgebra.ι ℂ (u:V)*xc.val-z=t*Q := by
    have he := congrArg Subtype.val ht
    change t*Q = actionMap (ExteriorAlgebra.ι ℂ u)*xc.val-z at he
    rw [actionMap,ExteriorAlgebra.map_apply_ι] at he
    exact he.symm
  let x3 : ⋀[ℂ]^3 V := DirectSum.decompose (fun i : ℕ => ⋀[ℂ]^i V) xc.val 3
  let x : E := x3
  have hul : ExteriorAlgebra.ι ℂ (u:V) ∈ ⋀[ℂ]^1 V := by
    simpa only [ExteriorAlgebra.exteriorPower,pow_one] using LinearMap.mem_range_self (ExteriorAlgebra.ι ℂ) (u:V)
  have hel : ExteriorAlgebra.ι ℂ (u:V)*x=z := by
    have hp := congrArg (GradedAlgebra.proj (fun i : ℕ => ⋀[ℂ]^i V) 4) he
    rw [map_sub,degree_four_boundary] at hp
    have hpz : GradedAlgebra.proj (fun i : ℕ => ⋀[ℂ]^i V) 4 z=z :=
      DirectSum.decompose_of_mem_same (fun i : ℕ => ⋀[ℂ]^i V) hz
    have hpl : GradedAlgebra.proj (fun i : ℕ => ⋀[ℂ]^i V) 4
        (ExteriorAlgebra.ι ℂ (u:V)*xc.val)=ExteriorAlgebra.ι ℂ (u:V)*x :=
      DirectSum.coe_decompose_mul_add_of_left_mem
        (fun i : ℕ => ⋀[ℂ]^i V) (i := 1) (j := 3) hul
    rw [hpz,hpl] at hp
    exact sub_eq_zero.mp hp
  refine ⟨x3,?_,hel⟩
  have hcq : Q*xc.val=0 := (cycle_left xc.val).mp xc.property
  have hp := congrArg (GradedAlgebra.proj (fun i : ℕ => ⋀[ℂ]^i V) 8) hcq
  rw [map_zero] at hp
  exact (DirectSum.coe_decompose_mul_add_of_left_mem
    (fun i : ℕ => ⋀[ℂ]^i V) (i := 5) (j := 3) Q_hom).symm.trans hp
private theorem eval_hom (p : Poly) (n : ℕ)
    (hp : ∀ t ∈ p, weight 15 t.1.val = n) : eval p ∈ ⋀[ℂ]^n V := by
  induction p with
  | nil => exact Submodule.zero_mem _
  | cons t p ih =>
    rw [eval_cons]
    apply Submodule.add_mem
    · apply Submodule.smul_mem
      rw [←hp t (by simp only [List.mem_cons, true_or])]
      exact word_hom 15 basisSeq t.1.val
    · exact ih (fun t ht => hp t (List.mem_cons_of_mem _ ht))
private def ellH : H := ⟨creatorVec 0 0+creatorVec 1 1,
  Submodule.add_mem _ (Submodule.subset_span ⟨0,rfl⟩) (Submodule.subset_span ⟨1,rfl⟩)⟩
private theorem ellH_coords : (ellH : V)=coordBasis 0+coordBasis 1 := by
  simp only [ellH.eq_1,coordBasis_eq,ij.eq_1,Matrix.cons_val_zero,Matrix.cons_val_one]
private def φ : V →ₗ[ℂ] ℂ := coordBasis.coord 0
private theorem φ_ell : φ (ellH : V)=1 := by
  rw [ellH_coords]
  simp [φ.eq_1,Module.Basis.coord_apply]
private theorem ellH_ne : ellH≠0 := by
  intro h
  have ht := φ_ell
  rw [h] at ht
  simp at ht
private theorem eval_ell : eval [(1,1),(2,1)] = ExteriorAlgebra.ι ℂ (ellH:V) := by
  rw [ellH_coords,map_add]
  change eval [(singletonMask 0,1),(singletonMask 1,1)] = g 0+g 1
  rw [eval_cons,eval_cons,eval_nil,one_smul,one_smul,mono_singleton,mono_singleton,add_zero]
private def P : V →ₗ[ℂ] V :=
  coordBasis.constr ℂ (fun k => if (5467 : ℕ).testBit k.val then coordBasis k else 0)
private def π : E →ₐ[ℂ] E := ExteriorAlgebra.map P
private def projectData (p : Poly) : Poly := p.filter (fun t => allowed 15 t.1.val 5467)
private theorem mono_projection (s : Mask) :
    π (mono s)=if allowed 15 s.val 5467 then mono s else 0 := by
  apply word_projection 15 basisSeq s.val 5467 π
  intro i hi
  simp only [π.eq_1,ExteriorAlgebra.map_apply_ι,P.eq_1,basisSeq.eq_1,Module.Basis.constr_basis,
    Nat.mod_eq_of_lt hi]
  split_ifs <;> simp only [map_zero]
private theorem eval_projection (p : Poly) : π (eval p)=eval (projectData p) := by
  induction p with
  | nil => exact map_zero _
  | cons t p ih =>
    rw [eval_cons,map_add,map_zsmul,mono_projection]
    change _ = eval (List.filter _ (t::p))
    by_cases ht : allowed 15 t.1.val 5467 = true
    · rw [if_pos ht,List.filter_cons_of_pos (p := fun t : Mask × ℤ => allowed 15 t.1.val 5467) ht,eval_cons,ih]
      rfl
    · rw [if_neg ht,List.filter_cons_of_neg (p := fun t : Mask × ℤ => allowed 15 t.1.val 5467) ht,smul_zero,zero_add,ih]
      rfl


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
-- The three bounded integer certificates share this theorem's elaboration budget.
/-- The traceless cohomology at (p,N)=(5,4) fails diagonal freeness. -/
theorem result : ¬ claim := by
  intro hfree
  let yd : Poly := [(530,-1), (532,1), (648,1), (1104,-1), (1154,1), (1156,1), (4130,-1), (4132,-1), (4360,1), (6160,-1), (8288,-1), (8450,1), (8452,-1), (10368,-1), (16928,1), (17664,1)]
  let ld : Poly := [(1,1),(2,1)]
  let y : E := eval yd
  let ell : E := ExteriorAlgebra.ι ℂ (ellH:V)
  let z : E := ell*y
  have hell : eval ld=ell := eval_ell
  have hy : y ∈ ⋀[ℂ]^3 V := eval_hom yd 3 (by decide)
  have hl : ell ∈ ⋀[ℂ]^1 V := by
    simpa only [ExteriorAlgebra.exteriorPower,pow_one] using
      LinearMap.mem_range_self (ExteriorAlgebra.ι ℂ) (ellH:V)
  have hz : z ∈ ⋀[ℂ]^4 V := SetLike.mul_mem_graded hl hy
  have hqz : Q*z=0 := by
    change Q*(ell*eval yd)=0
    rw [←hell,Q_eq_eval,←eval_mul,←eval_mul]
    have hc : mul (tracePow AData 5) (mul ld yd)=[] := by decide
    rw [hc,eval_nil]
  have hzq : z*Q=0 := (cycle_left z).mpr hqz
  have hlz : ell*z=0 := by
    change ell*(ell*y)=0
    rw [←mul_assoc,ExteriorAlgebra.ι_sq_zero,zero_mul]
  have hql : π (Q*ell)=0 := by
    rw [←hell,Q_eq_eval,←eval_mul,eval_projection]
    have hc : projectData (mul (tracePow AData 5) ld)=[] := by decide
    rw [hc,eval_nil]
  have hqy : π (Q*y)=(-20 : ℤ) • mono 5467 := by
    change π (Q*eval yd)=_
    rw [Q_eq_eval,←eval_mul,eval_projection]
    have hc : projectData (mul (tracePow AData 5) yd)=[(5467,-20)] := by decide
    rw [hc,eval_cons,eval_nil,add_zero]
  have hm : mono 5467 = coordBasis.ExteriorAlgebra {0,1,3,4,6,8,10,12} := by
    let c : ({0,1,3,4,6,8,10,12} : Finset (Fin 15)).card=8 := by decide
    have he : (({0,1,3,4,6,8,10,12} : Finset (Fin 15)).orderEmbOfFin c : Fin 8 → Fin 15) =
        ![0,1,3,4,6,8,10,12] :=
      (Finset.orderEmbOfFin_unique c (by decide) (by decide)).symm
    change word 15 basisSeq 5467=_
    rw [ExteriorAlgebra.basis_apply_ofCard coordBasis c, ExteriorAlgebra.ιMulti_family,
      Set.powersetCard.ofFinEmbEquiv_symm_apply]
    change _ = ExteriorAlgebra.ιMulti ℂ 8 (coordBasis ∘ (Finset.orderEmbOfFin _ c))
    rw [he,ExteriorAlgebra.ιMulti_apply]
    rfl
  have hmn : mono 5467≠0 := by rw [hm]; exact coordBasis.ExteriorAlgebra.ne_zero _
  have hqyn : π (Q*y)≠0 := by
    rw [hqy,←Int.cast_smul_eq_zsmul ℂ]
    exact smul_ne_zero (by norm_num) hmn
  obtain ⟨x,hx,hxl⟩ := free_lift ellH ellH_ne z hz hzq hlz hfree
  exact projection_obstruction Q y (ellH:V) φ φ_ell π hql hqyn ⟨x,hx,hxl⟩

end D5.S3.Quantum.Fermionic.TierzTracelessFreenessRefutation
