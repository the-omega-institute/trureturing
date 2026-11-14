/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/DefectTransfer
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/DefectTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact bond-defect counts reduce to finite transfers with arbitrary boundary quotients. -/

/-
admission_basis: escape-witness
escape_witness: counting_bridge, lumped_count
-/

import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

open scoped BigOperators

namespace D5.S3.Combinatorics.TraceAvoidingArrays.DefectTransfer

abbrev Row (q k : ℕ) := Fin k → Fin q

def bondDefects {q k : ℕ} (E : Finset (Fin k × Fin k)) (r t : Row q k) : ℕ :=
  (E.filter fun e => r e.1 = t e.2).card

def tailDefects {q k : ℕ} (H V : Finset (Fin k × Fin k)) : Row q k → List (Row q k) → ℕ
  | _, [] => 0
  | r, t :: ts => bondDefects V r t + bondDefects H t t + tailDefects H V t ts

def defects {q k : ℕ} (H V : Finset (Fin k × Fin k)) : List (Row q k) → ℕ
  | [] => 0
  | r :: rs => bondDefects H r r + tailDefects H V r rs

def literalCount {q k : ℕ} (H V : Finset (Fin k × Fin k)) (D n : ℕ) : ℕ :=
  (Finset.univ.filter fun A : Fin n × Fin k → Fin q =>
    defects H V (List.ofFn fun i j => A (i, j)) = D).card

section Transfer

variable {q k : ℕ} {B : Type*}
variable (H V : Finset (Fin k × Fin k))
variable (P : Row q k → B) (C : B → Row q k → ℕ)

def continuation : ℕ → B → ℕ → ℤ
  | 0, _, d => if d = 0 then 1 else 0
  | n + 1, p, d => ∑ r : Row q k,
      if C p r + bondDefects H r r ≤ d then
        continuation n (P r) (d - (C p r + bondDefects H r r)) else 0

private def projectedCost : B → List (Row q k) → ℕ
  | _, [] => 0
  | p, r :: rs => C p r + bondDefects H r r + projectedCost (P r) rs

private theorem cost_eq
    (edge : ∀ r t, bondDefects V r t = C (P r) t) (r : Row q k) (rs : List (Row q k)) :
    tailDefects H V r rs = projectedCost H P C (P r) rs := by
  induction rs generalizing r with
  | nil => rfl
  | cons t ts ih => simp only [tailDefects, projectedCost, edge, ih]

private theorem continuation_count (n : ℕ) (p : B) (d : ℕ) :
    (∑ f : Fin n → Row q k,
      if projectedCost H P C p (List.ofFn f) = d then (1 : ℤ) else 0) =
      continuation H P C n p d := by
  induction n generalizing p d with
  | zero => simp [List.ofFn_zero, projectedCost, continuation, eq_comm]
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Row q k)).sum_comp,
      Fintype.sum_prod_type]
    change (∑ r : Row q k, ∑ f : Fin n → Row q k,
      if projectedCost H P C p (List.ofFn (Fin.cons r f)) = d then (1 : ℤ) else 0) = _
    simp only [List.ofFn_succ, Fin.cons_zero, Fin.tail_cons, projectedCost]
    rw [continuation]
    apply Finset.sum_congr rfl
    intro r _
    by_cases h : C p r + bondDefects H r r ≤ d
    · rw [if_pos h, ← ih]
      apply Finset.sum_congr rfl
      intro f _
      congr 1
      omega
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro f _
      exact if_neg (by omega)

theorem counting_bridge
    (edge : ∀ r t, bondDefects V r t = C (P r) t) (D n : ℕ) :
    (literalCount H V D (n + 1) : ℤ) =
      ∑ r : Row q k, if bondDefects H r r ≤ D then
        continuation H P C n (P r) (D - bondDefects H r r) else 0 := by
  rw [literalCount, Finset.natCast_card_filter]
  let e : (Fin (n + 1) × Fin k → Fin q) ≃ (Fin (n + 1) → Row q k) :=
    { toFun := fun A i j => A (i, j)
      invFun := fun f p => f p.1 p.2
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← e.symm.sum_comp,
    ← (Fin.consEquiv (fun _ : Fin (n + 1) => Row q k)).sum_comp,
    Fintype.sum_prod_type]
  change (∑ r : Row q k, ∑ f : Fin n → Row q k,
    if defects H V (List.ofFn (Fin.cons r f)) = D then (1 : ℤ) else 0) = _
  simp only [List.ofFn_succ, Fin.cons_zero, Fin.tail_cons, defects, cost_eq H V P C edge]
  apply Finset.sum_congr rfl
  intro r _
  by_cases h : bondDefects H r r ≤ D
  · rw [if_pos h, ← continuation_count]
    apply Finset.sum_congr rfl
    intro f _
    congr 1
    omega
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro f _
    exact if_neg (by omega)

variable {S : Type*} [Fintype S] [DecidableEq S]
variable (Valid : B → ℕ → Prop) (cl : B → ℕ → S)
variable (T : Matrix S S ℤ) (v e : S → ℤ) (D : ℕ)

private theorem continuation_matrix
    (hzero : ∀ p d, Valid p d → e (cl p d) = if d = 0 then 1 else 0)
    (hnext : ∀ p d, Valid p d → ∀ r, C p r + bondDefects H r r ≤ d →
      Valid (P r) (d - (C p r + bondDefects H r r)))
    (hT : ∀ p d, Valid p d → ∀ s,
      (∑ r : Row q k, if C p r + bondDefects H r r ≤ d ∧
        cl (P r) (d - (C p r + bondDefects H r r)) = s then (1 : ℤ) else 0) = T (cl p d) s)
    (n : ℕ) (p : B) (d : ℕ) (hpd : Valid p d) :
    continuation H P C n p d = ((T ^ n).mulVec e) (cl p d) := by
  induction n generalizing p d with
  | zero => simpa only [pow_zero, Matrix.one_mulVec, continuation] using (hzero p d hpd).symm
  | succ n ih =>
    rw [continuation, pow_succ', ← Matrix.mulVec_mulVec]
    unfold Matrix.mulVec dotProduct
    simp_rw [← hT p d hpd, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    by_cases hr : C p r + bondDefects H r r ≤ d
    · rw [if_pos hr, ih _ _ (hnext p d hpd r hr)]
      simp [hr]
    · simp [hr]

theorem lumped_count
    (edge : ∀ r t, bondDefects V r t = C (P r) t)
    (hzero : ∀ p d, Valid p d → e (cl p d) = if d = 0 then 1 else 0)
    (hnext : ∀ p d, Valid p d → ∀ r, C p r + bondDefects H r r ≤ d →
      Valid (P r) (d - (C p r + bondDefects H r r)))
    (hT : ∀ p d, Valid p d → ∀ s,
      (∑ r : Row q k, if C p r + bondDefects H r r ≤ d ∧
        cl (P r) (d - (C p r + bondDefects H r r)) = s then (1 : ℤ) else 0) = T (cl p d) s)
    (hinit : ∀ r, bondDefects H r r ≤ D → Valid (P r) (D - bondDefects H r r))
    (hv : ∀ s, (∑ r : Row q k, if bondDefects H r r ≤ D ∧
      cl (P r) (D - bondDefects H r r) = s then (1 : ℤ) else 0) = v s)
    (n : ℕ) :
    (literalCount H V D (n + 1) : ℤ) = dotProduct v ((T ^ n).mulVec e) := by
  rw [counting_bridge H V P C edge]
  unfold dotProduct
  simp_rw [← hv, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : bondDefects H r r ≤ D
  · rw [if_pos hr, continuation_matrix H P C Valid cl T e hzero hnext hT n _ _ (hinit r hr)]
    simp [hr]
  · simp [hr]

end Transfer

section Recurrence

variable {S : Type*} [Fintype S] [DecidableEq S]

def forward (T : Matrix S S ℤ) (v : S → ℤ) : ℕ → S → ℤ
  | 0 => v
  | n + 1 => Matrix.vecMul (forward T v n) T

private theorem forward_eq (T : Matrix S S ℤ) (v : S → ℤ) (n : ℕ) :
    forward T v n = Matrix.vecMul v (T ^ n) := by
  induction n with
  | zero => simp [forward]
  | succ n ih => simp only [forward, ih, pow_succ, Matrix.vecMul_vecMul]

theorem forward_shift (T : Matrix S S ℤ) (v e : S → ℤ) (d b : ℕ) (c : Fin d → ℤ)
    (h : forward T v (b + d) = ∑ j : Fin d, c j • forward T v (b + j.val)) (n : ℕ) :
    dotProduct v ((T ^ (n + b + d)).mulVec e) =
      ∑ j : Fin d, c j * dotProduct v ((T ^ (n + b + j.val)).mulVec e) := by
  have hh := congrArg (fun w => dotProduct w ((T ^ n).mulVec e)) h
  simp only [sum_dotProduct, smul_dotProduct, smul_eq_mul, forward_eq,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← pow_add] at hh
  convert hh using 1 <;> congr 3 <;> omega

end Recurrence

end D5.S3.Combinatorics.TraceAvoidingArrays.DefectTransfer
