/- GID: D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact bond-defect counts reduce to finite transfers with arbitrary boundary quotients. -/

/-
admission_basis: escape-witness
escape_witness: continuation_count for lumped_count: arbitrary-length suffixes counted at exact
budget by structural induction; live path continuation_count -> counting_bridge -> lumped_count.
Row: proof_shape=bind-only; consumers=bondDefects, literalCount
bondDefects: proof_shape=bind-only; consumers=defects, lumped_count
tailDefects: proof_shape=bind-only; consumers=defects, counting_bridge
defects: proof_shape=bind-only; consumers=literalCount, relabel_defects
literalCount: proof_shape=bind-only; consumers=lumped_count
tail_relabel: proof_shape=bind-only; consumers=relabel_defects
relabel_defects: proof_shape=bind-only; consumers=HardinA229580Strip.scale_count, HardinA229581Strip.scale_count, HardinA229582Strip.scale_count, HardinA229583Strip.scale_count, HardinA229584Strip.scale_count
constant_tail: proof_shape=bind-only; consumers=constant_defects
constant_defects: proof_shape=bind-only; consumers=HardinA229580Strip.scale_count, HardinA229581Strip.scale_count, HardinA229582Strip.scale_count, HardinA229583Strip.scale_count, HardinA229584Strip.scale_count
continuation: proof_shape=bind-only; consumers=lumped_count
projectedCost: proof_shape=bind-only; consumers=continuation_count, counting_bridge
cost_eq: proof_shape=bind-only; consumers=counting_bridge
continuation_count: proof_shape=content; consumers=counting_bridge
counting_bridge: proof_shape=content; consumers=lumped_count
continuation_matrix: proof_shape=bind-only; consumers=lumped_count
lumped_count: proof_shape=content; consumers=HardinA229580Strip.count_transfer, HardinA229581Strip.count_transfer, HardinA229582Strip.count_transfer, HardinA229583Strip.count_transfer, HardinA229584Strip.count_transfer
forward: proof_shape=bind-only; consumers=HardinA229580Strip.powers_table, HardinA229581Strip.powers_table, HardinA229582Strip.powers_table, HardinA229583Strip.powers_table, HardinA229584Strip.powers_table, forward_eq, forward_shift
forward_eq: proof_shape=bind-only; consumers=forward_shift, HardinA229583Strip.result, HardinA229584Strip.result
forward_shift: proof_shape=bind-only; consumers=HardinA229580Strip.result, HardinA229581Strip.result, HardinA229582Strip.result, HardinA229583Strip.result, HardinA229584Strip.result
-/

import Mathlib.LinearAlgebra.Matrix.Action
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-! Additive defect budgets and finite boundary transfers. -/

open scoped BigOperators

namespace D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer

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

private theorem tail_relabel {q k : ℕ} (H V : Finset (Fin k × Fin k))
    (e : Equiv.Perm (Fin q)) (r : Row q k) (rs : List (Row q k)) :
    tailDefects H V (e ∘ r) (rs.map fun t => e ∘ t) = tailDefects H V r rs := by
  induction rs generalizing r with
  | nil => rfl
  | cons t ts ih => simp [tailDefects, bondDefects, e.injective.eq_iff, ih]

theorem relabel_defects {q k : ℕ} (H V : Finset (Fin k × Fin k))
    (e : Equiv.Perm (Fin q)) (rs : List (Row q k)) :
    defects H V (rs.map fun r => e ∘ r) = defects H V rs := by
  cases rs with
  | nil => rfl
  | cons r rs => simp [defects, bondDefects, e.injective.eq_iff, tail_relabel]

private theorem constant_tail {q k : ℕ} (H V : Finset (Fin k × Fin k)) (c : Fin q) (n : ℕ) :
    tailDefects H V (fun _ => c) (List.replicate n (fun _ => c)) = n * (V.card + H.card) := by
  induction n with
  | zero => simp [tailDefects]
  | succ n ih => simp [List.replicate_succ, tailDefects, bondDefects, ih, Nat.succ_mul]; omega

theorem constant_defects {q k : ℕ} (H V : Finset (Fin k × Fin k)) (c : Fin q) (n : ℕ) :
    defects H V (List.replicate (n + 1) (fun _ => c)) = H.card + n * (V.card + H.card) := by
  simp [List.replicate_succ, defects, bondDefects, constant_tail]

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
    · rw [ite_eq_left h, ← ih]
      apply Finset.sum_congr rfl
      intro f _
      change (if C p r + bondDefects H r r + projectedCost H P C (P r) (List.ofFn f) = d
        then (1 : ℤ) else 0) = _
      congr 1
      apply propext
      omega
    · rw [ite_eq_right h]
      apply Finset.sum_eq_zero
      intro f _
      exact ite_eq_right (by omega)

private theorem counting_bridge
    (edge : ∀ r t, bondDefects V r t = C (P r) t) (D n : ℕ) :
    (literalCount (q := q) H V D (n + 1) : ℤ) =
      ∑ r : Row q k, if bondDefects H r r ≤ D then
        continuation H P C n (P r) (D - bondDefects H r r) else 0 := by
  rw [literalCount, Finset.natCast_card_filter]
  let e : (Fin (n + 1) × Fin k → Fin q) ≃ (Fin (n + 1) → Row q k) :=
    Equiv.curry (Fin (n + 1)) (Fin k) (Fin q)
  rw [← e.symm.sum_comp,
    ← (Fin.consEquiv (fun _ : Fin (n + 1) => Row q k)).sum_comp,
    Fintype.sum_prod_type]
  change (∑ r : Row q k, ∑ f : Fin n → Row q k,
    if defects H V (List.ofFn (Fin.cons r f)) = D then (1 : ℤ) else 0) = _
  simp only [List.ofFn_succ, Fin.cons_zero, Fin.tail_cons, defects, cost_eq H V P C edge]
  apply Finset.sum_congr rfl
  intro r _
  by_cases h : bondDefects H r r ≤ D
  · rw [ite_eq_left h, ← continuation_count]
    apply Finset.sum_congr rfl
    intro f _
    change (if bondDefects H r r + projectedCost H P C (P r) (List.ofFn f) = D
      then (1 : ℤ) else 0) = _
    congr 1
    apply propext
    omega
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro f _
    exact ite_eq_right (by omega)

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
    · rw [ite_eq_left hr, ih _ _ (hnext p d hpd r hr)]
      simp [hr, Matrix.mulVec, dotProduct]
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
    (literalCount (q := q) H V D (n + 1) : ℤ) = dotProduct v ((T ^ n).mulVec e) := by
  rw [counting_bridge H V P C edge]
  unfold dotProduct
  simp_rw [← hv, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : bondDefects H r r ≤ D
  · rw [ite_eq_left hr, continuation_matrix H P C Valid cl T e hzero hnext hT n _ _ (hinit r hr)]
    simp [hr]
  · simp [hr]

end Transfer

section Recurrence

variable {S : Type*} [Fintype S] [DecidableEq S]

def forward (T : Matrix S S ℤ) (v : S → ℤ) (n : ℕ) : S → ℤ :=
  Nat.iterate (fun w => Matrix.vecMul w T) n v

theorem forward_eq (T : Matrix S S ℤ) (v : S → ℤ) (n : ℕ) :
    forward T v n = Matrix.vecMul v (T ^ n) := by
  simpa only [forward, Matrix.op_smul_eq_vecMul, MulOpposite.unop_pow,
    MulOpposite.unop_op] using (smul_iterate_apply (MulOpposite.op T) n v)

theorem forward_shift (T : Matrix S S ℤ) (v e : S → ℤ) (d b : ℕ) (c : Fin d → ℤ)
    (h : forward T v (b + d) = ∑ j : Fin d, c j • forward T v (b + j.val)) (n : ℕ) :
    dotProduct v ((T ^ (n + b + d)).mulVec e) =
      ∑ j : Fin d, c j * dotProduct v ((T ^ (n + b + j.val)).mulVec e) := by
  have hh := congrArg (fun w => dotProduct w ((T ^ n).mulVec e)) h
  simp only [sum_dotProduct, smul_dotProduct, smul_eq_mul, forward_eq,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← pow_add] at hh
  simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hh

end Recurrence

end D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
