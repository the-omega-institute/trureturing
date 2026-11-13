/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact scanner fibres for literal seven-column complementary-pair arrays. -/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip

/-! Pair labels retain the scanner transition and the multiplicity of individual colours. -/

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge

open HardinA233175PairStrip (Seen allowed advance good finish)
open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)
open HardinA233251TriangleStrip (widthNormal widthV widthStep widthTotal)

def labelAdvance (s : Seen) (q : Fin 3) : Seen :=
  (s.1 || decide (q = 1), s.2 || decide (q = 2))

def labelWeight (s : Seen) (q : Fin 3) : ℤ :=
  if q = 0 then 2 else if q = 1 then (if s.1 then 2 else 1)
  else if s.1 then (if s.2 then 2 else 1) else 0

def rowFinish : {k : ℕ} → Seen → (Fin k → Fin 3) → Seen
  | 0, s, _ => s
  | _ + 1, s, q => rowFinish (labelAdvance s (q 0)) (Fin.tail q)

def rowWeight : {k : ℕ} → Seen → (Fin k → Fin 3) → ℤ
  | 0, _, _ => 1
  | _ + 1, s, q => labelWeight s (q 0) * rowWeight (labelAdvance s (q 0)) (Fin.tail q)

private theorem head_fibres (s : Seen) (H : Seen → Fin 3 → ℤ) :
    (∑ x : Fin 6, if allowed s x then H (advance s x) (beta x) else 0) =
      ∑ q : Fin 3, labelWeight s q * H (labelAdvance s q) q := by
  rcases s with ⟨a, b⟩
  cases a <;> cases b <;>
    simp [Fin.sum_univ_succ, allowed, advance, beta, labelWeight, labelAdvance] <;> ring

private theorem beta_cons {k : ℕ} (x : Fin 6) (c : Fin k → Fin 6) :
    (fun j : Fin (k + 1) => beta ((Fin.cons x c : Fin (k + 1) → Fin 6) j)) =
      Fin.cons (beta x) (fun j => beta (c j)) := by
  exact Fin.comp_cons beta x c

/-- Exact weighted pushforward of the original scanner, for every word length and readout. -/
theorem scanner_fibres (k : ℕ) (s : Seen) (H : Seen → (Fin k → Fin 3) → ℤ) :
    (∑ c : Fin k → Fin 6, if good s c then H (finish s c) (fun j => beta (c j)) else 0) =
      ∑ q : Fin k → Fin 3, rowWeight s q * H (rowFinish s q) q := by
  induction k generalizing s with
  | zero =>
    simp [good, finish, rowWeight, rowFinish]
    congr 1
    funext j
    exact Fin.elim0 j
  | succ k ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Fin 6)).sum_comp,
      Fintype.sum_prod_type]
    change (∑ x : Fin 6, ∑ c : Fin k → Fin 6,
      if good s (Fin.cons x c) then H (finish s (Fin.cons x c))
        (fun j => beta ((Fin.cons x c : Fin (k + 1) → Fin 6) j)) else 0) = _
    simp only [good, finish, Fin.cons_zero, Fin.tail_cons, beta_cons]
    change (∑ x : Fin 6, ∑ c : Fin k → Fin 6,
      if allowed s x ∧ good (advance s x) c then
        H (finish (advance s x) c) (Fin.cons (beta x) (fun j => beta (c j))) else 0) = _
    have hx (x : Fin 6) :
        (∑ c : Fin k → Fin 6, if allowed s x ∧ good (advance s x) c then
          H (finish (advance s x) c) (Fin.cons (beta x) (fun j => beta (c j))) else 0) =
        ∑ q : Fin k → Fin 3, if allowed s x then
          rowWeight (advance s x) q *
            H (rowFinish (advance s x) q) (Fin.cons (beta x) q) else 0 := by
      by_cases h : allowed s x
      · simpa only [h, true_and, ite_true] using
          ih (advance s x) (fun t q => H t (Fin.cons (beta x) q))
      · simp [h]
    simp_rw [hx]
    rw [Finset.sum_comm]
    have hhead (q : Fin k → Fin 3) := head_fibres s
      (fun t a => rowWeight t q * H (rowFinish t q) (Fin.cons a q))
    simp_rw [hhead]
    rw [Finset.sum_comm,
      ← (Fin.consEquiv (fun _ : Fin (k + 1) => Fin 3)).sum_comp,
      Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro qs _
    change labelWeight s q *
      (rowWeight (labelAdvance s q) qs * H (rowFinish (labelAdvance s q) qs) (Fin.cons q qs)) =
      rowWeight s (Fin.cons q qs) * H (rowFinish s (Fin.cons q qs)) (Fin.cons q qs)
    simp only [rowWeight, rowFinish, Fin.cons_zero, Fin.tail_cons, mul_assoc]

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge
