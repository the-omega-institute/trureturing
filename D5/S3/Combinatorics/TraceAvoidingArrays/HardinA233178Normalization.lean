/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Normalization
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Normalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact symmetrization of first-appearance scanner weights, including missing labels. -/

/-
admission_basis: escape-witness
proof_shape: content: result, weight_one_seen
escape_witness: weight_one_seen (unbounded word induction with an exact absence correction)
The declared result is a scanner identity, not an external-problem settlement.
absent_cons: proof_shape=bind-only; consumers=weight_one_seen, result
absent_swap: proof_shape=bind-only; consumer=result
weight_one_seen: proof_shape=content; consumer=result
result: proof_shape=content; induction using weight_one_seen and the exchanged word
The private auxiliaries are consumed on the result's live proof path.
Direct frozen dependency: HardinA233255LiteralBridge (rowWeight, labelWeight, labelAdvance),
statement_id: sha256:c3e47763a90b55bac6411eb8466c2c6012b56d12223aa67492b98cf0eae92fe3.
HardinA233255ShapeSymmetry.full_row supplies the completed-scanner word weight;
its module statement_id is sha256:1f16e42743d7e7eb40a1e81bd001307758a7555f003094ca2380ab67ff4f29a5.
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry

/-! The exact missing-label correction is uniform over all finite words. -/

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Normalization
open HardinA233255LiteralBridge (rowWeight labelWeight rowFinish labelAdvance)

/-- Exchange the two complementary-pair labels other than the initial pair. -/
def swap : Equiv.Perm (Fin 3) := Equiv.swap 1 2

/-- Absence of one label from the entire word. -/
def absent {k : ℕ} (q : Fin k → Fin 3) (c : Fin 3) : ℤ :=
  if ∀ j, q j ≠ c then 1 else 0

private theorem absent_cons {k : ℕ} (a c : Fin 3) (q : Fin k → Fin 3) :
    absent (Fin.cons a q) c = (if a = c then 0 else absent q c) := by
  simp only [absent, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
  by_cases h : a = c <;> simp [h]

private theorem weight_one_seen (k : ℕ) (q : Fin k → Fin 3) :
    2 * rowWeight (true, false) q = 2^k * (1 + absent q 2) := by
  induction k with
  | zero => norm_num [rowWeight, absent]
  | succ k ih =>
    rw [← Fin.cons_self_tail q]
    simp only [rowWeight, Fin.cons_zero, Fin.tail_cons, absent_cons]
    have h := ih (Fin.tail q)
    have hc := (HardinA233255ShapeSymmetry.full_row k (Fin.tail q)).2
    generalize q 0 = a
    fin_cases a <;> norm_num [labelWeight, labelAdvance] <;>
      rw [pow_succ] <;> nlinarith

private theorem absent_swap {k : ℕ} (q : Fin k → Fin 3) (c : Fin 3) :
    absent (fun j => swap (q j)) c = absent q (swap c) := by
  have he : (∀ j, swap (q j) ≠ c) ↔ ∀ j, q j ≠ swap c := by
    apply forall_congr'
    intro j
    have hc : swap (swap c) = c := Equiv.swap_apply_self 1 2 c
    constructor
    · intro h heq
      exact h (heq ▸ hc)
    · intro h heq
      apply h
      have := congrArg swap heq
      simpa [swap] using this
  simp only [absent, he]

/-- Exact missing-label correction for the two possible orders of first appearance. -/
theorem result (k : ℕ) (q : Fin k → Fin 3) :
    4 * (rowWeight (false, false) q +
      rowWeight (false, false) (fun j => swap (q j))) =
    2^k * (1 + absent q 1 + absent q 2 + 5 * (absent q 1 * absent q 2)) := by
  induction k with
  | zero => norm_num [rowWeight, absent]
  | succ k ih =>
    rw [← Fin.cons_self_tail q]
    have hswap : (fun j => swap ((Fin.cons (q 0) (Fin.tail q) : Fin (k+1) → Fin 3) j)) =
        Fin.cons (swap (q 0)) (fun j => swap (Fin.tail q j)) :=
      Fin.comp_cons swap _ _
    rw [hswap]
    simp only [rowWeight, Fin.cons_zero, Fin.tail_cons, absent_cons]
    have h0 := ih (Fin.tail q)
    have h1 := weight_one_seen k (Fin.tail q)
    have h2 := weight_one_seen k (fun j => swap (Fin.tail q j))
    rw [absent_swap] at h2
    generalize q 0 = a
    fin_cases a <;>
      norm_num [labelWeight, labelAdvance, swap, Equiv.swap_apply_def] at * <;>
      rw [pow_succ] <;> nlinarith

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Normalization
