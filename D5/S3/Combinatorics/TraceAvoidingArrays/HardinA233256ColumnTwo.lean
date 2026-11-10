/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233256ColumnTwo
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233256ColumnTwo
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233256ColumnTwo.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233256ColumnTwo.finite_certificate
   digest: Hardin's second-order recurrence for literal two-column pair-exclusion arrays. -/
/-
admission_basis: open-problem-resolution (#28883; Proved)
escape_witness: none
All declarations are bind-only under the registered external resolution basis.
R: proof_shape=bind-only; consumers=instDecidableR, a, v, total, counting_bridge, valid_next, initial_valid, recurrence
E: proof_shape=bind-only; consumers=instDecidableE, a, counting_bridge
instDecidableR: proof_shape=bind-only; consumers=a, v, total
instDecidableE: proof_shape=bind-only; consumers=a, counting_bridge
a: proof_shape=bind-only; consumers=counting_bridge, finite_certificate, result
P: proof_shape=bind-only; consumers=v, total, valid_next, initial_valid
C: proof_shape=bind-only; consumers=instDecidableC, v, valid_next
instDecidableC: proof_shape=bind-only; consumers=v
v: proof_shape=bind-only; consumers=counting_bridge, vector_certificate, vector_recurrence, recurrence, finite_certificate
total: proof_shape=bind-only; consumers=counting_bridge, recurrence, finite_certificate
counting_bridge: proof_shape=bind-only; consumers=recurrence, finite_certificate
Valid: proof_shape=bind-only; consumers=instDecidableValid, valid_next, initial_valid, vector_certificate, vector_recurrence
instDecidableValid: proof_shape=bind-only; consumers=vector_certificate
valid_next: proof_shape=bind-only; consumers=vector_recurrence
initial_valid: proof_shape=bind-only; consumers=recurrence
vector_certificate: proof_shape=bind-only; consumers=vector_recurrence
vector_recurrence: proof_shape=bind-only; consumers=recurrence
recurrence: proof_shape=bind-only; consumers=result
finite_certificate: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=external result of #28883
-/
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
import D5.S3.Observer.Separation.BooleanRankThreeK4
import Mathlib.Tactic

/-! Two-column arrays form a path in row-major order. -/
open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233256ColumnTwo
open HardinA233251TriangleStrip
open HardinA233175PairStrip (Seen good finish)
open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)

private def R (c : Fin 2 → Fin 6) : Prop := c 0 ≠ c 1 ∧ (c 0).val + (c 1).val ≠ 5
private def E (c d : Fin 2 → Fin 6) : Prop := c 1 ≠ d 0 ∧ (c 1).val + (d 0).val ≠ 5
private instance instDecidableR (c : Fin 2 → Fin 6) : Decidable (R c) :=
  inferInstanceAs (Decidable (_ ∧ _))
private instance instDecidableE (c d : Fin 2 → Fin 6) : Decidable (E c d) :=
  inferInstanceAs (Decidable (_ ∧ _))

def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin n × Fin 2 → Fin 6 => widthLegal R E A)).card

attribute [local irreducible] a

private abbrev P (c : Fin 2 → Fin 6) : Fin 3 := beta (c 1)
private def C (p : Fin 3) (c : Fin 2 → Fin 6) : Prop := p ≠ beta (c 0)
private instance instDecidableC (p : Fin 3) (c : Fin 2 → Fin 6) : Decidable (C p c) :=
  inferInstanceAs (Decidable (_ ≠ _))
private abbrev v := widthV R P C
private abbrev total := widthTotal R P

private theorem counting_bridge (n : ℕ) : (a (n + 1) : ℤ) = total (v n) := by
  unfold a
  exact width_counting_bridge R P C E (fun c d => colour_bond_iff (c 1) (d 0)) n

private def Valid (s : Seen) (p : Fin 3) : Prop :=
  s.1 = true ∧ (s.2 = false → p ≠ 2)
private instance instDecidableValid (s : Seen) (p : Fin 3) : Decidable (Valid s p) :=
  inferInstanceAs (Decidable (_ ∧ (_ → _)))

private theorem valid_next : ∀ s p c, Valid s p → R c ∧ C p c ∧ good s c →
    Valid (finish s c) (P c) := by decide +kernel
private theorem initial_valid : ∀ c : Fin 2 → Fin 6,
    c 0 = 0 ∧ R c ∧ good (false, false) c → Valid (finish (false, false) c) (P c) := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem vector_certificate : ∀ s p, Valid s p →
    v 2 s p = 20 * v 1 s p - 64 * v 0 s p := by decide +kernel

private theorem vector_recurrence (n : ℕ) : ∀ s p, Valid s p →
    v (n + 2) s p = 20 * v (n + 1) s p - 64 * v n s p := by
  induction n with
  | zero => exact vector_certificate
  | succ n ih =>
    intro s p hv
    change widthStep R P C (v (n + 2)) s p =
      20 * widthStep R P C (v (n + 1)) s p - 64 * widthStep R P C (v n) s p
    unfold widthStep
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro c _
    by_cases h : R c ∧ C p c ∧ good s c
    · simp only [h, ite_true]
      exact ih _ _ (valid_next s p c hv h)
    · simp only [if_neg h, mul_zero, sub_self, zero_add]

private theorem recurrence (n : ℕ) :
    (a (n + 3) : ℤ) = 20 * a (n + 2) - 64 * a (n + 1) := by
  rw [show n + 3 = (n + 2) + 1 by omega, counting_bridge,
    show n + 2 = (n + 1) + 1 by omega, counting_bridge, counting_bridge]
  unfold total widthTotal
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _
  by_cases h : c 0 = 0 ∧ R c ∧ good (false, false) c
  · simp only [h, ite_true]
    exact vector_recurrence n _ _ (initial_valid c h)
  · simp only [if_neg h, mul_zero, sub_self, zero_add]

theorem finite_certificate : (a 1 : ℤ) = 1 ∧ (a 2 : ℤ) = 10 ∧ (a 3 : ℤ) = 136 := by
  have h0 : total (v 0) = 1 := by decide +kernel
  have h1 : total (v 1) = 10 := by decide +kernel
  have h2 : total (v 2) = 136 := by decide +kernel
  refine ⟨?_, ?_, ?_⟩
  · exact (counting_bridge 0).trans h0
  · exact (counting_bridge 1).trans h1
  · exact (counting_bridge 2).trans h2

theorem result :
    (∀ n : ℕ, 3 ≤ n → (a n : ℤ) = 20 * a (n - 1) - 64 * a (n - 2)) ∧
    ((a 1 : ℤ) = 1 ∧ (a 2 : ℤ) = 10 ∧ (a 3 : ℤ) = 136) := by
  refine ⟨?_, finite_certificate⟩
  intro n hn
  have h := recurrence (n - 3)
  simpa only [show n - 3 + 3 = n by omega,
    show n - 3 + 2 = n - 1 by omega,
    show n - 3 + 1 = n - 2 by omega] using h

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233256ColumnTwo
