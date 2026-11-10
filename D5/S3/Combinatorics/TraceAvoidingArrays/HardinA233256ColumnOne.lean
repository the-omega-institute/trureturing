/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233256ColumnOne
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233256ColumnOne
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233256ColumnOne.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233256ColumnOne.finite_certificate
   digest: The literal one-column normalized count satisfies Hardin's cubic recurrence. -/
/-
admission_basis: open-problem-resolution (#28883; Proved)
escape_witness: none
-/
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
import Mathlib.Tactic

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233256ColumnOne
open HardinA233251TriangleStrip
open HardinA233175PairStrip (Seen)

def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin n × Fin 1 → Fin 6 =>
    widthLegal (fun _ => True) (fun _ _ => True) A)).card

private abbrev R : (Fin 1 → Fin 6) → Prop := fun _ => True
private abbrev P : (Fin 1 → Fin 6) → Unit := fun _ => ()
private abbrev C : Unit → (Fin 1 → Fin 6) → Prop := fun _ _ => True
private abbrev v := widthV R P C
private abbrev total := widthTotal R P

private theorem counting_bridge (n : ℕ) : (a (n + 1) : ℤ) = total (v n) :=
  width_counting_bridge R P C (fun _ _ => True) (fun _ _ => Iff.rfl) n

private theorem step_linear (u w z : Seen → Unit → ℤ) (s : Seen) (p : Unit) :
    widthStep R P C (fun s p => 12 * u s p - 44 * w s p + 48 * z s p) s p =
      12 * widthStep R P C u s p - 44 * widthStep R P C w s p +
        48 * widthStep R P C z s p := by
  unfold widthStep
  simp_rw [ite_add, ite_sub, ← mul_ite, mul_zero]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.mul_sum]

set_option maxRecDepth 100000 in
private theorem vector_certificate : ∀ s : Seen, ∀ p : Unit,
    v 3 s p = 12 * v 2 s p - 44 * v 1 s p + 48 * v 0 s p := by
  decide +kernel

private theorem vector_recurrence (n : ℕ) : ∀ s p,
    v (n + 3) s p = 12 * v (n + 2) s p - 44 * v (n + 1) s p + 48 * v n s p := by
  induction n with
  | zero => exact vector_certificate
  | succ n ih =>
    intro s p
    change widthStep R P C (v (n + 3)) s p =
      12 * widthStep R P C (v (n + 2)) s p -
        44 * widthStep R P C (v (n + 1)) s p + 48 * widthStep R P C (v n) s p
    rw [show v (n + 3) = (fun s p =>
      12 * v (n + 2) s p - 44 * v (n + 1) s p + 48 * v n s p) from
        funext (fun s => funext (ih s))]
    exact step_linear _ _ _ s p

private theorem recurrence (n : ℕ) :
    (a (n + 4) : ℤ) = 12 * a (n + 3) - 44 * a (n + 2) + 48 * a (n + 1) := by
  rw [show n + 4 = (n + 3) + 1 by omega, counting_bridge,
    show n + 3 = (n + 2) + 1 by omega, counting_bridge,
    show n + 2 = (n + 1) + 1 by omega, counting_bridge, counting_bridge]
  unfold total widthTotal
  simp_rw [vector_recurrence]
  simp_rw [ite_add, ite_sub, ← mul_ite, mul_zero]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.mul_sum]

theorem finite_certificate : a 1 = 1 ∧ a 2 = 3 ∧ a 3 = 11 ∧ a 4 = 48 := by
  have h (n : ℕ) := counting_bridge n
  have h0 : total (v 0) = 1 := by decide +kernel
  have h1 : total (v 1) = 3 := by decide +kernel
  have h2 : total (v 2) = 11 := by decide +kernel
  have h3 : total (v 3) = 48 := by decide +kernel
  have := h 0
  have := h 1
  have := h 2
  have := h 3
  omega

theorem result :
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) =
      12 * a (n - 1) - 44 * a (n - 2) + 48 * a (n - 3)) ∧
    (a 1 = 1 ∧ a 2 = 3 ∧ a 3 = 11 ∧ a 4 = 48) := by
  refine ⟨?_, finite_certificate⟩
  intro n hn
  have h := recurrence (n - 4)
  convert h using 1 <;> congr 1 <;> omega

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233256ColumnOne
