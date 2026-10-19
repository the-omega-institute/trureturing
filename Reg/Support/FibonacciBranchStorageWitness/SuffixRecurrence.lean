import Reg.Support.FibonacciQuadratic

namespace Reg.Support.FibonacciBranchStorageWitness
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open Reg.Support.FibonacciQuadratic
noncomputable section

/-- A linear rational recurrence certifies every suffix of one original word. -/
theorem suffix_table (w : List Label) (values : List (ℚ × ℚ))
    (hlen : values.length = w.length + 1)
    (hstep : List.zipWith step w values.tail = values.take w.length)
    (r : ℕ) (hr : r ≤ w.length) :
    compose (w.drop r) (eval (values[w.length]'(by omega))) =
      eval (values[r]'(by omega)) := by
  induction w generalizing values r with
  | nil =>
    have hz : r = 0 := by simpa using hr
    subst r
    rfl
  | cons l w ih =>
    cases values with
    | nil => simp at hlen
    | cons a values =>
      cases values with
      | nil => simp at hlen
      | cons b values =>
        have len : (b :: values).length = w.length + 1 := by
          simp only [List.length_cons] at hlen ⊢
          omega
        have steps : step l b = a ∧
            List.zipWith step w values = (b :: values).take w.length := by
          simpa only [List.tail_cons, List.zipWith_cons_cons, List.take_succ_cons,
            List.cons.injEq, List.length_cons] using hstep
        cases r with
        | zero =>
          change branch l (compose w (eval ((b :: values)[w.length]'(by omega)))) = eval a
          have tail := ih (b :: values) len steps.2 0 (by omega)
          simp only [List.drop_zero, List.getElem_cons_zero] at tail
          rw [tail, ← eval_step, steps.1]
        | succ r =>
          exact ih (b :: values) len steps.2 r (by simpa using hr)

end
end Reg.Support.FibonacciBranchStorageWitness
