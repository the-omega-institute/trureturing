/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/StoppingPrefixes
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/StoppingPrefixes
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Zero prefixes distinguish strict survival, first-one stopping, and the terminal a0 event. -/
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.ReadTree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
namespace ReadTree

def ZeroReplies (ts : List ℤ) (r : ℕ) (x : ℤ → Bool) : Prop :=
  ∀ t ∈ ts.take r, x t = false

theorem stopComb_outcomes (ts : List ℤ) (x : ℤ → Bool) :
    ((stopComb ts).run x).output = some (.a false) ∧
      ((stopComb ts).run x).paid = ts.length ∨
    ((stopComb ts).run x).output = some (.a true) ∧
      1 ≤ ((stopComb ts).run x).paid ∧ ((stopComb ts).run x).paid ≤ ts.length := by
  induction ts with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | cons t ts ih =>
    cases ht : x t with
    | true =>
      right
      simp [stopComb, run, ht, Execution.paid, Execution.prepend]
    | false =>
      rcases ih with h | h
      · left
        simpa only [stopComb, run, ht, Bool.false_eq_true, ↓reduceIte,
          Execution.output_prepend, Execution.paid_prepend, List.length_cons] using
          And.intro h.1 (congrArg (· + 1) h.2)
      · right
        simp only [stopComb, run, ht, Bool.false_eq_true, ↓reduceIte,
          Execution.output_prepend, Execution.paid_prepend, List.length_cons]
        exact ⟨h.1, by omega, by omega⟩

theorem stopComb_not_a1_at_zero (ts : List ℤ) (x : ℤ → Bool) :
    ¬(((stopComb ts).run x).output = some (.a true) ∧ ((stopComb ts).run x).paid = 0) := by
  intro h
  rcases stopComb_outcomes ts x with ha | ha
  · have := ha.1.symm.trans h.1; cases this
  · omega

/-- A new one response is exactly the difference of successive zero-prefix events. -/
theorem zero_prefix_difference (ts : List ℤ) (x : ℤ → Bool) (r : ℕ)
    (hr : r < ts.length) :
    (ZeroReplies ts r x ∧ ¬ZeroReplies ts (r + 1) x) ↔
      ((stopComb ts).run x).output = some (.a true) ∧
        ((stopComb ts).run x).paid = r + 1 := by
  induction ts generalizing r with
  | nil => simp at hr
  | cons t ts ih =>
    cases r with
    | zero =>
      cases hx : x t with
      | true => simp [ZeroReplies, stopComb, run, hx, Execution.paid, Execution.prepend]
      | false =>
        have hn := stopComb_not_a1_at_zero ts x
        simp only [ZeroReplies, List.take_zero, List.take_succ_cons, List.forall_mem_cons,
          List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true,
          hx, not_true_eq_false, true_and, stopComb, run, Bool.false_eq_true, ↓reduceIte,
          Execution.output_prepend, Execution.paid_prepend] at *
        simpa using hn
    | succ r =>
      have hr' : r < ts.length := by simpa using hr
      cases hx : x t with
      | true =>
        simp [ZeroReplies, stopComb, run, hx, Execution.paid, Execution.prepend]
      | false =>
        simpa [ZeroReplies, stopComb, run, hx, Execution.paid_prepend,
          Execution.output_prepend, Nat.add_assoc] using ih r hr'

/-- The final zero prefix is the a0 return event, rather than strict survival. -/
theorem zero_prefix_final (ts : List ℤ) (x : ℤ → Bool) :
    ZeroReplies ts ts.length x ↔
      ((stopComb ts).run x).output = some (.a false) ∧
        ((stopComb ts).run x).paid = ts.length := by
  induction ts with
  | nil => simp [ZeroReplies, stopComb, run, Execution.paid]
  | cons t ts ih =>
    cases hx : x t with
    | true => simp [ZeroReplies, stopComb, run, hx]
    | false =>
      simpa [ZeroReplies, stopComb, run, hx, Execution.output_prepend,
        Execution.paid_prepend] using ih

/-- Before the last call, a zero prefix means strictly more paid reads. -/
theorem zero_prefix_survival (ts : List ℤ) (x : ℤ → Bool) (r : ℕ)
    (hr : r < ts.length) : ZeroReplies ts r x ↔ r < ((stopComb ts).run x).paid := by
  induction ts generalizing r with
  | nil => simp at hr
  | cons t ts ih =>
    cases r with
    | zero =>
      have hp : 0 < ((stopComb (t :: ts)).run x).paid := by
        simp only [stopComb, run]
        split <;> simp
      simpa [ZeroReplies] using hp
    | succ r =>
      have hr' : r < ts.length := by simpa using hr
      cases hx : x t with
      | true => simp [ZeroReplies, stopComb, run, hx, Execution.paid, Execution.prepend]
      | false =>
        simpa [ZeroReplies, stopComb, run, hx, Execution.paid_prepend] using ih r hr'

def edgeComb (es : List ℤ) (φ : Bool) : ReadTree :=
  stopComb (es.map (fun e => 2 * e + φ.toInt))

theorem edge_zero_prefix (es : List ℤ) (φ : Bool) (S : Spins) (r : ℕ) :
    ZeroReplies (es.map (fun e => 2 * e + φ.toInt)) r (visible φ S) ↔
      ∀ e ∈ (es.take r).toFinset, S e = S (e + 1) := by
  have hb (a b : Bool) : Bool.xor a b = false ↔ a = b := by
    cases a <;> cases b <;> decide
  simp [ZeroReplies, ← List.map_take, active_visible, hb]

end ReadTree
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
