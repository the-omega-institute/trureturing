/- GID: D5/S3/Analytic/TailCertificate
   generality: G
   mirror-B: D5/B/S3/Analytic/TailCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finitely many tail certificates sum to a tail certificate with added budgets, and the summed window reading strictly encloses the exact sum in the closed budget interval. -/

import Mathlib

open scoped BigOperators

namespace D5.S3.Analytic.TailCertificate

/-- A family of finite windows cofinal among all finite sets of source atoms. -/
structure CofinalWindowFamily (Atom Window : Type*) where
  contents : Window -> Finset Atom
  cofinal : forall finite : Finset Atom, exists window, finite ⊆ contents window

/-- The source control clause, isolated as exactly the closure properties used by finite sums. -/
structure TailControl (Window : Type*) where
  Holds : (Window -> Real) -> Prop
  zero : Holds 0
  add : forall {first second}, Holds first -> Holds second -> Holds (first + second)

/-- A window reading with a controlled nonnegative budget bounding its error. -/
structure Certificate {Atom Window : Type*} (family : CofinalWindowFamily Atom Window)
    (control : TailControl Window) (value : Real) where
  reading : Window -> Real
  budget : Window -> Real
  budget_nonneg : forall window, 0 <= budget window
  error_le : forall window, |value - reading window| <= budget window
  controlled : control.Holds budget

private theorem TailControl.holds_finset_sum {Window Index : Type*}
    (control : TailControl Window) (s : Finset Index) (budget : Index -> Window -> Real)
    (hbudget : forall i, i ∈ s -> control.Holds (budget i)) :
    control.Holds (s.sum budget) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using control.zero
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact control.add (hbudget i (Finset.mem_insert_self i s))
        (ih fun j hj => hbudget j (Finset.mem_insert_of_mem hj))

/-- Finite tail certificates add with summed budgets, and the resulting reading encloses
the exact sum in the corresponding closed interval. -/
theorem finite_tail_certificates_sum_and_enclose
    {Atom Window Index : Type*} (family : CofinalWindowFamily Atom Window)
    (control : TailControl Window) (s : Finset Index)
    (value : Index -> Real)
    (certificate : forall i, Certificate family control (value i))
    (window : Window) :
    control.Holds (s.sum fun i => (certificate i).budget) ∧
      |s.sum value - s.sum (fun i => (certificate i).reading window)| <=
        s.sum (fun i => (certificate i).budget window) ∧
      s.sum (fun i => (certificate i).reading window) -
          s.sum (fun i => (certificate i).budget window) <= s.sum value ∧
      s.sum value <= s.sum (fun i => (certificate i).reading window) +
        s.sum (fun i => (certificate i).budget window) := by
  classical
  have hcontrolled : control.Holds (s.sum fun i => (certificate i).budget) :=
    control.holds_finset_sum s (fun i => (certificate i).budget)
      (fun i _ => (certificate i).controlled)
  have herr :
      |s.sum value - s.sum (fun i => (certificate i).reading window)| <=
        s.sum (fun i => (certificate i).budget window) := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs (s := s) (f := fun i =>
      value i - (certificate i).reading window)).trans ?_
    exact Finset.sum_le_sum fun i _ => (certificate i).error_le window
  refine ⟨hcontrolled, herr, ?_, ?_⟩ <;> rw [abs_le] at herr <;> linarith

end D5.S3.Analytic.TailCertificate
