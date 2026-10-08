/- GID: D5/S3/ObserverMemory/Prediction/CausalRepairEnvelopes
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Prediction/CausalRepairEnvelopes
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Common causal upper and lower envelopes of finite response tables. -/

import D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators
noncomputable section
namespace D5.S3.ObserverMemory.Prediction.CausalRepairEnvelopes
open D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion

private def prependPrefix {n : ℕ} {Y : Fin (n + 1) → Type*} {k : ℕ}
    (z : Y 0) (x : Prefix (fun t : Fin n => Y t.succ) k) : Prefix Y (k + 1) :=
  fun i => Fin.cases (motive := fun j => j.val < k + 1 → Y j)
    (fun _ => z) (fun j hj => x ⟨j, by simpa using hj⟩) i.1 i.2

private def dropPrefix {n : ℕ} {Y : Fin (n + 1) → Type*} {k : ℕ}
    (x : Prefix Y (k + 1)) : Prefix (fun t : Fin n => Y t.succ) k :=
  fun i => x ⟨i.1.succ, by simpa using i.2⟩

private def tailStrategy {n : ℕ} {A Y : Fin (n + 1) → Type*}
    (f : (t : Fin (n + 1)) → Prefix Y t.val → A t) (z : Y 0) :
    (t : Fin n) → Prefix (fun i : Fin n => Y i.succ) t.val → A t.succ :=
  fun t x => f t.succ (prependPrefix z x)

private def joinStrategy {n : ℕ} {A Y : Fin (n + 1) → Type*}
    (a : A 0)
    (g : Y 0 → (t : Fin n) → Prefix (fun i : Fin n => Y i.succ) t.val → A t.succ) :
    (t : Fin (n + 1)) → Prefix Y t.val → A t :=
  Fin.cases (fun _ => a) (fun t x => g (x ⟨0, by simp⟩) t (dropPrefix x))

private theorem tail_actions {n : ℕ} {A Y : Fin (n + 1) → Type*}
    (f : (t : Fin (n + 1)) → Prefix Y t.val → A t)
    (z : Y 0) (y : (t : Fin n) → Y t.succ) :
    Fin.tail (feedbackActions f (Fin.cons z y)) = feedbackActions (tailStrategy f z) y := by
  funext t
  simp only [Fin.tail, feedbackActions, tailStrategy]
  congr 1
  funext i
  rcases i with ⟨i, hi⟩
  refine Fin.cases ?_ (fun j => ?_) i hi
  · intro h
    rfl
  · intro h
    rfl

private theorem join_tail {n : ℕ} {A Y : Fin (n + 1) → Type*}
    (a : A 0)
    (g : Y 0 → (t : Fin n) → Prefix (fun i : Fin n => Y i.succ) t.val → A t.succ)
    (z : Y 0) : tailStrategy (joinStrategy a g) z = g z := by
  funext t x
  simp only [tailStrategy, joinStrategy, Fin.cases_succ]
  congr 1

private theorem split_mass {n : ℕ} {A Y : Fin (n + 1) → Type*}
    [∀ t, Fintype (Y t)]
    (P : ((t : Fin (n + 1)) → Y t) → ((t : Fin (n + 1)) → A t) → ℝ)
    (f : (t : Fin (n + 1)) → Prefix Y t.val → A t) :
    feedbackMass P f = ∑ z : Y 0,
      feedbackMass (fun y a => P (Fin.cons z y)
        (Fin.cons (f 0 (fun i => (Nat.not_lt_zero i.1.val i.2).elim)) a))
        (tailStrategy f z) := by
  classical
  rw [feedbackMass, ← (Fin.consEquiv Y).sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro z hz
  rw [feedbackMass]
  apply Finset.sum_congr rfl
  intro y hy
  congr 1
  rw [← Fin.cons_self_tail (feedbackActions f (Fin.cons z y)), tail_actions]
  rfl

end D5.S3.ObserverMemory.Prediction.CausalRepairEnvelopes
