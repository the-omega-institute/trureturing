/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/SlowSurvivalWindows
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/SlowSurvivalWindows
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Vanishing positive survival with unit successive ratio supplies ordered finite waiting windows. -/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter
open scoped Topology

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.SlowSurvivalWindows

private theorem fixed_shift_ratio (S : ℕ → ℝ) (hpos : ∀ n, 0 < S n)
    (hratio : Tendsto (fun n => S (n + 1) / S n) atTop (𝓝 1)) (L : ℕ) :
    Tendsto (fun n => S (n + L) / S n) atTop (𝓝 1) := by
  induction L with
  | zero =>
      simpa only [Nat.add_zero, div_self (hpos _).ne'] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  | succ L ih =>
      have hr : Tendsto (fun n => S (n + L + 1) / S (n + L)) atTop (𝓝 1) :=
        hratio.comp (tendsto_add_atTop_nat L)
      have hp : Tendsto
          (fun n => (S (n + L + 1) / S (n + L)) * (S (n + L) / S n))
          atTop (𝓝 1) := by
        simpa only [one_mul] using hr.mul ih
      apply hp.congr'
      exact Eventually.of_forall fun n => by
        change S (n + L + 1) / S (n + L) * (S (n + L) / S n) =
          S (n + (L + 1)) / S n
        rw [← Nat.add_assoc]
        field_simp [(hpos (n + L)).ne', (hpos n).ne'] <;> ring

private theorem next_window (S : ℕ → ℝ) (hpos : ∀ n, 0 < S n)
    (hzero : Tendsto S atTop (𝓝 0))
    (hratio : Tendsto (fun n => S (n + 1) / S n) atTop (𝓝 1))
    (θ : ℝ) (hθ : 0 < θ) (N L : ℕ) :
    ∃ p : ℕ × ℕ, N < p.1 ∧ L < p.2 ∧
      1 - θ < S (p.1 + L) / S p.1 ∧ S (p.1 + p.2) / S p.1 < θ := by
  have hearly : ∀ᶠ n in atTop, 1 - θ < S (n + L) / S n :=
    (fixed_shift_ratio S hpos hratio L).eventually
      (eventually_gt_nhds (by linarith : 1 - θ < (1 : ℝ)))
  obtain ⟨n, hn, hnL⟩ := ((eventually_gt_atTop N).and hearly).exists
  have htail : Tendsto (fun U => S (n + U) / S n) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.add_comm, zero_div] using
      (hzero.comp (tendsto_add_atTop_nat n)).div_const (S n)
  obtain ⟨U, hUL, hU⟩ := ((eventually_gt_atTop L).and
    (htail.eventually (eventually_lt_nhds hθ))).exists
  exact ⟨(n, U), hn, hUL, hnL, hU⟩

/-- A single boundary vector encodes all adjacent windows. For `K = 0` it has only
the zero boundary and the horizon is zero. For `K > 0` every selected age and
every window length is positive, the ages are strictly ordered, and the common
horizon is positive. No monotonicity or convergence rate for `S` is required. -/
theorem finite_waiting_windows (S : ℕ → ℝ) (hpos : ∀ n, 0 < S n)
    (hzero : Tendsto S atTop (𝓝 0))
    (hratio : Tendsto (fun n => S (n + 1) / S n) atTop (𝓝 1))
    (K : ℕ) (θ : ℝ) (hθ : 0 < θ) :
    ∃ (H : ℕ) (n : Fin K → ℕ) (b : Fin (K + 1) → ℕ),
      b 0 = 0 ∧ b (Fin.last K) = H ∧ (K = 0 ↔ H = 0) ∧
      StrictMono b ∧ StrictMono n ∧
      ∀ i : Fin K, 0 < n i ∧ b i.castSucc < b i.succ ∧ b i.succ ≤ H ∧
        1 - 2 * θ < (S (n i + b i.castSucc) - S (n i + b i.succ)) / S (n i) := by
  classical
  let next : ℕ × ℕ → ℕ × ℕ := fun p =>
    Classical.choose (next_window S hpos hzero hratio θ hθ p.1 p.2)
  have hnext (p : ℕ × ℕ) : p.1 < (next p).1 ∧ p.2 < (next p).2 ∧
      1 - θ < S ((next p).1 + p.2) / S (next p).1 ∧
      S ((next p).1 + (next p).2) / S (next p).1 < θ :=
    Classical.choose_spec (next_window S hpos hzero hratio θ hθ p.1 p.2)
  let a : ℕ → ℕ × ℕ := fun j => Nat.rec (0, 0) (fun _ p => next p) j
  have hstep (j : ℕ) : (a j).1 < (a (j + 1)).1 ∧ (a j).2 < (a (j + 1)).2 ∧
      1 - θ < S ((a (j + 1)).1 + (a j).2) / S (a (j + 1)).1 ∧
      S ((a (j + 1)).1 + (a (j + 1)).2) / S (a (j + 1)).1 < θ :=
    hnext (a j)
  have ha : StrictMono (fun j => (a j).1) :=
    strictMono_nat_of_lt_succ fun j => (hstep j).1
  have hb : StrictMono (fun j => (a j).2) :=
    strictMono_nat_of_lt_succ fun j => (hstep j).2.1
  refine ⟨(a K).2, (fun i => (a (i.val + 1)).1), (fun i => (a i.val).2),
    rfl, rfl, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro h
      subst K
      rfl
    · intro h
      by_contra hk
      have hx := hb (Nat.pos_of_ne_zero hk)
      change 0 < (a K).2 at hx
      omega
  · intro i j hij
    exact hb (show i.val < j.val from hij)
  · intro i j hij
    exact ha (Nat.add_lt_add_right (show i.val < j.val from hij) 1)
  · intro i
    have hi := hstep i.val
    refine ⟨lt_of_le_of_lt (Nat.zero_le _) hi.1, hi.2.1, ?_, ?_⟩
    · exact hb.monotone (Nat.succ_le_of_lt i.isLt)
    · change 1 - 2 * θ <
        (S ((a (i.val + 1)).1 + (a i.val).2) -
          S ((a (i.val + 1)).1 + (a (i.val + 1)).2)) / S (a (i.val + 1)).1
      rw [sub_div]
      linarith [hi.2.2.1, hi.2.2.2]

#print axioms finite_waiting_windows

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.SlowSurvivalWindows
