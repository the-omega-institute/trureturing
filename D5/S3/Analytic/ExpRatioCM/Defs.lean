/- GID: D5/S3/Analytic/ExpRatioCM/Defs
   generality: G
   mirror-B: D5/B/S3/Analytic/ExpRatioCM/Defs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas, mathlib/module/Mathlib.Analysis.SpecialFunctions.ExpDeriv]
   utility: none
   digest: Signed exponential reciprocal derivatives and complete monotonicity of their ratios. -/

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace D5.S3.Analytic.ExpRatioCM.Defs

/-- F_i(t) = (-1)^i (1/(exp t - 1))^(i). -/
noncomputable def F (i : ℕ) (t : ℝ) : ℝ :=
  (-1) ^ i * iteratedDeriv i (fun s => 1 / (Real.exp s - 1)) t

/-- G_i(t) = (-1)^i (1/(1 - exp(-t)))^(i). -/
noncomputable def G (i : ℕ) (t : ℝ) : ℝ :=
  (-1) ^ i * iteratedDeriv i (fun s => 1 / (1 - Real.exp (-s))) t

/-- Consecutive signed derivative ratio of the first reciprocal. -/
noncomputable def ratioF (i : ℕ) (t : ℝ) : ℝ := F (i + 1) t / F i t

/-- Consecutive signed derivative ratio of the second reciprocal. -/
noncomputable def ratioG (i : ℕ) (t : ℝ) : ℝ := G (i + 1) t / G i t

/-- Complete monotonicity on the positive real half-line. -/
def CompletelyMonotoneOn (h : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ⊤ h (Set.Ioi 0) ∧
    ∀ k : ℕ, ∀ t : ℝ, 0 < t → 0 ≤ (-1) ^ k * iteratedDeriv k h t

/-- The assertion about both families of consecutive ratios. -/
def claim : Prop :=
  ∀ i : ℕ, CompletelyMonotoneOn (ratioF i) ∧ CompletelyMonotoneOn (ratioG i)

end D5.S3.Analytic.ExpRatioCM.Defs
