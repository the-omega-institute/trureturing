/- GID: D5/S3/Analytic/Interpolation/UniformCoefficientBudget
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/UniformCoefficientBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Derivative budgets control the coefficient sum of exact interpolation without node separation. -/

import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

noncomputable section

open Finset Set Polynomial

namespace D5.S3.Analytic.Interpolation.UniformCoefficientBudget

/-- Iterated Rolle on an ordered family of distinct zeros. -/
private theorem rolle_nodes (n : ℕ) (f : ℝ → ℝ) (a b : ℝ)
    (z : Fin (n + 1) → ℝ) (hz : StrictMono z)
    (hzi : ∀ i, z i ∈ Icc a b) (hfz : ∀ i, f (z i) = 0)
    (hc : ∀ j < n, ContinuousOn (iteratedDeriv j f) (Icc a b)) :
    ∃ x ∈ Icc a b, iteratedDeriv n f x = 0 := by
  induction n generalizing f with
  | zero => exact ⟨z 0, hzi 0, by simpa using hfz 0⟩
  | succ n ih =>
    have hstep (i : Fin (n + 1)) :
        ∃ x ∈ Ioo (z i.castSucc) (z i.succ), deriv f x = 0 := by
      apply exists_deriv_eq_zero (hz (by simp))
      · exact (by simpa using hc 0 (by omega)).mono
          (Icc_subset_Icc (hzi i.castSucc).1 (hzi i.succ).2)
      · rw [hfz, hfz]
    choose w hw hwzero using hstep
    have hwmono : StrictMono w := by
      intro i j hij
      exact (hw i).2.trans_le ((hz.monotone (by simpa using hij)).trans (hw j).1.le)
    have hwi (i : Fin (n + 1)) : w i ∈ Icc a b :=
      ⟨(hzi i.castSucc).1.trans (hw i).1.le, (hw i).2.le.trans (hzi i.succ).2⟩
    obtain ⟨x, hx, hzero⟩ := ih (deriv f) w hwmono hwi hwzero (by
      intro j hj
      simpa only [← iteratedDeriv_succ'] using hc (j + 1) (by omega))
    exact ⟨x, hx, by simpa only [iteratedDeriv_succ'] using hzero⟩

end D5.S3.Analytic.Interpolation.UniformCoefficientBudget
