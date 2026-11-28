/- GID: D5/S3/Topology/Measures/AtomicMomentRepair
   generality: G
   mirror-B: D5/B/S3/Topology/Measures/AtomicMomentRepair
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Replace the zero cutoff while preserving five signed moments. -/

import D5.S3.MeasureTheory.AtomicMomentRepair
import Mathlib.Topology.Order.DenselyOrdered

/-! Publication statement for replacing the zero cutoff in a five-moment match. -/

open Set
open scoped BigOperators

namespace D5.S3.Topology.Measures.AtomicMomentRepair

/-- Move the zero-cutoff atom to a positive cutoff and restore its five moments
using arbitrarily small signed corrections at fixed positive cutoffs. -/
theorem exists_exact_moment_repair
    (moment : ℝ → Fin 5 → ℝ)
    (hContinuous : ContinuousWithinAt moment (Ioc 0 1) 0)
    (basisNode : Fin 5 → Ioc (0 : ℝ) 1)
    (basis : Module.Basis (Fin 5) ℝ (Fin 5 → ℝ))
    (hBasis : ∀ j, basis j = moment (basisNode j))
    (weight : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (x : Ioc (0 : ℝ) 1) (correction : Fin 5 → ℝ),
      weight • moment x + (∑ j, correction j • moment (basisNode j)) =
        weight • moment 0 ∧ (∑ j, |correction j|) < ε := by
  have h0 : (0 : ℝ) ∈ closure (Ioc 0 1) := by
    rw [closure_Ioc (zero_ne_one : (0 : ℝ) ≠ 1)]
    exact ⟨le_rfl, zero_le_one⟩
  obtain ⟨node, correction, hEq, hCost⟩ :=
    Omega.MeasureTheory.AtomicMomentRepair.exists_exact_moment_repair
      moment (Ioc 0 1) basisNode basis hBasis (fun _ : Unit => moment 0)
      (fun _ => weight) (fun _ => hContinuous.mem_closure_image h0) hε
  exact ⟨node (), correction, by simpa using hEq, hCost⟩

end D5.S3.Topology.Measures.AtomicMomentRepair
