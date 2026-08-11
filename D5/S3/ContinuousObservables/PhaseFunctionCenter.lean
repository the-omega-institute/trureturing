/- GID: D5/S3/ContinuousObservables/PhaseFunctionCenter
   generality: G
   mirror-B: D5/B/S3/ContinuousObservables/PhaseFunctionCenter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Identify the continuous matrix-observable center with scalar phase functions. -/

import D5.S3.Observer.CenterOperational
import Mathlib.Data.Matrix.Basis
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Instances.Matrix

namespace D5.S3.ContinuousObservables.PhaseFunctionCenter

/-- Embed a continuous phase observable as a scalar matrix field on a cyclic window. -/
noncomputable def phaseScalarObservable {M : ℕ} [NeZero M]
    (f : C(AddCircle (1 : ℝ), ℂ)) :
    C(AddCircle (1 : ℝ), Matrix (ZMod M) (ZMod M) ℂ) :=
  ⟨fun phase => Matrix.scalar (ZMod M) (f phase), by
    apply continuous_matrix
    intro i j
    by_cases h : i = j
    · subst j
      simpa using f.continuous
    · simpa [Matrix.scalar_apply, h] using
        (continuous_const : Continuous fun _ : AddCircle (1 : ℝ) => (0 : ℂ))⟩

/-- The center of the continuous cyclic-window matrix bundle consists exactly
of scalar fields, hence is the algebra of continuous functions on the phase circle. -/
theorem continuous_window_center_eq_phase_functions {M : ℕ} [NeZero M] :
    Set.center C(AddCircle (1 : ℝ), Matrix (ZMod M) (ZMod M) ℂ) =
      Set.range (phaseScalarObservable (M := M)) := by
  ext A
  rw [Set.mem_range]
  constructor
  · intro hA
    rw [Semigroup.mem_center_iff] at hA
    let i : ZMod M := 0
    let f : C(AddCircle (1 : ℝ), ℂ) :=
      ⟨fun phase => A phase i i,
        (continuous_apply_apply i i).comp A.continuous⟩
    refine ⟨f, ContinuousMap.ext ?_⟩
    intro phase
    have hcenter : A phase ∈ Set.center (Matrix (ZMod M) (ZMod M) ℂ) := by
      rw [Semigroup.mem_center_iff]
      intro B
      exact congrArg
        (fun C : C(AddCircle (1 : ℝ), Matrix (ZMod M) (ZMod M) ℂ) => C phase)
        (hA (ContinuousMap.const (AddCircle (1 : ℝ)) B))
    rw [Matrix.center_eq_range] at hcenter
    obtain ⟨c, hc⟩ := hcenter
    have hdiag : A phase i i = c := by
      rw [← hc]
      simp
    change Matrix.scalar (ZMod M) (f phase) = A phase
    rw [show f phase = c by exact hdiag]
    exact hc
  · rintro ⟨f, rfl⟩
    rw [Semigroup.mem_center_iff]
    intro B
    apply ContinuousMap.ext
    intro phase
    exact (Matrix.scalar_commute (f phase) (Commute.all _) (B phase)).symm.eq

end D5.S3.ContinuousObservables.PhaseFunctionCenter
