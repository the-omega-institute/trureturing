import D5.S3.QuantumChannels.ProjectionDiagnostics.CyclicMonitoredContraction

open scoped InnerProductSpace
open D5.S3.QuantumChannels.ProjectionDiagnostics.CyclicMonitoredContraction
open D5.S3.QuantumChannels.ProjectionDiagnostics.MonitoredReturnConservation

noncomputable section

-- The actual restriction also handles a zero generating vector.
example : (⨅ n : ℕ, LinearMap.ker
    ((cyclicClick (LinearIsometryEquiv.refl ℂ ℂ) 0).toLinearMap.comp
      ((cyclicStep (LinearIsometryEquiv.refl ℂ ℂ) 0).toLinearMap ^ n))) = ⊥ :=
  cyclic_future_kernel_eq_bot _ _

-- Omitting the actual cyclic restriction permits a nonzero all-future hidden vector.
example : (1 : ℂ) ≠ 0 ∧ ∀ n : ℕ,
    (ℂ ∙ (0 : ℂ)).starProjection
      ((monitoredStep (LinearIsometryEquiv.refl ℂ ℂ) 0 ^ n) 1) = 0 := by
  simp

-- A nonzero eigenvector generates precisely its line.
example : cyclicSpace (LinearIsometryEquiv.refl ℂ ℂ) 1 = ⊤ := by
  apply top_unique
  intro z _
  have h : (1 : ℂ) ∈ cyclicSpace (LinearIsometryEquiv.refl ℂ ℂ) 1 :=
    Submodule.subset_span ⟨0, rfl⟩
  simpa using (cyclicSpace (LinearIsometryEquiv.refl ℂ ℂ) 1).smul_mem z h
