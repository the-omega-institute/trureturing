/- GID: D5/S3/Quantum/Fibers/PhysicalFiber
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/PhysicalFiber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite-dimensional physical readout fiber is nonempty, compact, and convex. -/

import Mathlib

namespace D5.S3.Quantum.Fibers.PhysicalFiber

open Set
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology

/-- States with the same accessible readout as `rho`, cut down by positivity and normalization. -/
def physicalFiber {n k : Type*} [Fintype n]
    (readout : Matrix n n ℂ →ₗ[ℂ] (k → ℂ)) (rho : Matrix n n ℂ) :
    Set (Matrix n n ℂ) :=
  {sigma | readout sigma = readout rho ∧ sigma.PosSemidef ∧ Matrix.trace sigma = 1}

/-- In finite dimension, the positive trace-one states with a fixed accessible readout form a
    nonempty compact convex fiber. -/
theorem finite_dimensional_physical_fiber {n k : Type*}
    [Fintype n] [Nonempty n] [Finite k]
    (readout : Matrix n n ℂ →ₗ[ℂ] (k → ℂ)) (rho : Matrix n n ℂ)
    (hRho : rho.PosSemidef) (hTrace : Matrix.trace rho = 1) :
    (physicalFiber readout rho).Nonempty ∧
      IsCompact (physicalFiber readout rho) ∧
      Convex ℝ (physicalFiber readout rho) := by
  classical
  letI := Fintype.ofFinite k
  letI : CStarAlgebra (Matrix n n ℂ) := { }
  have state_norm_le_one {sigma : Matrix n n ℂ} (hSigmaPos : sigma.PosSemidef)
      (hSigmaTrace : Matrix.trace sigma = 1) : ‖sigma‖ ≤ 1 := by
    have hEigenvalueSum : ∑ j, hSigmaPos.isHermitian.eigenvalues j = 1 := by
      have hComplexSum := hSigmaPos.isHermitian.trace_eq_sum_eigenvalues
      rw [hSigmaTrace] at hComplexSum
      simpa using congrArg Complex.re hComplexSum.symm
    have hNormSpectrum :=
      CStarAlgebra.norm_or_neg_norm_mem_spectrum (a := sigma)
        (ha := hSigmaPos.isHermitian.isSelfAdjoint)
    rw [hSigmaPos.isHermitian.spectrum_real_eq_range_eigenvalues] at hNormSpectrum
    rcases hNormSpectrum with ⟨i, hi⟩ | ⟨i, hi⟩
    · rw [← hi, ← hEigenvalueSum]
      exact Finset.single_le_sum
        (fun j _ => hSigmaPos.eigenvalues_nonneg j) (Finset.mem_univ i)
    · have hEigenvalueNonneg := hSigmaPos.eigenvalues_nonneg i
      rw [hi] at hEigenvalueNonneg
      linarith [norm_nonneg sigma]
  have hNonempty : (physicalFiber readout rho).Nonempty := by
    exact ⟨rho, rfl, hRho, hTrace⟩
  have hClosed : IsClosed (physicalFiber readout rho) := by
    have hReadoutContinuous : Continuous readout :=
      LinearMap.continuous_of_finiteDimensional readout
    have hReadoutClosed : IsClosed {sigma : Matrix n n ℂ | readout sigma = readout rho} :=
      isClosed_eq hReadoutContinuous continuous_const
    have hPosClosed : IsClosed {sigma : Matrix n n ℂ | sigma.PosSemidef} := by
      have hset : {sigma : Matrix n n ℂ | sigma.PosSemidef} =
          Set.Ici (0 : Matrix n n ℂ) := by
        ext sigma
        exact Matrix.nonneg_iff_posSemidef.symm
      rw [hset]
      exact isClosed_Ici
    have hTraceContinuous : Continuous (Matrix.traceLinearMap n ℂ ℂ) :=
      LinearMap.continuous_of_finiteDimensional _
    have hTraceClosed : IsClosed {sigma : Matrix n n ℂ | Matrix.trace sigma = 1} :=
      isClosed_eq hTraceContinuous continuous_const
    exact hReadoutClosed.inter (hPosClosed.inter hTraceClosed)
  have hCompact : IsCompact (physicalFiber readout rho) := by
    apply (isCompact_closedBall (0 : Matrix n n ℂ) 1).of_isClosed_subset hClosed
    intro sigma hSigma
    rw [Metric.mem_closedBall, dist_zero_right]
    exact state_norm_le_one hSigma.2.1 hSigma.2.2
  have hConvex : Convex ℝ (physicalFiber readout rho) := by
    intro x hx y hy a b ha hb hab
    refine ⟨?_, ?_, ?_⟩
    · calc
        readout (a • x + b • y) = a • readout x + b • readout y := by
          rw [map_add, readout.map_smul_of_tower, readout.map_smul_of_tower]
        _ = a • readout rho + b • readout rho := by rw [hx.1, hy.1]
        _ = (a + b) • readout rho := by rw [add_smul]
        _ = readout rho := by rw [hab, one_smul]
    · exact (hx.2.1.smul ha).add (hy.2.1.smul hb)
    · calc
        Matrix.trace (a • x + b • y) =
            a • Matrix.trace x + b • Matrix.trace y := by
          rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul]
        _ = a • (1 : ℂ) + b • (1 : ℂ) := by rw [hx.2.2, hy.2.2]
        _ = ((a + b : ℝ) : ℂ) := by
          simp [Algebra.smul_def]
        _ = 1 := by rw [hab]; norm_num
  exact ⟨hNonempty, hCompact, hConvex⟩

#print axioms finite_dimensional_physical_fiber

end D5.S3.Quantum.Fibers.PhysicalFiber
