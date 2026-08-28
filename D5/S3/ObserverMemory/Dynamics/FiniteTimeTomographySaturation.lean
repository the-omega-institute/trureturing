/- GID: D5/S3/ObserverMemory/Dynamics/FiniteTimeTomographySaturation
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Dynamics/FiniteTimeTomographySaturation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Infinite observability is decided by the first trace-zero carrier dimension layers. -/

import D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
import D5.S3.Quantum.Fibers.TraceZeroReadoutOrthogonalEquivalence
import Mathlib.LinearAlgebra.Charpoly.Basic

/- Library-search audit trail (2026-08-27):
   * Exact family hits `HermitianTraceZero` and
     `trace_zero_hermitian_finrank` supply the source's real traceless
     Hermitian carrier and its exact dimension `d ^ 2 - 1`.
   * Repository searches for finite/infinite unobservable kernels, finrank
     saturation, and finite-time tomography found the canonical kernel and
     observable-Krylov families, but no theorem equating the all-future kernel
     with the first `d ^ 2 - 1` time layers on this carrier.
   * Pinned Mathlib's exact Cayley--Hamilton primitive is
     `LinearMap.pow_eq_aeval_mod_charpoly`; polynomial reduction and
     `Polynomial.aeval_eq_sum_range'` express every later power through the
     first ambient-finrank powers. No packaged kernel-saturation theorem was
     found.
   * No new definition or abbreviation is introduced. Both unobservable
     spaces are constructed publicly from the source evolution, readout, and
     kernels. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Dynamics.FiniteTimeTomographySaturation

open D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
open D5.S3.Quantum.Fibers.TraceZeroReadoutOrthogonalEquivalence
open D5.S3.Quantum.Measurement.BasisMeasurementProjection

private theorem all_future_kernel_eq_finrank_kernel
    {K V Y : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup Y] [Module K Y]
    (A : V →ₗ[K] V) (C : V →ₗ[K] Y) :
    (⨅ k : ℕ, LinearMap.ker (C.comp (A ^ k))) =
      ⨅ k : Fin (Module.finrank K V),
        LinearMap.ker (C.comp (A ^ (k : ℕ))) := by
  let n := Module.finrank K V
  by_cases hn : n = 0
  · haveI : Subsingleton V := Module.finrank_zero_iff.mp hn
    exact Subsingleton.elim _ _
  · apply le_antisymm
    · apply le_iInf
      intro k
      exact iInf_le (fun exponent : ℕ =>
        LinearMap.ker (C.comp (A ^ exponent))) (k : ℕ)
    · apply le_iInf
      intro exponent x hx
      rw [Submodule.mem_iInf] at hx
      rw [LinearMap.mem_ker, LinearMap.comp_apply]
      let reduced := Polynomial.X ^ exponent %ₘ A.charpoly
      have hcharpoly : A.charpoly ≠ 1 := by
        intro hOne
        have hdegree := congrArg Polynomial.natDegree hOne
        rw [A.charpoly_natDegree, Polynomial.natDegree_one] at hdegree
        exact hn hdegree
      have hreducedDegree : reduced.natDegree < n := by
        simpa only [reduced, n, A.charpoly_natDegree] using
          Polynomial.natDegree_modByMonic_lt
            (Polynomial.X ^ exponent) A.charpoly_monic hcharpoly
      have hpower :
          A ^ exponent =
            ∑ i ∈ Finset.range n, reduced.coeff i • A ^ i := by
        calc
          A ^ exponent = Polynomial.aeval A reduced :=
            A.pow_eq_aeval_mod_charpoly exponent
          _ = ∑ i ∈ Finset.range n, reduced.coeff i • A ^ i :=
            Polynomial.aeval_eq_sum_range' hreducedDegree A
      rw [hpower]
      simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
        map_sum, map_smul]
      apply Finset.sum_eq_zero
      intro i hi
      have hxi := hx ⟨i, by
        change i < n
        exact Finset.mem_range.mp hi⟩
      rw [LinearMap.mem_ker] at hxi
      rw [show C ((A ^ i) x) = 0 by
        simpa only [LinearMap.comp_apply] using hxi, smul_zero]

/-- On the real traceless Hermitian carrier of dimension `d ^ 2 - 1`, the
all-future unobservable subspace equals the intersection from time zero through
time `d ^ 2 - 2`. Hence a trivial all-future kernel already forces the finite
kernel at that exact horizon to be trivial. -/
theorem finite_time_tomography_saturation
    (d : ℕ) [NeZero d]
    (A : HermitianTraceZero (d := Fin d) →ₗ[ℝ]
      HermitianTraceZero (d := Fin d))
    {Y : Type*} [AddCommGroup Y] [Module ℝ Y]
    (C : HermitianTraceZero (d := Fin d) →ₗ[ℝ] Y) :
    let infiniteKernel :=
      ⨅ k : ℕ, LinearMap.ker (C.comp (A ^ k))
    let finiteKernel :=
      ⨅ k : Fin (d ^ 2 - 1),
        LinearMap.ker (C.comp (A ^ (k : ℕ)))
    (infiniteKernel = ⊥ → finiteKernel = ⊥) ∧
      infiniteKernel = finiteKernel := by
  dsimp only
  let carrier := HermitianTraceZero (d := Fin d)
  let directEquiv : carrier ≃ₗ[ℝ] traceZeroHermitian d :=
    { toFun := fun X => ⟨⟨X.1, X.2.1⟩, X.2.2⟩
      invFun := fun X => ⟨X.1.1, X.1.2, X.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hdimension :
      Module.finrank ℝ (HermitianTraceZero (d := Fin d)) = d ^ 2 - 1 := by
    change Module.finrank ℝ carrier = d ^ 2 - 1
    rw [directEquiv.finrank_eq]
    exact trace_zero_hermitian_finrank d
  have hsaturation := all_future_kernel_eq_finrank_kernel A C
  rw [hdimension] at hsaturation
  exact ⟨fun hzero => hsaturation ▸ hzero, hsaturation⟩

#print axioms finite_time_tomography_saturation

end D5.S3.ObserverMemory.Dynamics.FiniteTimeTomographySaturation
