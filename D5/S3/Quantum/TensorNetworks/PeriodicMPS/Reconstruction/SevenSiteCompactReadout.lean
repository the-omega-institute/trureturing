/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteCompactReadout
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteCompactReadout
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Pauli coordinates for exchange-symmetric two-site densities. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reflection.PeriodicMPSExchangeSymmetry
import Mathlib.Analysis.Matrix.Normed

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSCompactReadout

open Set Matrix Function
open scoped Topology Matrix Kronecker Matrix.Norms.Elementwise ComplexConjugate
open TwoQubitMarginalReflection (Density ExchangeSymmetric)
open PeriodicMPSUniformHardCoreLocalization
open PeriodicMPSUniformHardCoreMarginalWitness (Amplitudes pairGram mass_eq_trace)
open PeriodicMPSProjectiveCoordinates (mass mass_pos)
open PeriodicMPSExchangeSymmetry (normalizedMarginal_exchangeSymmetric)

open private pauliFrame expect expect_swap eq_of_frame_readouts trace_is_real from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reflection.TwoQubitMarginalReflection

noncomputable section

abbrev Readout := Fin 9 → ℝ

/-- Index zero denotes the identity, followed by X, Y and Z.
First the three Bloch components, then the upper triangle of the correlation matrix. -/
def pauliIndices : Fin 9 → Fin 4 × Fin 4 :=
  ![(1, 0), (2, 0), (3, 0), (1, 1), (1, 2), (1, 3), (2, 2), (2, 3), (3, 3)]

/-- Real Pauli expectation values, in the order specified by `pauliIndices`. -/
def readout : Density →L[ℝ] Readout :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ρ k => expect (pauliFrame (pauliIndices k).1 ⊗ₖ
        pauliFrame (pauliIndices k).2) ρ
      map_add' := by
        intro ρ σ
        funext k
        simp [expect, Matrix.mul_add, Matrix.trace_add]
      map_smul' := by
        intro t ρ
        funext k
        simp [expect, Matrix.trace_smul] }

theorem readout_apply (ρ : Density) (k : Fin 9) :
    readout ρ k = ((pauliFrame (pauliIndices k).1 ⊗ₖ
      pauliFrame (pauliIndices k).2) * ρ).trace.re := rfl

/-- A Hermitian, exchange-symmetric matrix is determined by its nine readings and trace. -/
theorem eq_of_readout_of_trace_eq {ρ σ : Density}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (hsρ : ExchangeSymmetric ρ) (hsσ : ExchangeSymmetric σ)
    (ht : ρ.trace.re = σ.trace.re) (h : readout ρ = readout σ) : ρ = σ := by
  apply eq_of_frame_readouts hρ hσ
  have h00 : expect (pauliFrame 0 ⊗ₖ pauliFrame 0) ρ =
      expect (pauliFrame 0 ⊗ₖ pauliFrame 0) σ := by
    simpa [pauliFrame, expect] using ht
  have hcoord (i j : Fin 4) (k : Fin 9) (hk : pauliIndices k = (i, j)) :
      expect (pauliFrame i ⊗ₖ pauliFrame j) ρ =
        expect (pauliFrame i ⊗ₖ pauliFrame j) σ := by
    simpa only [readout_apply, hk, expect] using congrFun h k
  have hswap (i j : Fin 4)
      (hij : expect (pauliFrame i ⊗ₖ pauliFrame j) ρ =
        expect (pauliFrame i ⊗ₖ pauliFrame j) σ) :
      expect (pauliFrame j ⊗ₖ pauliFrame i) ρ =
        expect (pauliFrame j ⊗ₖ pauliFrame i) σ :=
    (expect_swap hsρ _ _).trans (hij.trans (expect_swap hsσ _ _).symm)
  intro i j
  fin_cases i <;> fin_cases j
  all_goals
    first
    | exact h00
    | exact hcoord _ _ 0 rfl
    | exact hcoord _ _ 1 rfl
    | exact hcoord _ _ 2 rfl
    | exact hcoord _ _ 3 rfl
    | exact hcoord _ _ 4 rfl
    | exact hcoord _ _ 5 rfl
    | exact hcoord _ _ 6 rfl
    | exact hcoord _ _ 7 rfl
    | exact hcoord _ _ 8 rfl
    | exact hswap _ _ (hcoord _ _ 0 rfl)
    | exact hswap _ _ (hcoord _ _ 1 rfl)
    | exact hswap _ _ (hcoord _ _ 2 rfl)
    | exact hswap _ _ (hcoord _ _ 4 rfl)
    | exact hswap _ _ (hcoord _ _ 5 rfl)
    | exact hswap _ _ (hcoord _ _ 7 rfl)

/-- The literal affine space containing the normalized two-site observations. -/
def normalizedExchangeMarginals : Set Density :=
  {ρ | ρ.IsHermitian ∧ ExchangeSymmetric ρ ∧ ρ.trace = 1}

private theorem continuous_conjTranspose_density :
    Continuous (fun ρ : Density => ρᴴ) := by
  refine continuous_pi fun p => continuous_pi fun q => ?_
  exact Complex.continuous_conj.comp ((continuous_apply p).comp (continuous_apply q))

private theorem continuous_trace_density : Continuous (fun ρ : Density => ρ.trace) := by
  unfold Matrix.trace
  exact continuous_finsetSum _ fun p _ => (continuous_apply p).comp (continuous_apply p)

theorem isClosed_normalizedExchangeMarginals : IsClosed normalizedExchangeMarginals := by
  have hHermitian : IsClosed {ρ : Density | ρ.IsHermitian} :=
    isClosed_eq continuous_conjTranspose_density continuous_id
  have hSwap : IsClosed {ρ : Density | ExchangeSymmetric ρ} := by
    rw [show {ρ : Density | ExchangeSymmetric ρ} =
      ⋂ p : Fin 2 × Fin 2, ⋂ q : Fin 2 × Fin 2, {ρ : Density |
        ρ p.swap q.swap = ρ p q} by ext ρ; simp [ExchangeSymmetric]]
    refine isClosed_iInter fun p => isClosed_iInter fun q => isClosed_eq ?_ ?_
    · exact (continuous_apply q.swap).comp (continuous_apply p.swap)
    · exact (continuous_apply q).comp (continuous_apply p)
  have hTrace : IsClosed {ρ : Density | ρ.trace = 1} :=
    isClosed_eq continuous_trace_density continuous_const
  exact hHermitian.inter (hSwap.inter hTrace)

private theorem isHermitian_pairGram {m : ℕ} (ψ : Amplitudes m) :
    (pairGram ψ).IsHermitian := by
  change (pairGram ψ)ᴴ = _
  ext p q
  simp [Matrix.conjTranspose_apply, pairGram, mul_comm]

theorem normalizedMarginal_mem {m : ℕ} (A : Fin 2 → PeriodicMPSParentIntersection.Bond)
    (hA : UniformMPSExpectedDimensionRefutation.traceWord 2 2 (2 + m) A ≠ 0) :
    normalizedMarginal m A ∈ normalizedExchangeMarginals := by
  let ψ := UniformMPSExpectedDimensionRefutation.traceWord 2 2 (2 + m) A
  have hψ : (pairGram ψ).IsHermitian := isHermitian_pairGram ψ
  have ht : ((pairGram ψ).trace.re : ℂ) = (pairGram ψ).trace := by
    simpa only [Matrix.one_mul] using trace_is_real (Matrix.isHermitian_one (n := Fin 2 × Fin 2)
      (α := ℂ)) hψ
  refine ⟨?_, normalizedMarginal_exchangeSymmetric A m, ?_⟩
  · change (((pairGram ψ).trace.re)⁻¹ • pairGram ψ)ᴴ =
      ((pairGram ψ).trace.re)⁻¹ • pairGram ψ
    simp [Matrix.conjTranspose_smul, hψ.eq]
  · change (((pairGram ψ).trace.re)⁻¹ • pairGram ψ).trace = 1
    have hne : (pairGram ψ).trace.re ≠ 0 := by
      rw [← mass_eq_trace]
      exact (mass_pos ψ hA).ne'
    rw [Matrix.trace_smul, Complex.real_smul, ← ht, Complex.ofReal_re, Complex.ofReal_inv,
      inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hne)]

/-- All three equations survive on the full compact source, including its border. -/
theorem twoSiteObservation_mem_of_mem_closure {m : ℕ} {p : StateMatrix m}
    (hp : p ∈ closure (actualProjectors m)) :
    twoSiteObservation m p ∈ normalizedExchangeMarginals := by
  apply closure_minimal _ (isClosed_normalizedExchangeMarginals.preimage
    (continuous_twoSiteObservation m)) hp
  rintro _ ⟨A, hA, rfl⟩
  change twoSiteObservation m _ ∈ normalizedExchangeMarginals
  rw [twoSiteObservation_traceWord]
  exact normalizedMarginal_mem A hA

theorem readout_injOn_normalized : InjOn readout normalizedExchangeMarginals := by
  intro ρ hρ σ hσ h
  exact eq_of_readout_of_trace_eq hρ.1 hσ.1 hρ.2.1 hσ.2.1
    (congrArg Complex.re (hρ.2.2.trans hσ.2.2.symm)) h

/-- The nine real readings and the literal marginal induce exactly the same
fibers on the compact closure of actual projectors. -/
theorem readout_eq_iff {m : ℕ} (x y : closure (actualProjectors m)) :
    readout (twoSiteObservation m y.val) = readout (twoSiteObservation m x.val) ↔
      twoSiteObservation m y.val = twoSiteObservation m x.val :=
  ⟨readout_injOn_normalized (twoSiteObservation_mem_of_mem_closure y.property)
    (twoSiteObservation_mem_of_mem_closure x.property), congrArg readout⟩

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSCompactReadout
