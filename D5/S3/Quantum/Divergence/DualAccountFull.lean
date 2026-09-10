/- GID: D5/S3/Quantum/Divergence/DualAccountFull
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/DualAccountFull
   mirror-E: none(waiver:general-operator-identity)
   anchors: []
   utility: none
   digest: A state fixed by one unbiased pinching pays its full entropy deficit in the other. -/

import D5.S3.Quantum.Divergence.GibbsVariationalIdentity
import D5.S3.Quantum.Tomography.MutuallyUnbiasedDiagonalPlanes
import D5.S3.Quantum.Sharpness.FreeNegentropyBudget
import D5.S3.Entropy.EntropyNonneg

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Divergence.DualAccountFull

open scoped ComplexOrder CStarAlgebra MatrixOrder
open D5.S3.Observer.Conditioning
open D5.S3.Quantum.Tomography.RankOneContextCommutator
open D5.S3.Quantum.Tomography.MutuallyUnbiasedDiagonalPlanes
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Quantum.Divergence.GibbsVariationalIdentity
open D5.S3.Quantum.Sharpness.FreeNegentropyBudget
open D5.S3.Entropy.MaxEntropy
open D5.S3.Entropy.EntropyNonneg

private theorem conjugate_pinching_eq_uniform
    {d : ℕ} [NeZero d] (Z X : RankOneContext d)
    (hZ : IsRecordMeasurement Z.projector)
    (hX : IsRecordMeasurement X.projector)
    (hZX : ∀ j k, overlap Z X j k = (d : ℝ)⁻¹)
    (rho : DensityState (Fin d))
    (hFixed : unreadState Z.projector rho.1 = rho.1) :
    unreadState X.projector rho.1 =
      (gibbsState (0 : CStarMatrix (Fin d) (Fin d) ℂ) (IsSelfAdjoint.zero _)).1 := by
  by_cases hd : 2 ≤ d
  · have hp : (CStarMatrix.ofMatrix.symm rho.1).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp
        (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm rho.2.1)
    have h := ((mutually_unbiased_diagonal_planes hd Z X hZ hX).2.2.2.mpr hZX
      (CStarMatrix.ofMatrix.symm rho.1) hp.isHermitian).2
    rw [hFixed, rho.2.2] at h
    rw [h, gibbs_state_zero]
    simp [Complex.real_smul]
  · have hdOne : d = 1 := by have := NeZero.ne d; omega
    subst d
    have hr : rho.1 = (1 : CStarMatrix (Fin 1) (Fin 1) ℂ) := by
      ext i j
      fin_cases i
      fin_cases j
      simpa [Matrix.trace, Matrix.diag] using rho.2.2
    rw [hr, gibbs_state_zero]
    simp only [Fintype.card_fin, Nat.cast_one, inv_one, one_smul]
    change unreadState X.projector (1 : Matrix (Fin 1) (Fin 1) ℂ) = 1
    simp only [unreadState, Matrix.mul_one, hX.idempotent]
    exact X.resolvesIdentity

/-- For a density state unchanged by Z pinching, the actual X pinching output is the
maximally mixed state. Its relative-entropy tax equals the full freedom relative to that
state, the entropy deficit, and the entropy gained in X pinching. Being fixed by X as well
is equivalent to being maximally mixed. Z and X are arbitrary mutually unbiased contexts. -/
theorem dual_account_full
    {d : ℕ} [NeZero d] (Z X : RankOneContext d)
    (hZ : IsRecordMeasurement Z.projector)
    (hX : IsRecordMeasurement X.projector)
    (hZX : ∀ j k, overlap Z X j k = (d : ℝ)⁻¹)
    (rho sigma : DensityState (Fin d))
    (hFixed : unreadState Z.projector rho.1 = rho.1)
    (hPinch : unreadState X.projector rho.1 = sigma.1) :
    let omega := gibbsState (0 : CStarMatrix (Fin d) (Fin d) ℂ)
      (IsSelfAdjoint.zero _)
    sigma = omega ∧
      quantumRelativeEntropy rho sigma = quantumRelativeEntropy rho omega ∧
      quantumRelativeEntropy rho sigma = Real.log d - vonNeumannEntropy rho ∧
      vonNeumannEntropy sigma - vonNeumannEntropy rho =
        quantumRelativeEntropy rho sigma ∧
      (unreadState X.projector rho.1 = rho.1 ↔ rho = omega) := by
  dsimp only
  let omega := gibbsState (0 : CStarMatrix (Fin d) (Fin d) ℂ) (IsSelfAdjoint.zero _)
  have hOut : unreadState X.projector rho.1 = omega.1 :=
    conjugate_pinching_eq_uniform Z X hZ hX hZX rho hFixed
  have hSigma : sigma = omega := Subtype.ext (hPinch.symm.trans hOut)
  have hAccount : vonNeumannEntropy rho + quantumRelativeEntropy rho omega = Real.log d := by
    simpa only [Fintype.card_fin] using entropy_uniform_identity rho
  have hSelf : quantumRelativeEntropy omega omega = 0 := by
    simp [quantumRelativeEntropy]
  have hEntropy : vonNeumannEntropy omega = Real.log d := by
    simpa only [Fintype.card_fin, hSelf, add_zero] using entropy_uniform_identity omega
  refine ⟨hSigma, congrArg (quantumRelativeEntropy rho) hSigma, ?_, ?_, ?_⟩
  · rw [hSigma]
    linarith
  · rw [hSigma, hEntropy]
    linarith
  · rw [hOut]
    constructor
    · intro h
      exact Subtype.ext h.symm
    · intro h
      exact congrArg Subtype.val h.symm

/-- Every finite density state lies on the closed entropy/freedom segment in nats.
Freedom is the existing relative entropy to the zero-Hamiltonian Gibbs state. -/
theorem entropy_freedom_segment
    {d : ℕ} [NeZero d] (rho : DensityState (Fin d)) :
    let omega := gibbsState (0 : CStarMatrix (Fin d) (Fin d) ℂ)
      (IsSelfAdjoint.zero _)
    0 ≤ vonNeumannEntropy rho ∧
      0 ≤ quantumRelativeEntropy rho omega ∧
      vonNeumannEntropy rho + quantumRelativeEntropy rho omega = Real.log d := by
  dsimp only
  have hSpectrum := (free_negentropy_budget rho).1
  have hEntropy := von_neumann_entropy_eq_shannon_state_spectrum rho
  have hNonneg : 0 ≤ vonNeumannEntropy rho := by
    rw [hEntropy]
    exact shannon_entropy_nonneg _ hSpectrum
  have hUpper : vonNeumannEntropy rho ≤ Real.log d := by
    rw [hEntropy]
    simpa only [Fintype.card_fin] using entropy_le_log_card _ hSpectrum
  have hAccount := entropy_uniform_identity rho
  simp only [Fintype.card_fin] at hAccount
  exact ⟨hNonneg, by linarith, hAccount⟩

#print axioms dual_account_full
#print axioms entropy_freedom_segment

end D5.S3.Quantum.Divergence.DualAccountFull
